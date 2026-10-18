# -*- coding: UTF-8 -*-
"""
Zepp Life(原小米运动)微信步数自动化 · 分时段累加模式
====================================================

功能说明
--------
每天从早上 6 点(北京时间)开始自动提交步数:
  - 第 1 次提交一个 1000~2000 的随机步数
  - 之后每次提交 = 上一次累计值 + random(1000, 2000),步数逐次累加
  - 两次提交之间随机间隔 1~2 小时(次数多时会自动压缩间隔以保证当天完成)
  - 每天执行次数:工作日(周一至周五)14 次,休息日(周六日/法定节假日)10 次
    工作日最终约 14000~28000 步,休息日约 10000~20000 步,模拟真实用户步数增长

实现方式
--------
GitHub Actions 单个 Job 最长只能运行 6 小时,无法在一次运行里完成全天
跨度 10~20 小时的提交,因此采用「定时唤醒 + 状态文件」方案:
  1. Workflow 每 20 分钟触发一次 main.py(见 .github/workflows/main.yml)
  2. 脚本读取仓库中的 state.json,判断当前是否到达某次提交的"预约时间"
  3. 到点则登录 Zepp,提交一次"累计总步数"
  4. 把新状态(累计步数 / 已提交次数 / 下次提交时间)写回 state.json
  5. Workflow 自动把 state.json commit & push 回仓库,供下次唤醒时读取
  6. 跨天后状态自动重置,重新从 6 点开始,如此往复
每天次数按「工作日/休息日」自动区分:优先调用免费节假日接口识别法定节假日
与调休补班(可关闭),接口失败时回退为「周一至周五=工作日、周六日=休息日」。
"""

import requests
import re
import random
import socket
import struct
import time
import os
import json
import hashlib
import urllib.parse
from datetime import datetime, timedelta, timezone

# ====================== 全局默认配置(可按需修改) ======================

DEFAULT_START_HOUR = 6        # 每天开始提交的小时(北京时间,24 小时制)
DEFAULT_WEEKDAY_RUNS = 14     # 工作日(周一至周五)每天提交次数
DEFAULT_WEEKEND_RUNS = 10     # 休息日(周六日/法定节假日)每天提交次数
DEFAULT_STEP_MIN = 1000       # 每次累加的步数下限(闭区间)
DEFAULT_STEP_MAX = 2000       # 每次累加的步数上限(闭区间)
DEFAULT_INTERVAL_MIN = 60     # 两次提交之间的最小间隔(分钟)
DEFAULT_INTERVAL_MAX = 120    # 两次提交之间的最大间隔(分钟)

# 说明:工作日 14 次无法在 6:00-23:40 内全部用满 1~2 小时间隔
# (13 个间隔 x 平均 90 分钟 ≈ 19.5 小时),脚本会按「剩余时间/剩余次数」
# 自动压缩间隔(约 60~100 分钟),保证当天次数全部完成。

# ---- 法定节假日识别(用于区分工作日/休息日,可按需关闭) ----
USE_HOLIDAY_API = True        # True=自动识别法定节假日与调休补班;失败自动回退按星期判断
HOLIDAY_API_URL = "https://timor.tech/api/holiday/info/{date}"   # 免费接口,无需 Key
HOLIDAY_API_TIMEOUT = 5       # 接口超时(秒)
# 手动覆盖优先级最高,示例: {"2025-10-01": "rest", "2025-09-28": "work"}
HOLIDAY_OVERRIDES = {}

RETRY_INTERVAL_MINUTES = 10   # 提交失败后的重试间隔(分钟)
MAX_RETRY_PER_DAY = 5         # 单账号每日最大失败重试次数,超过则今日放弃
DAY_END_HOUR = 23             # 当天最后一个可用唤醒点(北京时间 23:40,按 20 分钟周期),
DAY_END_MINUTE = 40           # 间隔规划会预留完整槽位,确保当天次数全部完成
WAKE_TICK_MINUTES = 20        # main.yml 中 cron 的唤醒间隔(分钟),间隔规划会对齐到该周期

STATE_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "state.json")

BJ_TZ = timezone(timedelta(hours=8))   # 北京时间(UTC+8,无夏令时)


# ====================== 登录与提交(Zepp/华米接口,保持原有逻辑) ======================

def login(account, password):
    PHONE_PATTERN = r"(^(1)\d{10}$)"
    if re.match(PHONE_PATTERN, account):
        account = f"+86{account}"
        third_name = "huami_phone"
    else:
        third_name = "email"   # 邮箱账号用 email 类型(原 "huami" 会导致 0106)

    headers = {
        "content-type": "application/x-www-form-urlencoded; charset=UTF-8",
        "user-agent": "MiFit/6.12.0 (MCE16; Android 16; Density/1.5)",
        "app_name": "com.xiaomi.hm.health",
    }
    url1 = "https://api-user.huami.com/registrations/" + account + "/tokens"
    data1 = f"client_id=HuaMi&country_code=CN&json_response=true&name={account}&password={password}&redirect_uri=https://s3-us-west-2.amazonaws.com/hm-registration/successsignin.html&state=REDIRECTION&token=access"
    res1 = requests.post(url1, data=data1, headers=headers)

    if res1.status_code == 200:
        r1sc = res1.status_code
        res1 = res1.json()
        if "access" in res1:
            print(f"信息:登录成功,Access Code={r1sc}")
            code = res1["access"]
        else:
            print(f"错误:用户名或密码不正确,Access Code={r1sc}")
            return None, None
    elif res1.status_code == 429:
        print(f"错误:请求过于频繁,请稍后再试,Access Code={res1.status_code}")
        return None, None
    else:
        print(f"错误:登录失败,Access Code={res1.status_code}")
        return None, None

    url2 = "https://account.huami.com/v2/client/login"
    data2 = f"app_name=com.xiaomi.hm.health&country_code=CN&code={code}&device_id=00:00:00:00:00:00&device_model=android_phone&app_version=6.12.0&grant_type=access_token&allow_registration=false&source=com.xiaomi.hm.health&third_name={third_name}"
    res2 = requests.post(url2, data=data2, headers=headers)

    res2_body = res2.text
    if res2.status_code == 200:
        r2sc = res2.status_code
        try:
            res2 = res2.json()
            login_token = res2["token_info"]["login_token"]
            user_id = res2["token_info"]["user_id"]
            print(f"信息:登录成功,Login Code={r2sc},User ID={user_id}")
            return login_token, user_id
        except Exception:
            print(f"错误:第二步登录响应中无 token_info,HTTP {r2sc},响应内容(前600字):{res2_body[:600]}")
            return None, None
    else:
        print(f"错误:登录失败,Login Code={res2.status_code},响应内容(前600字):{res2_body[:600]}")
        return None, None

def get_app_token(login_token):
    headers = {
        "content-type": "application/x-www-form-urlencoded; charset=UTF-8",
        "user-agent": "MiFit/6.12.0 (MCE16; Android 16; Density/1.5)",
        "app_name": "com.xiaomi.hm.health",
    }
    url = f"https://account-cn.huami.com/v1/client/app_tokens?login_token={login_token}"
    res = requests.get(url, headers=headers)

    if res.status_code == 200:
        res_data = res.json()
        if "token_info" in res_data:
            print(f"信息:成功获取到 app_token ,Code={res.status_code}")
            return res_data["token_info"]["app_token"]
        else:
            print(f"错误:无法解析出有效的 app_token ,Code={res.status_code}")
            return None
    else:
        print(f"错误:无法获取到有效的 app_token ,Code={res.status_code}")
        return None

def change_steps(account, user_id, app_token, steps):
    # 修改步数
    sec_timestamp = get_sec_timestamp()
    if sec_timestamp is None:
        sec_timestamp = int(time.time())
        print(f"警告:NTP 时间获取失败,使用系统时间{sec_timestamp}")

    # 使用北京日期。GitHub 服务器是 UTC,若沿用 time.strftime("%F"),
    # 在北京时间 0~8 点提交时会拿到"昨天"的日期,导致步数记到前一天
    dateToday = datetime.now(BJ_TZ).strftime("%F")
    deviceID = "0000000000000000"

    dataJSON = "%5b%7b%22data_hr%22%3a%22" + "%5c%2fv7%2b"*480 + f"%22%2c%22date%22%3a%22{dateToday}%22%2c%22data%22%3a%5b%7b%22start%22%3a0%2c%22stop%22%3a1439%2c%22value%22%3a%22" + "A"*5760 + f"%22%2c%22tz%22%3a32%2c%22did%22%3a%22{deviceID}%22%2c%22src%22%3a24%7d%5d%2c%22summary%22%3a%22%7b%5c%22v%5c%22%3a6%2c%5c%22slp%5c%22%3a%7b%5c%22st%5c%22%3a0%2c%5c%22ed%5c%22%3a0%2c%5c%22dp%5c%22%3a0%2c%5c%22lt%5c%22%3a0%2c%5c%22wk%5c%22%3a0%2c%5c%22usrSt%5c%22%3a-1440%2c%5c%22usrEd%5c%22%3a-1440%2c%5c%22wc%5c%22%3a0%2c%5c%22is%5c%22%3a0%2c%5c%22lb%5c%22%3a0%2c%5c%22to%5c%22%3a0%2c%5c%22dt%5c%22%3a0%2c%5c%22rhr%5c%22%3a0%2c%5c%22ss%5c%22%3a0%7d%2c%5c%22stp%5c%22%3a%7b%5c%22ttl%5c%22%3a{steps}%2c%5c%22dis%5c%22%3a0%2c%5c%22cal%5c%22%3a0%2c%5c%22wk%5c%22%3a0%2c%5c%22rn%5c%22%3a0%2c%5c%22runDist%5c%22%3a0%2c%5c%22runCal%5c%22%3a0%2c%5c%22stage%5c%22%3a%5b%5d%7d%2c%5c%22goal%5c%22%3a0%2c%5c%22tz%5c%22%3a%5c%2228800%5c%22%7d%22%2c%22source%22%3a24%2c%22type%22%3a0%7d%5d"

    headers0 = {
        "content-type": "application/x-www-form-urlencoded; charset=UTF-8",
        "user-agent": "MiFit/6.12.0 (MCE16; Android 16; Density/1.5)",
        "app_name": "com.xiaomi.hm.health",
        "apptoken": app_token,
    }
    url0 = f"https://api-mifit-cn.huami.com/v1/data/band_data.json?&t={sec_timestamp}"
    data0 = f"userid={user_id}&last_sync_data_time={sec_timestamp}&device_type=0&last_deviceid={deviceID}&data_json={dataJSON}"

    try:
        res0 = requests.post(url0, data=data0, headers=headers0)
        res0_data = res0.json()
        print(f"信息:账号:{account};步数={steps};返回结果={res0_data}")
        if res0_data.get('message') == 'success':
            return True
        else:
            return False
    except Exception as e:
        print(f"错误:提交步数失败:{e}")
        return False

def get_sec_timestamp():
    # 通过 NTP 服务器获取秒级时间戳
    client = None
    try:
        NTP_SERVER = 'ntp.ntsc.ac.cn'
        PORT = 123
        NTP_FORMAT = '!12I'
        NTP_DELTA = 2208988800

        client = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        client.settimeout(5)

        data = bytearray(48)
        data[0] = 0x1B

        client.sendto(data, (NTP_SERVER, PORT))
        data, address = client.recvfrom(1024)

        if data:
            unpacked = struct.unpack(NTP_FORMAT, data[:48])
            timestamp = unpacked[10] - NTP_DELTA
            print(f"信息:成功通过 NTP 服务器获取到秒级时间戳,SecTimeStamp={timestamp}")
            return int(timestamp)

        return None

    except socket.timeout:
        print("错误:连接 NTP 服务器超时")
        return None
    except socket.gaierror:
        print("错误:无法解析 NTP 服务器地址")
        return None
    except Exception as e:
        print(f"错误:获取时间戳失败 - {e}")
        return None
    finally:
        try:
            if client is not None:
                client.close()
        except:
            pass


def URL_encode_dataJSON(dateToday, deviceID, steps):
    JSON_Frame = f'[{{"date":"{dateToday}","data":[{{"start":0,"stop":1439,"did":"{deviceID}","src":24}}],"summary":"{{\\"stp\\":{{\\"ttl\\":{steps}}}}}","source":24,"type":0}}]'
    Encoded_dataJSON = urllib.parse.quote(JSON_Frame, safe='')
    return Encoded_dataJSON


# ====================== 分时段累加调度(核心新增逻辑) ======================

def account_key(account):
    # 把账号转成 md5 指纹作为状态键,避免在 state.json 中暴露明文账号
    return hashlib.md5(str(account).encode("utf-8")).hexdigest()[:16]


def mask_account(account):
    s = str(account)
    if "@" in s:
        name, _, domain = s.partition("@")
        return f"{name[:2]}***@{domain}"
    if s.isdigit() and len(s) == 11:
        return f"{s[:3]}****{s[-4:]}"
    return s[:2] + "***"


def normalize_cfg(c):
    """把 AccountGroup 中每个账号的第三个配置元素统一成 dict 配置"""
    cfg = {
        "mode": "cumulative",        # cumulative=分时段累加(新默认) / oneshot=每日一次随机总数(旧模式)
        "start_hour": DEFAULT_START_HOUR,
        "runs_per_day": None,        # 显式指定则每天都用固定次数;None=按工作日/休息日自动区分
        "weekday_runs": DEFAULT_WEEKDAY_RUNS,    # 工作日(周一至周五)次数
        "weekend_runs": DEFAULT_WEEKEND_RUNS,    # 休息日(周六日/法定节假日)次数
        "step_min": DEFAULT_STEP_MIN,
        "step_max": DEFAULT_STEP_MAX,
        "interval_min": DEFAULT_INTERVAL_MIN,
        "interval_max": DEFAULT_INTERVAL_MAX,
    }
    if c is None:
        return cfg
    if isinstance(c, dict):
        cfg.update(c)
        return cfg
    # 旧模式:列表 [min, max] 或单个整数 => 每天开始时间后一次性提交随机总步数
    if isinstance(c, (list, tuple)) and len(c) == 2:
        return {"mode": "oneshot", "start_hour": DEFAULT_START_HOUR, "step_min": int(c[0]), "step_max": int(c[1])}
    v = int(c)
    return {"mode": "oneshot", "start_hour": DEFAULT_START_HOUR, "step_min": v, "step_max": v}


def load_state():
    try:
        with open(STATE_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, dict) and "accounts" in data:
            return data
    except (FileNotFoundError, json.JSONDecodeError):
        pass
    except Exception as e:
        print(f"警告:读取状态文件失败({e}),将重建状态")
    return {"version": 1, "accounts": {}}


def save_state(state):
    tmp = STATE_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(state, f, ensure_ascii=False, indent=2)
    os.replace(tmp, STATE_FILE)


def submit_steps(account, password, steps):
    """登录并提交一次步数;成功返回 True"""
    login_token, userid = login(account, password)
    if not login_token:
        print(f"错误:账号:{account},登录失败")
        return False
    app_token = get_app_token(login_token)
    if not app_token:
        print(f"错误:账号:{account},获取 app_token 失败")
        return False
    return change_steps(account, userid, app_token, str(steps))


def query_holiday_api(date_str):
    """查询中国法定节假日/调休。返回 True=休息日,False=工作日,None=查询失败"""
    try:
        url = HOLIDAY_API_URL.format(date=date_str)
        res = requests.get(url, timeout=HOLIDAY_API_TIMEOUT)
        if res.status_code != 200:
            print(f"警告:节假日接口返回 HTTP {res.status_code},回退为按星期判断")
            return None
        data = res.json()
        ttype = (data.get("type") or {}).get("type")
        # 接口 type 字段: 0=工作日 1=周末 2=法定节假日 3=调休补班
        mapping = {0: False, 1: True, 2: True, 3: False}
        if ttype in mapping:
            name = (data.get("type") or {}).get("name", "")
            print(f"信息:节假日接口判定 {date_str} 为{'休息日' if mapping[ttype] else '工作日'}({name})")
            return mapping[ttype]
        print("警告:节假日接口返回格式异常,回退为按星期判断")
        return None
    except Exception as e:
        print(f"警告:节假日接口查询失败({e}),回退为按星期判断")
        return None


def is_rest_day(date_str, state):
    """判断某天是否休息日(决定当日提交次数)。
    优先级:手动覆盖 > 法定节假日接口(可选) > 周一至周五=工作日,周六日=休息日"""
    if date_str in HOLIDAY_OVERRIDES:
        return str(HOLIDAY_OVERRIDES[date_str]).lower() in ("rest", "休息", "holiday", "rest_day")

    cache = state.setdefault("workday_cache", {})
    if date_str in cache:
        return bool(cache[date_str].get("rest"))

    rest = query_holiday_api(date_str) if USE_HOLIDAY_API else None
    source = "节假日接口"
    if rest is None:
        d = datetime.strptime(date_str, "%Y-%m-%d")
        rest = d.weekday() >= 5   # 5=周六,6=周日
        source = "按星期回退"
    cache[date_str] = {"rest": bool(rest), "source": source}
    print(f"信息:{date_str} 按{source}判定为{'休息日' if rest else '工作日'}")
    return bool(rest)


def get_runs_for_date(cfg, date_str, state):
    """获取某天应执行的提交次数:工作日 14 次 / 休息日 10 次(可按账号配置覆盖)"""
    if cfg.get("runs_per_day") is not None:
        return int(cfg["runs_per_day"])   # 显式指定固定次数时,不再区分工作日/休息日
    if is_rest_day(date_str, state):
        return int(cfg["weekend_runs"])
    return int(cfg["weekday_runs"])


def plan_next_wait_minutes(now, remaining_runs, cfg):
    """生成两次提交之间的随机等待分钟数(1~2 小时,对齐唤醒周期);
    若剩余次数在当天排不完(如工作日 14 次),则按「最后一个可用唤醒点 -
    剩余次数 x 唤醒周期」自动压缩间隔,保证剩余每一次都有可用槽位"""
    base = random.randint(cfg["interval_min"], cfg["interval_max"])
    wait = max(1, -(-base // WAKE_TICK_MINUTES)) * WAKE_TICK_MINUTES   # 对齐到唤醒周期整数倍
    # 当天最后一个可用唤醒点之前,必须给剩余每一次都留出槽位
    day_end = now.replace(hour=DAY_END_HOUR, minute=DAY_END_MINUTE, second=0, microsecond=0)
    latest_next = day_end - (remaining_runs - 1) * timedelta(minutes=WAKE_TICK_MINUTES)
    max_wait = (latest_next - now).total_seconds() / 60
    if max_wait < wait:
        wait = max(WAKE_TICK_MINUTES, int(max_wait // WAKE_TICK_MINUTES) * WAKE_TICK_MINUTES)
    return int(wait)


def process_account(account, password, cfg, state, now):
    """处理单个账号的一次唤醒:判断是否到点,到点则提交并更新状态"""
    key = account_key(account)
    entries = state.setdefault("accounts", {})
    today = now.strftime("%F")
    entry = entries.get(key)

    # 新账号或跨天:重置当日状态
    if entry is None or entry.get("date") != today:
        entry = {
            "date": today,
            "run_count": 0,       # 今日已提交次数
            "total_steps": 0,     # 今日当前累计步数
            "next_run_ts": 0,     # 下次提交预约时间(Unix 秒级时间戳)
            "fail_count": 0,      # 今日连续失败次数
            "done": False,        # 今日是否已全部完成
        }
        entries[key] = entry

    now_ts = now.timestamp()
    tag = mask_account(account)

    # 今日任务已完成
    if entry.get("done"):
        print(f"信息:账号:{tag},今日任务已完成(共{entry['run_count']}次,累计{entry['total_steps']}步),本次跳过")
        return

    # ---------- 旧模式:每天 start_hour 点后一次性提交随机总步数 ----------
    if cfg["mode"] == "oneshot":
        if now.hour < cfg["start_hour"]:
            print(f"信息:账号:{tag},未到每日开始时间({cfg['start_hour']}点),本次跳过")
            return
        if entry.get("next_run_ts") and now_ts < entry["next_run_ts"]:
            return   # 上次失败后,处于静默重试等待期
        step = random.randint(cfg["step_min"], cfg["step_max"])
        print(f"信息:账号:{tag},一次性模式,本次提交总步数:{step}")
        if submit_steps(account, password, step):
            entry.update({"run_count": 1, "total_steps": step, "done": True, "fail_count": 0, "next_run_ts": 0})
            print(f"信息:账号:{tag},今日步数修改成功:{step}")
        else:
            entry["fail_count"] = entry.get("fail_count", 0) + 1
            if entry["fail_count"] >= MAX_RETRY_PER_DAY:
                entry["done"] = True
                print(f"错误:账号:{tag},连续失败{entry['fail_count']}次,今日放弃")
            else:
                entry["next_run_ts"] = now_ts + RETRY_INTERVAL_MINUTES * 60
                print(f"错误:账号:{tag},提交失败,{RETRY_INTERVAL_MINUTES}分钟后重试(第{entry['fail_count']}/{MAX_RETRY_PER_DAY}次)")
        return

    # ---------- 累加模式:每天 start_hour 点起,每 1~2 小时随机累加一次 ----------
    if now.hour < cfg["start_hour"]:
        print(f"信息:账号:{tag},未到每日开始时间({cfg['start_hour']}点),本次跳过")
        return

    # 今日目标次数:工作日 14 次 / 休息日 10 次(可被账号配置 runs_per_day 覆盖)
    today_runs = get_runs_for_date(cfg, today, state)

    if entry["run_count"] >= today_runs:
        entry["done"] = True
        print(f"信息:账号:{tag},今日{today_runs}次提交已全部完成,累计{entry['total_steps']}步")
        return

    next_ts = entry.get("next_run_ts") or 0
    if next_ts and now_ts < next_ts:
        nxt = datetime.fromtimestamp(next_ts, BJ_TZ)
        print(f"信息:账号:{tag},下次提交预约时间为 {nxt:%H:%M},本次跳过")
        return

    # 到点:本次步数 = 当前累计 + random(1000, 2000)
    delta = random.randint(cfg["step_min"], cfg["step_max"])
    new_total = entry["total_steps"] + delta
    which = entry["run_count"] + 1
    print(f"信息:账号:{tag},今日第 {which}/{today_runs} 次提交,本次累加 {delta} 步,总步数 {entry['total_steps']} -> {new_total}")

    if submit_steps(account, password, new_total):
        entry["run_count"] = which
        entry["total_steps"] = new_total
        entry["fail_count"] = 0
        if entry["run_count"] >= today_runs:
            entry["done"] = True
            entry["next_run_ts"] = 0
            print(f"信息:账号:{tag},今日任务全部完成!共 {entry['run_count']} 次,累计 {new_total} 步")
        else:
            wait = plan_next_wait_minutes(now, today_runs - entry["run_count"], cfg)
            entry["next_run_ts"] = now_ts + wait * 60
            nxt = datetime.fromtimestamp(entry["next_run_ts"], BJ_TZ)
            print(f"信息:账号:{tag},下次提交预约:{nxt:%H:%M}(随机间隔约 {wait} 分钟)")
    else:
        entry["fail_count"] = entry.get("fail_count", 0) + 1
        if entry["fail_count"] >= MAX_RETRY_PER_DAY:
            entry["done"] = True
            print(f"错误:账号:{tag},连续失败 {entry['fail_count']} 次,今日放弃")
        else:
            entry["next_run_ts"] = now_ts + RETRY_INTERVAL_MINUTES * 60
            print(f"错误:账号:{tag},本次提交失败,{RETRY_INTERVAL_MINUTES} 分钟后自动重试(第 {entry['fail_count']}/{MAX_RETRY_PER_DAY} 次)")


def run_tick(now=None):
    """一次唤醒:遍历所有账号,按状态决定是否提交;状态有变化则写回 state.json"""
    now = now or datetime.now(BJ_TZ)
    print(f"===== 唤醒时间(北京时间):{now:%Y-%m-%d %H:%M:%S} =====")

    if not AccountGroup:
        print("错误:未配置任何账号")
        return

    state = load_state()

    # 清理已经不在账号组里的历史状态
    keep_keys = {account_key(acc) for acc, _, _ in AccountGroup}
    accounts_state = state.setdefault("accounts", {})
    for stale in [k for k in accounts_state if k not in keep_keys]:
        del accounts_state[stale]

    # 只保留当天的节假日判定缓存
    today_str = now.strftime("%F")
    wc = state.get("workday_cache")
    if isinstance(wc, dict):
        for k in [k for k in wc if k != today_str]:
            del wc[k]

    snapshot = json.dumps(state, sort_keys=True, ensure_ascii=False)

    for account, password, cfg in AccountGroup:
        if not account or not password:
            print("错误:存在未配置的账号或密码(请检查环境变量 ACCOUNT / PASSWORD),已跳过")
            continue
        process_account(account, password, normalize_cfg(cfg), state, now)

    if json.dumps(state, sort_keys=True, ensure_ascii=False) != snapshot:
        save_state(state)
        print("信息:任务状态已写回 state.json(稍后由 Workflow 自动提交回仓库)")
    else:
        print("信息:本次唤醒无状态变化")
    print("=" * 60)


# ====================== 账号配置 ======================

def build_account_group():
    """从环境变量读取默认账号,并组装账号配置组"""
    ACCOUNT = os.environ.get("ACCOUNT", "")
    PASSWORD = os.environ.get("PASSWORD", "")
    return [
        # 每行格式: [账号, 密码, 步数配置]
        # 第三个元素(步数配置)的取值:
        #   None            -> 全局默认(分时段累加):每天 6 点开始,每 1~2 小时随机累加
        #                      1000~2000 步;工作日(周一至周五)14 次,休息日 10 次
        #   dict            -> 自定义累加参数,可选字段:
        #                      start_hour(开始小时) / weekday_runs(工作日次数) /
        #                      weekend_runs(休息日次数) / runs_per_day(每天固定次数,优先级最高) /
        #                      step_min, step_max(每次累加范围) /
        #                      interval_min, interval_max(间隔分钟范围)
        #                      如 {"weekday_runs": 12, "weekend_runs": 8}
        #   [min, max] / 整数 -> 旧模式:每天 6 点后一次性提交随机总步数(如 [8000, 10000])
        [ACCOUNT, PASSWORD, None],
        # ['账号2', '密码2', None],
        # ['账号3', '密码3', {"weekday_runs": 12, "weekend_runs": 8, "step_min": 800, "step_max": 1600}],
        # ['账号4', '密码4', [8000, 10000]],
    ]


AccountGroup = []

if __name__ == "__main__":
    AccountGroup = build_account_group()
    run_tick()
