"""
Emby 存量字幕补齐插件

扫描 Emby 媒体库中的电影和剧集，找出缺少中文字幕的外语内容，
调用 MoviePilot 核心字幕搜索（与 AutoSubtitle 插件相同的字幕来源）
下载中文字幕并存放到视频文件旁边。

与 AutoSubtitle 的区别：
- AutoSubtitle：文件整理入库完成后触发，只处理新入库的媒体
- 本插件：扫描 Emby 中已有的存量媒体，批量补齐缺失的中文字幕
"""
import asyncio
import json
import re
import threading
import zipfile
from datetime import datetime
from pathlib import Path
from typing import Any
from uuid import uuid4

import httpx
from apscheduler.triggers.cron import CronTrigger

from app.chain.search import SearchChain
from app.core.config import settings
from app.core.context import SubtitleInfo
from app.helper.torrent import TorrentHelper
from app.log import logger
from app.plugins import _PluginBase
from app.schemas import NotificationType
from app.utils.http import AsyncRequestUtils


class EmbySubtitleSync(_PluginBase):
    # 插件名称
    plugin_name = "Emby存量字幕补齐"
    # 插件描述
    plugin_desc = "扫描 Emby 媒体库，为缺少中文字幕的外语电影/剧集补齐中文字幕"
    # 插件图标
    plugin_icon = "subtitle.png"
    # 插件版本
    plugin_version = "2.2.0"
    # 插件作者
    plugin_author = "muse"
    # 作者主页
    author_url = ""
    # 插件配置项ID前缀
    plugin_config_prefix = "embysubtitlesync_"
    # 加载顺序
    plugin_order = 10
    # 可使用的用户级别
    auth_level = 1

    # 中文语言标记（Emby MediaStreams 中的 Language 字段常见值）
    _ZH_LANG_TAGS = {
        "chi", "zho", "zh", "zh-cn", "zh_cn", "zh-tw", "zh_tw",
        "zh-hk", "zh_hk", "zh-mo", "zh_mo", "zh-hans", "zh_hans",
        "zh-hant", "zh_hant", "zho-hans", "zho_hans", "zho-hant", "zho_hant",
        "chs", "cht", "cmn", "yue", "zhx", "chi_sim", "chi-hans", "chi_hans",
    }
    # 外挂字幕文件名中的简体标记
    _SIMP_FILE_MARKERS = {"zh-cn", "zh_cn", "chs", "简体", "简中", "简"}
    # 外挂字幕文件名中的繁体标记
    _TRAD_FILE_MARKERS = {"zh-tw", "zh_tw", "zh-hk", "zh_hk", "cht", "繁体", "繁中", "繁"}
    # 外挂字幕文件名中的通用中文标记（需结合文件内容判定简/繁）
    _GENERIC_ZH_MARKERS = {"zh", "chi", "zho", "中文", "中字"}
    # 字幕文件扩展名
    _SUBTITLE_EXTS = {".srt", ".ass", ".ssa", ".vtt", ".smi", ".sub", ".srt.txt"}
    # 用于内容检测的常见繁体字集合
    _TRAD_CHARS = set(
        "說見時會過個們來學開關頭門體國對發現後經麼樣點從當還沒給讓問聽"
        "實際報長東動裡種類華機產萬話風電業處際識達爾羅馬魚鳥龍書馬長"
        "兒義區彆後麵愛專門難擊讓體處變聲讀寫買賣進遠運"
    )

    _HISTORY_KEY = "download_history"
    _HISTORY_MAX = 100
    _PROCESSED_KEY = "processed_ids"

    def __init__(self) -> None:
        super().__init__()
        self._enabled = False
        self._emby_host = ""
        self._emby_api_key = ""
        self._library_names: list[str] = []
        self._only_foreign = True
        self._subtitle_langs: list[str] = ["简体中文"]
        self._request_delay = 2.0
        self._max_count = 200
        self._path_mappings: list[tuple[str, str]] = []
        self._cron = "0 3 * * *"
        self._run_once = False
        self._notify = False
        self._running = False
        self._dry_run = True
        self._dry_run_samples: list[str] = []

    # ------------------------------------------------------------------
    # 插件生命周期
    # ------------------------------------------------------------------

    def init_plugin(self, config: dict | None = None) -> None:
        if config:
            self._enabled = config.get("enabled", False) or False
            self._emby_host = (config.get("emby_host") or "").strip().rstrip("/")
            self._emby_api_key = (config.get("emby_api_key") or "").strip()
            _raw_libs = config.get("library_names")
            if isinstance(_raw_libs, list):
                self._library_names = [str(x).strip() for x in _raw_libs if str(x).strip()]
            elif isinstance(_raw_libs, str):
                self._library_names = [ln.strip() for ln in _raw_libs.splitlines() if ln.strip()]
            else:
                self._library_names = []
            self._only_foreign = config.get("only_foreign", True)
            if self._only_foreign is None:
                self._only_foreign = True
            self._subtitle_langs = config.get("subtitle_langs") or ["简体中文"]
            try:
                self._request_delay = float(config.get("request_delay") or 2.0)
            except (ValueError, TypeError):
                self._request_delay = 2.0
            try:
                _mc = config.get("max_count")
                self._max_count = 200 if _mc is None else int(_mc)
            except (ValueError, TypeError):
                self._max_count = 200
            self._path_mappings = []
            for line in (config.get("path_mappings") or "").splitlines():
                line = line.strip()
                if "=" in line:
                    src, dst = line.split("=", 1)
                    src, dst = src.strip(), dst.strip()
                    if src and dst:
                        self._path_mappings.append((src, dst))
            self._cron = (config.get("cron") or "0 3 * * *").strip()
            self._run_once = config.get("run_once", False) or False
            self._notify = config.get("notify", False) or False
            dry = config.get("dry_run", True)
            self._dry_run = True if dry is None else bool(dry)

            # 清空已处理记录
            if config.get("clear_processed"):
                self.save_data(self._PROCESSED_KEY, json.dumps([]))
                logger.info("[EmbySubtitleSync] 已清空已处理记录")
            # 清空下载历史
            if config.get("clear_history"):
                self.save_data(self._HISTORY_KEY, json.dumps([]))
                logger.info("[EmbySubtitleSync] 已清空下载历史")

        # 保存后立即执行一次（后台线程，避免阻塞配置保存）
        if self._run_once and self._enabled:
            self._run_once = False
            self.update_config({**self._current_config_dict(), "run_once": False, "clear_processed": False, "clear_history": False})
            thread = threading.Thread(target=self._run_once_wrapper, daemon=True, name="EmbySubtitleSync-once")
            thread.start()

    def _current_config_dict(self) -> dict:
        return {
            "enabled": self._enabled,
            "emby_host": self._emby_host,
            "emby_api_key": self._emby_api_key,
            "library_names": list(self._library_names),
            "only_foreign": self._only_foreign,
            "subtitle_langs": self._subtitle_langs,
            "request_delay": self._request_delay,
            "max_count": self._max_count,
            "path_mappings": "\n".join(f"{s}={d}" for s, d in self._path_mappings),
            "cron": self._cron,
            "notify": self._notify,
            "dry_run": self._dry_run,
        }

    def _run_once_wrapper(self) -> None:
        """后台线程入口：新建事件循环执行扫描。"""
        try:
            asyncio.run(self._sync())
        except Exception as e:
            logger.error(f"[EmbySubtitleSync] 手动执行异常: {e}")

    def get_state(self) -> bool:
        return self._enabled

    def get_service(self) -> list[dict[str, Any]]:
        """注册定时服务：按 cron 表达式周期性扫描补齐。"""
        if self.get_state() and self._emby_host and self._emby_api_key:
            try:
                trigger = CronTrigger.from_crontab(self._cron)
            except Exception as e:
                logger.error(f"[EmbySubtitleSync] cron 表达式无效: {self._cron}, {e}")
                return []
            return [
                {
                    "id": "EmbySubtitleSync",
                    "name": "Emby存量字幕补齐",
                    "trigger": trigger,
                    "func": self._service_entry,
                    "kwargs": {},
                }
            ]
        return []

    def _service_entry(self) -> None:
        """APScheduler 同步入口（插件服务 func 为同步调用）。"""
        try:
            asyncio.run(self._sync())
        except Exception as e:
            logger.error(f"[EmbySubtitleSync] 定时任务异常: {e}")

    def get_api(self) -> list[dict[str, Any]]:
        return []

    def get_form(self) -> tuple[list[dict], dict[str, Any]]:
        return self._build_form()

    def get_page(self) -> list[dict]:
        return self._build_page()

    def stop_service(self) -> None:
        pass

    # ------------------------------------------------------------------
    # Emby API 客户端
    # ------------------------------------------------------------------

    async def _emby_get(self, client: httpx.AsyncClient, path: str, params: dict | None = None) -> dict | None:
        """调用 Emby API，返回解析后的 JSON，失败返回 None。"""
        url = f"{self._emby_host}{path}"
        try:
            resp = await client.get(url, params=params, headers={"X-Emby-Token": self._emby_api_key}, timeout=30)
            if resp.status_code != 200:
                logger.warning(f"[EmbySubtitleSync] Emby 请求失败 HTTP {resp.status_code}: {path}")
                return None
            return resp.json()
        except Exception as e:
            logger.error(f"[EmbySubtitleSync] Emby 请求异常 {path}: {e}")
            return None

    async def _emby_refresh_item(self, client: httpx.AsyncClient, item_id: str) -> None:
        """字幕落盘后通知 Emby 刷新该条目，让外挂字幕立即被识别（失败不影响主流程）。"""
        try:
            await client.post(
                f"{self._emby_host}/emby/Items/{item_id}/Refresh",
                params={"Recursive": "false", "MetadataRefreshMode": "Default",
                        "ImageRefreshMode": "Default", "ReplaceAllMetadata": "false",
                        "ReplaceAllImages": "false"},
                headers={"X-Emby-Token": self._emby_api_key},
                timeout=30,
            )
        except Exception as e:
            logger.debug(f"[EmbySubtitleSync] Emby 条目刷新失败（忽略）: {e}")

    def _fetch_emby_library_names(self) -> list[str] | None:
        """同步拉取 Emby 媒体库名称（仅电影/电视剧库），供配置表单生成多选项；失败返回 None。"""
        if not self._emby_host or not getattr(self, "_emby_api_key", ""):
            return None
        try:
            with httpx.Client(timeout=5) as c:
                resp = c.get(
                    f"{self._emby_host}/emby/Library/MediaFolders",
                    headers={"X-Emby-Token": self._emby_api_key},
                )
            if resp.status_code != 200:
                return None
            names: list[str] = []
            for item in resp.json().get("Items", []):
                if (item.get("CollectionType") or "").lower() in ("movies", "tvshows"):
                    name = (item.get("Name") or "").strip()
                    if name and name not in names:
                        names.append(name)
            return names or None
        except Exception:
            return None

    async def _get_libraries(self, client: httpx.AsyncClient) -> list[dict]:
        """获取 Emby 媒体库列表，仅保留电影/电视剧类型。"""
        data = await self._emby_get(client, "/emby/Library/MediaFolders")
        if not data:
            return []
        libs = []
        for item in data.get("Items", []):
            ctype = (item.get("CollectionType") or "").lower()
            if ctype not in ("movies", "tvshows"):
                continue
            name = item.get("Name") or ""
            if self._library_names and name not in self._library_names:
                continue
            libs.append({"id": item.get("Id"), "name": name, "type": ctype})
        return libs

    async def _iter_movies(self, client: httpx.AsyncClient, library_id: str):
        """分页遍历电影库中的电影。"""
        start, limit = 0, 200
        while True:
            data = await self._emby_get(
                client,
                "/emby/Items",
                {
                    "ParentId": library_id,
                    "IncludeItemTypes": "Movie",
                    "Recursive": "true",
                    "Fields": "Path,MediaSources,ProductionYear,OriginalTitle",
                    "StartIndex": start,
                    "Limit": limit,
                    "SortBy": "SortName",
                    "SortOrder": "Ascending",
                },
            )
            if not data:
                break
            items = data.get("Items", [])
            if not items:
                break
            for item in items:
                yield item
            if start + len(items) >= (data.get("TotalRecordCount") or 0):
                break
            start += len(items)

    async def _iter_series(self, client: httpx.AsyncClient, library_id: str):
        """分页遍历剧集库中的剧集。"""
        start, limit = 0, 200
        while True:
            data = await self._emby_get(
                client,
                "/emby/Items",
                {
                    "ParentId": library_id,
                    "IncludeItemTypes": "Series",
                    "Recursive": "true",
                    "Fields": "Path,ProductionYear,OriginalTitle",
                    "StartIndex": start,
                    "Limit": limit,
                    "SortBy": "SortName",
                    "SortOrder": "Ascending",
                },
            )
            if not data:
                break
            items = data.get("Items", [])
            if not items:
                break
            for item in items:
                yield item
            if start + len(items) >= (data.get("TotalRecordCount") or 0):
                break
            start += len(items)

    async def _iter_episodes(self, client: httpx.AsyncClient, series_id: str):
        """分页遍历指定剧集的所有分集。"""
        start, limit = 0, 200
        while True:
            data = await self._emby_get(
                client,
                f"/emby/Shows/{series_id}/Episodes",
                {
                    "Fields": "Path,MediaSources,SeriesName,ParentIndexNumber,IndexNumber",
                    "StartIndex": start,
                    "Limit": limit,
                },
            )
            if not data:
                break
            items = data.get("Items", [])
            if not items:
                break
            for item in items:
                yield item
            if start + len(items) >= (data.get("TotalRecordCount") or 0):
                break
            start += len(items)

    # ------------------------------------------------------------------
    # 扫描主流程
    # ------------------------------------------------------------------

    async def _sync(self) -> None:
        """扫描主入口：遍历 Emby 媒体库，补齐缺失的中文字幕。"""
        if self._running:
            logger.info("[EmbySubtitleSync] 上一轮扫描尚未结束，跳过本次执行")
            return
        if not self._enabled or not self._emby_host or not self._emby_api_key:
            logger.warning("[EmbySubtitleSync] 插件未启用或 Emby 连接信息不完整，跳过")
            return
        self._running = True
        try:
            async with httpx.AsyncClient() as client:
                libraries = await self._get_libraries(client)
                if not libraries:
                    logger.warning("[EmbySubtitleSync] 未获取到 Emby 媒体库，请检查地址、API Key 及媒体库名称配置")
                    return
                logger.info(f"[EmbySubtitleSync] 开始扫描 {len(libraries)} 个媒体库: {[l['name'] for l in libraries]}")

                # v2: 路径映射必填校验——没配映射直接中止，避免重蹈 v1 全量误标覆辙
                if not self._path_mappings:
                    logger.error("[EmbySubtitleSync] 未配置路径映射（path_mappings），扫描中止。请在插件配置中填写，如 /movie_strm=/movie_strm")
                    return
                live_dst = 0
                for _src_p, _dst_p in self._path_mappings:
                    if Path(_dst_p).exists():
                        live_dst += 1
                    else:
                        logger.warning(f"[EmbySubtitleSync] 映射目标在本机不存在: {_dst_p}（请确认 MP 容器已挂载该目录）")
                if live_dst == 0:
                    logger.error("[EmbySubtitleSync] 所有映射目标均不存在，扫描中止。请先给 MP 容器加挂载再运行")
                    return
                if self._dry_run:
                    self._dry_run_samples = []
                    logger.info("[EmbySubtitleSync] 当前为仅扫描模式（dry-run）：只统计待补齐清单，不下载字幕")

                processed = self._load_processed()
                stats = {"checked": 0, "skipped_has_sub": 0, "skipped_foreign": 0,
                         "skipped_processed": 0, "downloaded": 0, "failed": 0,
                         "unmapped": 0, "dry_run_candidates": 0}
                stop = False

                for lib in libraries:
                    if stop:
                        break
                    if lib["type"] == "movies":
                        async for movie in self._iter_movies(client, lib["id"]):
                            if stop:
                                break
                            r = await self._process_item(client, movie, "电影", processed, stats)
                            if r == "limit":
                                stop = True
                    else:
                        async for series in self._iter_series(client, lib["id"]):
                            if stop:
                                break
                            async for ep in self._iter_episodes(client, series["Id"]):
                                if stop:
                                    break
                                r = await self._process_item(client, ep, "电视剧", processed, stats)
                                if r == "limit":
                                    stop = True
                                    break

                self._save_processed(processed)
                summary = (
                    f"扫描完成：检查 {stats['checked']} 个，已有字幕跳过 {stats['skipped_has_sub']} 个，"
                    f"非外语跳过 {stats['skipped_foreign']} 个，已处理跳过 {stats['skipped_processed']} 个，"
                    f"成功补齐 {stats['downloaded']} 个，失败 {stats['failed']} 个，"
                    f"路径不可见 {stats['unmapped']} 个"
                )
                if self._dry_run:
                    summary += f"，待补齐（dry-run）{stats['dry_run_candidates']} 个"
                    if self._dry_run_samples:
                        summary += "，样本：" + "；".join(self._dry_run_samples[:20])
                logger.info(f"[EmbySubtitleSync] {summary}")
                if self._notify:
                    self.post_message(title="Emby存量字幕补齐", text=summary, mtype=NotificationType.Plugin)
        finally:
            self._running = False

    async def _process_item(self, client: httpx.AsyncClient, item: dict, media_type: str,
                            processed: set, stats: dict) -> str | None:
        """处理单个媒体条目。返回 "limit" 表示达到本次处理上限。"""
        item_id = str(item.get("Id") or "")
        if not item_id:
            return None
        if item_id in processed:
            stats["skipped_processed"] += 1
            return None
        if stats["checked"] + stats["downloaded"] + stats["failed"] >= self._max_count and self._max_count > 0:
            return "limit"

        emby_path = item.get("Path") or ""
        local_path = self._map_path(emby_path)
        if not local_path or not Path(local_path).is_file():
            # v2 关键修复：文件在本机不可见时只计数报警，绝不标记已处理（v1 因此误标 11 万条）
            stats["unmapped"] += 1
            if stats["unmapped"] <= 5:
                logger.warning(f"[EmbySubtitleSync] 路径不可见，本轮跳过（不标记已处理）: {emby_path} -> {local_path}")
            return None

        stats["checked"] += 1
        streams = []
        try:
            sources = item.get("MediaSources") or []
            if sources:
                streams = sources[0].get("MediaStreams") or []
        except Exception:
            pass

        # 1. 检查是否已有中文字幕（内封 + 外挂）
        has_simp, has_trad = self._check_chinese_subtitle(local_path, streams)
        need_langs = []
        if "简体中文" in self._subtitle_langs and not has_simp:
            need_langs.append("简体中文")
        if "繁體中文" in self._subtitle_langs and not has_trad:
            need_langs.append("繁體中文")
        if not need_langs:
            stats["skipped_has_sub"] += 1
            processed.add(item_id)
            return None

        # 2. 外语过滤：含中文音轨的视为中文内容，跳过
        if self._only_foreign and self._has_chinese_audio(streams):
            stats["skipped_foreign"] += 1
            processed.add(item_id)
            return None

        # 2.5 dry-run：确认缺字幕且为外语内容后只登记清单，不搜索不下载不标记已处理
        title_for_log = item.get("Name") or Path(local_path).stem
        if self._dry_run:
            stats["dry_run_candidates"] += 1
            if len(self._dry_run_samples) < 20:
                yr = item.get("ProductionYear") or ""
                self._dry_run_samples.append(f"{title_for_log}({yr})[{media_type}]" if yr else f"{title_for_log}[{media_type}]")
            logger.info(f"[EmbySubtitleSync][dry-run] 待补齐: {title_for_log} 缺 {','.join(need_langs)}")
            return None

        # 3. 搜索并下载
        title = item.get("Name") or Path(local_path).stem
        keyword = self._build_keyword(item, media_type)
        logger.info(f"[EmbySubtitleSync] 缺失{','.join(need_langs)}字幕，搜索: {keyword}")
        try:
            results = await SearchChain().async_search_subtitles_by_title(title=keyword, page=0)
        except Exception as e:
            logger.error(f"[EmbySubtitleSync] 字幕搜索异常 {keyword}: {e}")
            results = None

        target = self._pick_best(results, set(need_langs), item, media_type) if results else None
        if not target:
            logger.info(f"[EmbySubtitleSync] 未找到合适字幕: {title}")
            stats["failed"] += 1
            self._add_history(title, item.get("ProductionYear") or "", media_type,
                              ",".join(need_langs), "", False)
            processed.add(item_id)
            return None

        ok, sub_name = await self._download_subtitle(target, local_path, need_langs[0])
        if ok:
            stats["downloaded"] += 1
            logger.info(f"[EmbySubtitleSync] 字幕补齐成功: {title} <- {sub_name}")
            await self._emby_refresh_item(client, item_id)
        else:
            stats["failed"] += 1
        self._add_history(title, item.get("ProductionYear") or "", media_type,
                          ",".join(need_langs), sub_name or "", ok)
        processed.add(item_id)
        if self._request_delay > 0:
            await asyncio.sleep(self._request_delay)
        return None

    # ------------------------------------------------------------------
    # 路径映射与字幕检测
    # ------------------------------------------------------------------

    def _map_path(self, emby_path: str) -> str | None:
        """将 Emby 侧路径映射为 MoviePilot 本机路径。"""
        if not emby_path:
            return None
        for src, dst in self._path_mappings:
            if emby_path.startswith(src):
                return dst + emby_path[len(src):]
        return emby_path

    def _check_chinese_subtitle(self, video_path: str, streams: list) -> tuple[bool, bool]:
        """检查是否已有中文字幕：内封字幕流 + 外挂字幕文件。返回 (有简体, 有繁体)。"""
        has_simp, has_trad = False, False

        # 内封字幕流
        for s in streams:
            if (s.get("Type") or "").lower() != "subtitle":
                continue
            lang = (s.get("Language") or "").lower().replace("_", "-")
            if lang not in self._ZH_LANG_TAGS:
                continue
            title = f"{s.get('DisplayTitle') or ''} {s.get('Title') or ''} {s.get('Name') or ''}"
            if re.search(r"traditional|繁", title, re.IGNORECASE):
                has_trad = True
            else:
                # 无法区分时按简体计（市面中文字幕多为简体）
                has_simp = True

        # 外挂字幕文件
        video_file = Path(video_path)
        stem = video_file.stem.lower()
        try:
            for f in video_file.parent.iterdir():
                if not f.is_file():
                    continue
                if f.suffix.lower() not in self._SUBTITLE_EXTS:
                    continue
                name = f.stem.lower()
                if not (name == stem or name.startswith(stem + ".")):
                    continue
                tag = name[len(stem):].lstrip(".")
                if any(m in tag for m in self._SIMP_FILE_MARKERS):
                    has_simp = True
                elif any(m in tag for m in self._TRAD_FILE_MARKERS):
                    has_trad = True
                elif any(m in tag for m in self._GENERIC_ZH_MARKERS) or not tag:
                    detected = self._detect_subtitle_lang(f)
                    if detected == "繁體中文":
                        has_trad = True
                    else:
                        has_simp = True
        except Exception as e:
            logger.debug(f"[EmbySubtitleSync] 外挂字幕扫描异常 {video_path}: {e}")

        return has_simp, has_trad

    def _detect_subtitle_lang(self, file_path: Path) -> str | None:
        """读取字幕文件内容，按繁体字比例判定简/繁。"""
        try:
            text = file_path.read_text(encoding="utf-8", errors="ignore")
        except Exception:
            return None
        # 取正文行（去掉序号和时间轴）
        lines = [ln for ln in text.splitlines()
                 if ln.strip() and not re.match(r"^\d+$", ln.strip())
                 and "-->" not in ln and not ln.strip().startswith(("WEBVTT", "NOTE"))]
        sample = "".join(lines[:200])
        if not sample:
            return None
        cjk = [c for c in sample if "\u4e00" <= c <= "\u9fff"]
        if not cjk:
            return None
        trad_count = sum(1 for c in cjk if c in self._TRAD_CHARS)
        return "繁體中文" if trad_count / len(cjk) > 0.15 else "简体中文"

    def _has_chinese_audio(self, streams: list) -> bool:
        """判断是否有中文音轨。"""
        for s in streams:
            if (s.get("Type") or "").lower() != "audio":
                continue
            lang = (s.get("Language") or "").lower().replace("_", "-")
            if lang in self._ZH_LANG_TAGS:
                return True
        return False

    # ------------------------------------------------------------------
    # 字幕搜索与筛选（与 AutoSubtitle 相同的字幕来源）
    # ------------------------------------------------------------------

    def _build_keyword(self, item: dict, media_type: str) -> str:
        """构造字幕搜索关键词。"""
        if media_type == "电影":
            name = item.get("OriginalTitle") or item.get("Name") or ""
            year = item.get("ProductionYear") or ""
            return f"{name} {year}".strip()
        # 剧集：系列名 + SxxExx
        series = item.get("SeriesName") or ""
        season = item.get("ParentIndexNumber")
        ep = item.get("IndexNumber")
        if season is not None and ep is not None:
            return f"{series} S{int(season):02d}E{int(ep):02d}".strip()
        return series.strip()

    # 各站点 language 字段格式不统一：多数站给文字（简体中文/English），
    # 馒头给数字代码（实测 25=中文类字幕，标题多为简体中字/双语/Mandarin；
    # 18=阿拉伯语）。以下别名/代码表 + 标题关键词兜底共同判定语言。
    _SIMP_ALIASES = {
        "简体中文", "简体", "简中", "简体中文版", "中英双语", "简繁双语",
        "双语", "双语字幕", "中英", "简英双语", "中文", "中文字幕",
        "chs", "zh-cn", "zh-hans", "zh_cn", "zh", "cn", "sc",
        "simplified chinese", "chinese (simplified)", "chinese",
    }
    _TRAD_ALIASES = {
        "繁體中文", "繁体中文", "繁体", "繁體", "繁中",
        "cht", "zh-tw", "zh-hk", "zh-hant", "zh_tw", "tc",
        "traditional chinese", "chinese (traditional)",
    }
    # 站点数字语言代码（key 为站点名包含的关键词）
    _SITE_LANG_CODES = {
        "馒头": {"25": "简体中文"},
        "m-team": {"25": "简体中文"},
        "mteam": {"25": "简体中文"},
    }

    def _resolve_sub_lang(self, sub: SubtitleInfo) -> tuple[str | None, int]:
        """判定一条字幕结果的语言。返回 (语言, 档位)：
        档位 0=字段明确匹配，1=标题关键词兜底，2=语言未知（other/空）。"""
        raw = (sub.language or "").strip()
        low = raw.lower()
        if raw in ("简体中文",) or low in self._SIMP_ALIASES:
            return "简体中文", 0
        if raw in ("繁體中文",) or low in self._TRAD_ALIASES:
            return "繁體中文", 0
        if raw.isdigit():
            site_name = (sub.site_name or "").lower()
            for key, table in self._SITE_LANG_CODES.items():
                if key in site_name and raw in table:
                    return table[raw], 0
        if raw in ("", "other", "未知", "unknown", "none"):
            return None, 2
        # 字段无法识别时用标题关键词兜底（阿拉伯语等外语标题不含这些词，不会误收）
        title = f"{sub.title or ''} {sub.file_name or ''}"
        if any(k in title for k in ("繁體", "繁中", "繁体")) or ".cht" in title.lower():
            return "繁體中文", 1
        if any(k in title for k in ("简体", "簡體", "中字", "中文字幕", "双语", "雙語",
                                    "汉化", "漢化", "压制", "chs")):
            return "简体中文", 1
        return None, -1  # 明确的外语，拒绝

    def _pick_best(self, results: list[SubtitleInfo], need_langs: set[str],
                   item: dict, media_type: str) -> SubtitleInfo | None:
        """从搜索结果中挑选最佳字幕：语言匹配 → 季集匹配 → 下载量/发布时间排序。"""
        candidates = []
        rejected = []
        for sub in results:
            lang, tier = self._resolve_sub_lang(sub)
            if tier == 2:
                lang = next(iter(need_langs)) if need_langs else None
            if lang is None or lang not in need_langs:
                rejected.append(sub)
                continue
            if media_type == "电视剧" and not self._match_episode(sub, item):
                rejected.append(sub)
                continue
            candidates.append((sub, lang, tier))
        if not candidates:
            if rejected:
                desc = "; ".join(
                    f"{s.site_name}/lang={s.language!r}/{(s.title or '')[:30]}"
                    for s in rejected[:8])
                logger.info(f"[EmbySubtitleSync] 候选字幕均被过滤（语言/季集不匹配）: {desc}")
            return None
        # 排序：先按旧规则（下载量/发布时间/站点优先级）降序，再稳定按档位升序
        def sort_key(pair: tuple) -> tuple:
            sub = pair[0]
            grabs = sub.grabs or 0
            pubdate = 0
            if sub.pubdate:
                try:
                    pubdate = datetime.strptime(sub.pubdate.split("T")[0], "%Y-%m-%d").toordinal()
                except (ValueError, IndexError):
                    pass
            site_order = -(sub.site_order or 0)
            return (grabs, pubdate, site_order)
        candidates.sort(key=sort_key, reverse=True)
        candidates.sort(key=lambda p: p[2])
        return candidates[0][0]

    def _match_episode(self, sub: SubtitleInfo, item: dict) -> bool:
        """剧集字幕的季/集匹配。"""
        try:
            sub_dict = sub.to_dict()
        except Exception:
            return True
        sub_se = sub_dict.get("season_episode")
        sub_ep_list = sub_dict.get("episode_list") or []
        if not sub_se and not sub_ep_list:
            return True  # 无季集信息，宽松通过
        season, ep = item.get("ParentIndexNumber"), item.get("IndexNumber")
        if season is None or ep is None:
            return True
        expected = f"S{int(season):02d}E{int(ep):02d}"
        if sub_se and str(sub_se).upper() == expected.upper():
            return True
        return bool(sub_ep_list and int(ep) in [int(x) for x in sub_ep_list])

    # ------------------------------------------------------------------
    # 字幕下载与落盘
    # ------------------------------------------------------------------

    async def _download_subtitle(self, target: SubtitleInfo, video_path: str, lang: str) -> tuple[bool, str | None]:
        """下载字幕 → 解压 → 重命名 → 放到视频目录。返回 (成功, 字幕名称)。"""
        sub_name = target.title or target.file_name or "unknown"
        work_dir = Path(self.get_data_path()) / "downloads" / uuid4().hex
        work_dir.mkdir(parents=True, exist_ok=True)
        try:
            client = AsyncRequestUtils(
                cookies=target.site_cookie,
                ua=target.site_ua or settings.USER_AGENT,
                proxies=settings.PROXY if target.site_proxy and settings.PROXY else {},
            )
            try:
                response = await client.get_res(target.enclosure)
            except Exception as e:
                logger.error(f"[EmbySubtitleSync] 下载请求失败: {e}")
                return False, None
            if not response or response.status_code != 200:
                logger.error(f"[EmbySubtitleSync] 下载失败 HTTP {response.status_code if response else 'N/A'}: {target.enclosure}")
                return False, None

            file_name = TorrentHelper.get_url_filename(response, target.enclosure) or f"{uuid4().hex}.srt"
            temp_file = work_dir / file_name
            temp_file.write_bytes(response.content)

            sub_files = self._extract_subtitle_files(temp_file, work_dir)
            if not sub_files:
                return False, None

            # 多文件时（如季包）尽量匹配单集
            if len(sub_files) > 1:
                stem = Path(video_path).stem
                m = re.search(r"[Ss](\d{1,2})[Ee](\d{1,3})", stem)
                if m:
                    tag = f"s{int(m.group(1)):02d}e{int(m.group(2)):02d}"
                    matched = [f for f in sub_files if tag in f.name.lower()]
                    if matched:
                        sub_files = matched[:1]
                sub_files = sub_files[:1]

            video_stem = Path(video_path).stem
            suffix = ".zh.srt" if lang == "简体中文" else ".cht.srt"
            dest = Path(video_path).parent / f"{video_stem}{suffix}"
            try:
                # 已存在则覆盖
                if dest.exists():
                    dest.unlink()
                sub_files[0].rename(dest)
            except Exception as e:
                logger.error(f"[EmbySubtitleSync] 字幕落盘失败: {e}")
                return False, None
            logger.info(f"[EmbySubtitleSync] 字幕已保存: {dest}")
            return True, sub_name
        finally:
            import shutil
            shutil.rmtree(work_dir, ignore_errors=True)

    def _extract_subtitle_files(self, temp_file: Path, save_dir: Path) -> list[Path]:
        """解压字幕压缩包（zip），单文件直接返回。"""
        suffix = temp_file.suffix.lower()
        if suffix == ".zip":
            try:
                with zipfile.ZipFile(temp_file) as zf:
                    zf.extractall(save_dir)
            except Exception as e:
                logger.error(f"[EmbySubtitleSync] 解压失败 {temp_file}: {e}")
                return []
            results = []
            for f in save_dir.rglob("*"):
                if f.is_file() and f.suffix.lower() in self._SUBTITLE_EXTS:
                    results.append(f)
            # 排除刚下载的压缩包本身
            return [f for f in results if f != temp_file]
        if suffix in self._SUBTITLE_EXTS:
            return [temp_file]
        # 尝试按 zip 处理无后缀文件
        try:
            with zipfile.ZipFile(temp_file) as zf:
                zf.extractall(save_dir)
            results = [f for f in save_dir.rglob("*")
                       if f.is_file() and f.suffix.lower() in self._SUBTITLE_EXTS and f != temp_file]
            if results:
                return results
        except Exception:
            pass
        logger.warning(f"[EmbySubtitleSync] 不支持的字幕文件格式: {temp_file.name}")
        return []

    # ------------------------------------------------------------------
    # 历史记录
    # ------------------------------------------------------------------

    def _load_history(self) -> list[dict]:
        data = self.get_data(self._HISTORY_KEY)
        if isinstance(data, str):
            try:
                return json.loads(data)
            except (json.JSONDecodeError, TypeError):
                return []
        return data if isinstance(data, list) else []

    def _add_history(self, title: str, year: str | int, media_type: str,
                     lang: str, sub_name: str, success: bool) -> None:
        history = self._load_history()
        history.insert(0, {
            "time": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "title": str(title),
            "year": str(year) if year else "",
            "type": media_type,
            "lang": lang,
            "sub_name": sub_name,
            "success": success,
        })
        if len(history) > self._HISTORY_MAX:
            history = history[:self._HISTORY_MAX]
        self.save_data(self._HISTORY_KEY, json.dumps(history, ensure_ascii=False))

    def _load_processed(self) -> set:
        data = self.get_data(self._PROCESSED_KEY)
        if isinstance(data, str):
            try:
                return set(json.loads(data))
            except (json.JSONDecodeError, TypeError):
                return set()
        return set(data) if isinstance(data, list) else set()

    def _save_processed(self, processed: set) -> None:
        self.save_data(self._PROCESSED_KEY, json.dumps(sorted(processed)))

    # ------------------------------------------------------------------
    # 配置表单
    # ------------------------------------------------------------------

    def _build_form(self) -> tuple[list[dict], dict[str, Any]]:
        _lib_names = self._fetch_emby_library_names()
        if _lib_names:
            _lib_field = self._col(6, "VSelect", {
                "model": "library_names",
                "label": "扫描的媒体库（不选=全部电影/电视剧库）",
                "multiple": True,
                "chips": True,
                "items": [{"title": n, "value": n} for n in _lib_names],
            })
        else:
            _lib_field = self._col(6, "VTextarea", {
                "model": "library_names",
                "label": "扫描的媒体库（每行一个，留空=全部电影/电视剧库）",
                "rows": 3,
                "placeholder": "电影\n剧集",
            })
        return [
            {
                "component": "VForm",
                "content": [
                    {
                        "component": "VRow",
                        "content": [
                            self._col(3, "VSwitch", {"model": "enabled", "label": "启用插件"}),
                            self._col(3, "VSwitch", {"model": "notify", "label": "发送通知"}),
                            self._col(3, "VSwitch", {"model": "only_foreign", "label": "仅处理外语内容"}),
                            self._col(3, "VSwitch", {"model": "run_once", "label": "保存后立即执行一次"}),
                        ],
                    },
                    {
                        "component": "VRow",
                        "content": [
                            self._col(6, "VTextField", {
                                "model": "emby_host",
                                "label": "Emby 服务器地址",
                                "placeholder": "http://192.168.1.100:8096",
                            }),
                            self._col(6, "VTextField", {
                                "model": "emby_api_key",
                                "label": "Emby API Key",
                                "type": "password",
                                "placeholder": "在 Emby 控制台 > 高级 > API 密钥 中创建",
                            }),
                        ],
                    },
                    {
                        "component": "VRow",
                        "content": [
                            _lib_field,
                            self._col(6, "VTextarea", {
                                "model": "path_mappings",
                                "label": "路径映射（每行一条：Emby路径=本机路径）",
                                "rows": 3,
                                "placeholder": "/media=/mnt/media",
                            }),
                        ],
                    },
                    {
                        "component": "VRow",
                        "content": [
                            {
                                "component": "VCol",
                                "props": {"cols": 12, "md": 3},
                                "content": [
                                    {
                                        "component": "VSelect",
                                        "props": {
                                            "model": "subtitle_langs",
                                            "label": "字幕语言",
                                            "multiple": True,
                                            "chips": True,
                                            "items": [
                                                {"title": "简体中文", "value": "简体中文"},
                                                {"title": "繁体中文", "value": "繁體中文"},
                                            ],
                                        },
                                    }
                                ],
                            },
                            self._col(3, "VTextField", {"model": "request_delay", "label": "请求间隔(秒)", "placeholder": "2"}),
                            self._col(3, "VTextField", {"model": "max_count", "label": "每次最多处理(个,0=不限)", "placeholder": "200"}),
                            self._col(3, "VTextField", {"model": "cron", "label": "定时执行(cron)", "placeholder": "0 3 * * *"}),
                        ],
                    },
                    {
                        "component": "VRow",
                        "content": [
                            self._col(3, "VSwitch", {"model": "dry_run", "label": "仅扫描报告（不下载）"}),
                            self._col(3, "VSwitch", {"model": "clear_processed", "label": "清空已处理记录"}),
                            self._col(3, "VSwitch", {"model": "clear_history", "label": "清空下载历史"}),
                        ],
                    },
                ],
            }
        ], {
            "enabled": False,
            "notify": False,
            "only_foreign": True,
            "run_once": False,
            "emby_host": "",
            "emby_api_key": "",
            "library_names": [],
            "path_mappings": "",
            "subtitle_langs": ["简体中文"],
            "request_delay": 2,
            "max_count": 200,
            "cron": "0 3 * * *",
            "clear_processed": False,
            "clear_history": False,
            "dry_run": True,
        }

    @staticmethod
    def _col(md: int, component: str, props: dict) -> dict:
        return {
            "component": "VCol",
            "props": {"cols": 12, "md": md},
            "content": [{"component": component, "props": props}],
        }

    # ------------------------------------------------------------------
    # 数据页面
    # ------------------------------------------------------------------

    def _build_page(self) -> list[dict]:
        history = self._load_history()
        if not history:
            return [
                {
                    "component": "VAlert",
                    "props": {
                        "type": "info",
                        "variant": "tonal",
                        "text": "暂无字幕补齐记录。配置好 Emby 连接信息并启用插件后，将按定时计划扫描媒体库补齐缺失的中文字幕。",
                    },
                }
            ]
        total = len(history)
        success_count = sum(1 for h in history if h.get("success"))
        fail_count = total - success_count
        page: list[dict] = [
            {
                "component": "VAlert",
                "props": {
                    "type": "success" if fail_count == 0 else "warning",
                    "variant": "tonal",
                    "text": f"共 {total} 条补齐记录，成功 {success_count} 条，失败 {fail_count} 条。最多保留最近 {self._HISTORY_MAX} 条。",
                    "class": "mb-2",
                },
            }
        ]
        for entry in history:
            success = entry.get("success")
            page.append(
                {
                    "component": "VCard",
                    "props": {"class": "mb-2"},
                    "content": [
                        {
                            "component": "VCardText",
                            "content": [
                                {
                                    "component": "div",
                                    "props": {
                                        "class": "font-weight-bold "
                                                 + ("text-success" if success else "text-error"),
                                        "text": f"{'✓' if success else '✗'} {entry.get('title', '')}"
                                                f"{' (' + str(entry.get('year')) + ')' if entry.get('year') else ''}"
                                                f" [{entry.get('type', '')}]",
                                    },
                                },
                                {
                                    "component": "div",
                                    "props": {
                                        "class": "text-caption text-medium-emphasis",
                                        "text": f"{entry.get('time', '')}｜补齐{entry.get('lang', '')}｜"
                                                f"{entry.get('sub_name', '') or '未找到合适字幕'}",
                                    },
                                },
                            ],
                        }
                    ],
                }
            )
        return page
