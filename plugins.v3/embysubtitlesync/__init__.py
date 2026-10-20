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
    plugin_version = "2.6.0"
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
        # 额外字幕源（v2.3.0，参考 SubtitleAssistant 的源实现）
        self._assrt_enabled = False
        self._assrt_token = ""
        self._opensubtitles_enabled = False
        self._os_api_key = ""
        self._os_username = ""
        self._os_password = ""
        self._os_jwt: str | None = None
        self._os_base_url = "https://api.opensubtitles.com/api/v1"
        self._assrt_dl_times: list[float] = []
        # v2.6.0 剧集改造（学 CSF）：整季包缓存 + ASSRT 搜索限速/限流熔断
        self._pack_cache: dict[str, list] = {}
        self._assrt_last_search = 0.0
        self._assrt_cooldown_until = 0.0

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
            # 额外字幕源配置
            self._assrt_enabled = config.get("assrt_enabled", False) or False
            self._assrt_token = (config.get("assrt_token") or "").strip()
            self._opensubtitles_enabled = config.get("opensubtitles_enabled", False) or False
            self._os_api_key = (config.get("os_api_key") or "").strip()
            self._os_username = (config.get("os_username") or "").strip()
            self._os_password = (config.get("os_password") or "").strip()

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
            "assrt_enabled": self._assrt_enabled,
            "assrt_token": self._assrt_token,
            "opensubtitles_enabled": self._opensubtitles_enabled,
            "os_api_key": self._os_api_key,
            "os_username": self._os_username,
            "os_password": self._os_password,
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
                    "Fields": "Path,MediaSources,ProductionYear,OriginalTitle,ProviderIds",
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
                    "Fields": "Path,ProductionYear,OriginalTitle,ProviderIds",
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
                    "Fields": "Path,MediaSources,SeriesName,ParentIndexNumber,IndexNumber,ProviderIds",
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

                # 整季包缓存按轮重置（包文件只在本轮内复用，避免磁盘堆积）
                self._pack_cache = {}
                try:
                    import shutil as _sh
                    _sh.rmtree(Path(self.get_data_path()) / "season_packs", ignore_errors=True)
                except Exception:
                    pass

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
                            r = await self._process_item_safe(client, movie, "电影", processed, stats)
                            if r == "limit":
                                stop = True
                    else:
                        async for series in self._iter_series(client, lib["id"]):
                            if stop:
                                break
                            async for ep in self._iter_episodes(client, series["Id"]):
                                if stop:
                                    break
                                r = await self._process_item_safe(client, ep, "电视剧", processed, stats,
                                                                  series_item=series)
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

    async def _process_item_safe(self, client: httpx.AsyncClient, item: dict, media_type: str,
                                 processed: set, stats: dict, series_item: dict | None = None) -> str | None:
        """_process_item 的隔离包装：单条异常只记失败并跳过，绝不拖垮整轮扫描。"""
        try:
            return await self._process_item(client, item, media_type, processed, stats,
                                            series_item=series_item)
        except Exception as e:
            logger.error(f"[EmbySubtitleSync] 处理条目异常（已跳过）: {item.get('Name') or item.get('Id')}: {e}")
            stats["failed"] += 1
            return None

    async def _process_item(self, client: httpx.AsyncClient, item: dict, media_type: str,
                            processed: set, stats: dict, series_item: dict | None = None) -> str | None:
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

        # 显示名与剧集上下文：剧集用「剧名 SxxExx」展示与记历史（原单集名如"有罪之人"无从辨认是哪部剧）
        title = item.get("Name") or Path(local_path).stem
        disp_title = title
        tv = None
        if media_type == "电视剧":
            _series = series_item or {}
            _sname = item.get("SeriesName") or _series.get("Name") or title
            _sn, _epn = item.get("ParentIndexNumber"), item.get("IndexNumber")
            if _sn is not None and _epn is not None:
                disp_title = f"{_sname} S{int(_sn):02d}E{int(_epn):02d}"
                tv = {"season": int(_sn), "episode": int(_epn),
                      "cache_key": f"{self._norm_title(_sname)}|S{int(_sn):02d}"}
            else:
                disp_title = _sname
        hist_year = item.get("ProductionYear") or (series_item or {}).get("ProductionYear") or ""

        # 2.5 dry-run：确认缺字幕且为外语内容后只登记清单，不搜索不下载不标记已处理
        if self._dry_run:
            stats["dry_run_candidates"] += 1
            if len(self._dry_run_samples) < 20:
                yr = item.get("ProductionYear") or ""
                self._dry_run_samples.append(f"{disp_title}({yr})[{media_type}]" if yr else f"{disp_title}[{media_type}]")
            logger.info(f"[EmbySubtitleSync][dry-run] 待补齐: {disp_title} 缺 {','.join(need_langs)}")
            return None

        # 3.0 整季包缓存（CSF 式）：同剧同季已下过的字幕包先在本地挑本集，命中就不联网
        if tv and self._try_season_cache(tv, local_path, need_langs[0]):
            stats["downloaded"] += 1
            logger.info(f"[EmbySubtitleSync] 字幕补齐成功（整季包缓存）: {disp_title}")
            await self._emby_refresh_item(client, item_id)
            self._add_history(disp_title, hist_year, media_type,
                              ",".join(need_langs), "整季包缓存命中", True)
            processed.add(item_id)
            return None

        # 3. 搜索并下载：多标题依次尝试（剧集先原名后中文名——站点字幕多按原名索引）
        target = None
        for keyword in self._build_keywords(item, media_type, series_item):
            logger.info(f"[EmbySubtitleSync] 缺失{','.join(need_langs)}字幕，搜索: {keyword}")
            try:
                results = await SearchChain().async_search_subtitles_by_title(title=keyword, page=0)
            except Exception as e:
                logger.error(f"[EmbySubtitleSync] 字幕搜索异常 {keyword}: {e}")
                results = None
            if results:
                target = self._pick_best(results, set(need_langs), item, media_type)
            if target:
                break
        ok, sub_name = False, None
        if target:
            ok, sub_name = await self._download_subtitle(target, local_path, need_langs[0], tv=tv)
        if not ok:
            # 站点搜索无果或下载失败 → 额外字幕源兜底（ASSRT → OpenSubtitles）
            ok, sub_name = await self._try_extra_sources(item, media_type, series_item,
                                                         local_path, need_langs[0])
        if not ok:
            logger.info(f"[EmbySubtitleSync] 未找到合适字幕: {disp_title}")
            stats["failed"] += 1
            self._add_history(disp_title, hist_year, media_type,
                              ",".join(need_langs), "", False)
            processed.add(item_id)
            return None

        stats["downloaded"] += 1
        logger.info(f"[EmbySubtitleSync] 字幕补齐成功: {disp_title} <- {sub_name}")
        await self._emby_refresh_item(client, item_id)
        self._add_history(disp_title, hist_year, media_type,
                          ",".join(need_langs), sub_name or "", True)
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

    def _build_keywords(self, item: dict, media_type: str,
                        series_item: dict | None = None) -> list[str]:
        """构造字幕搜索关键词列表（按优先级依次尝试，命中可下载候选即停）。
        剧集学 CSF 的多标题检索：先用原名+季集（PT 站字幕多按原名索引，
        只用中文剧名实测 10 站全 0 结果），再用中文剧名兜底。"""
        if media_type == "电影":
            name = item.get("OriginalTitle") or item.get("Name") or ""
            year = item.get("ProductionYear") or ""
            kws = [f"{name} {year}".strip()]
            cn = item.get("Name") or ""
            if cn and cn != name:
                kws.append(f"{cn} {year}".strip())
            return [k for k in kws if k]
        # 剧集：系列原名/中文名 + SxxExx
        series = series_item or {}
        sname = item.get("SeriesName") or series.get("Name") or ""
        sorig = series.get("OriginalTitle") or item.get("OriginalTitle") or ""
        season, ep = item.get("ParentIndexNumber"), item.get("IndexNumber")
        tag = f"S{int(season):02d}E{int(ep):02d}" if season is not None and ep is not None else ""
        kws: list[str] = []
        for base in (sorig, sname):
            if base:
                kw = f"{base} {tag}".strip()
                if kw not in kws:
                    kws.append(kw)
        return kws or ([sname] if sname else [])

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

    # 中英双语标记（v2.5.0 字幕优先级：双语 > 纯简体中文）
    _BILINGUAL_MARKERS = (
        "双语", "雙語", "中英", "简英", "繁英", "中英双字", "双字幕",
        "bilingual", "dual", "chs-eng", "chs_eng", "cht-eng", "cht_eng",
        "zh-en", "zh_en", "cn-en", "cn_en", "eng-chs", "eng-cht",
    )

    def _is_bilingual_text(self, *texts: str) -> bool:
        """文本（语言字段/标题/文件名/发布名）是否表明这是中英双语字幕。"""
        blob = " ".join(t for t in texts if t).lower()
        return any(m in blob for m in self._BILINGUAL_MARKERS)

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
        """从搜索结果中挑选最佳字幕：语言匹配 → 季集匹配 → 年份校验 → 版本/下载量排序。"""
        candidates = []
        rejected = []
        _res, _tags = self._video_specs(item)
        spec_ctx = {"res": _res, "src_tags": _tags}
        item_year = self._to_int(item.get("ProductionYear"))
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
            # 年份硬校验：候选带年份且与目标不一致 → 拒绝，防同名不同年份误配
            cy = self._find_year(f"{sub.title or ''} {sub.file_name or ''}")
            if cy and item_year and cy != item_year:
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
        # 同语言档内优先分辨率/版本与视频一致的候选（稳定排序，不改变既有次序维度）
        candidates.sort(
            key=lambda p: self._spec_bonus(spec_ctx, f"{p[0].title or ''} {p[0].file_name or ''}"),
            reverse=True)
        candidates.sort(key=lambda p: p[2])
        # 字幕优先级（v2.5.0）：中英双语优先于纯简体中文——稳定排序放最后，双语组内保留既有次序
        candidates.sort(
            key=lambda p: 0 if self._is_bilingual_text(
                p[0].language or "", p[0].title or "", p[0].file_name or "") else 1)
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

    async def _download_subtitle(self, target: SubtitleInfo, video_path: str, lang: str,
                                 tv: dict | None = None) -> tuple[bool, str | None]:
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

            try:
                file_name = TorrentHelper.get_url_filename(response, target.enclosure) or ""
            except Exception as e:
                # MP 核心 get_url_filename 对含中文的 Content-Disposition 文件名
                # 会抛 latin-1 编码错误（其内部 encode('ISO-8859-1')），兜底改用候选自带文件名
                logger.warning(f"[EmbySubtitleSync] 解析下载文件名失败，改用候选文件名: {e}")
                file_name = ""
            if not file_name or "/" in file_name or "\\" in file_name:
                file_name = Path(target.file_name or "").name
            if not file_name:
                file_name = f"{uuid4().hex}.srt"
            temp_file = work_dir / file_name
            temp_file.write_bytes(response.content)

            if self._place_subtitle(temp_file, work_dir, video_path, lang, tv=tv):
                return True, sub_name
            return False, None
        finally:
            import shutil
            shutil.rmtree(work_dir, ignore_errors=True)

    # ---------------- 剧集集号解析与整季包（v2.6.0，学 CSF 的包内逐集匹配） ----------------

    _CN_DIGITS = {"一": 1, "二": 2, "三": 3, "四": 4, "五": 5,
                  "六": 6, "七": 7, "八": 8, "九": 9}

    @staticmethod
    def _cn_to_int(s: str) -> int | None:
        """中文数字转整数（支持一~九十九，如 十二=12、二十三=23）。"""
        if not s:
            return None
        d = EmbySubtitleSync._CN_DIGITS
        if s == "十":
            return 10
        if "十" in s:
            a, _, b = s.partition("十")
            tens = d.get(a, 1) if a else 1
            ones = d.get(b, 0) if b else 0
            return tens * 10 + ones
        return d.get(s)

    @staticmethod
    def _parse_episode_tag(name: str) -> tuple[int | None, int] | None:
        """从字幕文件名解析 (季, 集)；季未知时季为 None。解析不到返回 None。
        覆盖 CSF 常见的集号写法：S01E02、1x02、第5集/第十二集、EP07、裸集号开头。"""
        low = (name or "").lower()
        m = re.search(r"s(\d{1,2})[\s._\-]*e(\d{1,3})", low)
        if m:
            return int(m.group(1)), int(m.group(2))
        m = re.search(r"(?<!\d)(\d{1,2})x(\d{1,3})(?!\d)", low)
        if m:
            return int(m.group(1)), int(m.group(2))
        m = re.search(r"第(\d{1,3})[集話话]", low)
        if m:
            return None, int(m.group(1))
        m = re.search(r"第([一二三四五六七八九十]{1,3})[集話话]", name or "")
        if m:
            n = EmbySubtitleSync._cn_to_int(m.group(1))
            if n:
                return None, n
        m = re.search(r"(?<![a-z])ep(\d{1,3})(?!\d)", low)
        if m:
            return None, int(m.group(1))
        m = re.match(r"(\d{1,3})(?:[.\s_\-]|$)", low)
        if m:
            return None, int(m.group(1))
        return None

    def _pick_episode_file(self, files: list, tv: dict | None) -> Path | None:
        """在字幕文件列表里挑出目标集的文件（CSF 式包内逐集匹配）。
        精确 (季,集) 命中优先；只有集号且对得上次之；单文件包直接用它。"""
        if not tv:
            return files[0] if len(files) == 1 else None
        s, e = tv["season"], tv["episode"]
        ep_only = []
        for f in files:
            se = self._parse_episode_tag(f.name)
            if se is None:
                continue
            if se[0] is not None and se == (s, e):
                return f
            if se[0] is None and se[1] == e:
                ep_only.append(f)
        if ep_only:
            return ep_only[0]
        if len(files) == 1:
            return files[0]
        return None

    def _stash_pack(self, tv: dict, files: list) -> None:
        """把整包字幕文件存入按「剧+季」缓存，供同季后续集本地挑集、免重复联网下载。"""
        try:
            import hashlib
            import shutil
            key = hashlib.md5(tv["cache_key"].encode("utf-8")).hexdigest()[:16]
            cache_dir = Path(self.get_data_path()) / "season_packs" / key
            cache_dir.mkdir(parents=True, exist_ok=True)
            merged = {p.name: p for p in self._pack_cache.get(tv["cache_key"], [])}
            for f in files:
                dst = cache_dir / f.name
                try:
                    if Path(f).resolve() != dst.resolve():
                        shutil.copyfile(f, dst)
                except Exception:
                    continue
                merged[dst.name] = dst
            self._pack_cache[tv["cache_key"]] = list(merged.values())
        except Exception as e:
            logger.debug(f"[EmbySubtitleSync] 整季包缓存写入失败（忽略）: {e}")

    @staticmethod
    def _dest_for(video_path: str, lang: str, ext: str) -> Path:
        lang_tag = ".zh" if lang == "简体中文" else ".cht"
        return Path(video_path).parent / f"{Path(video_path).stem}{lang_tag}{ext}"

    def _try_season_cache(self, tv: dict, video_path: str, lang: str) -> bool:
        """先查整季包缓存：挑中本集文件就直接落盘，返回 True。"""
        files = [Path(f) for f in self._pack_cache.get(tv["cache_key"], []) if Path(f).is_file()]
        if not files:
            return False
        picked = self._pick_episode_file(files, tv)
        if not picked:
            return False
        dest = self._dest_for(video_path, lang, picked.suffix.lower() or ".srt")
        try:
            import shutil
            shutil.copyfile(picked, dest)
        except Exception as e:
            logger.error(f"[EmbySubtitleSync] 缓存字幕落盘失败: {e}")
            return False
        logger.info(f"[EmbySubtitleSync] 字幕已保存: {dest}")
        return True

    def _place_subtitle(self, downloaded_file: Path, work_dir: Path, video_path: str, lang: str,
                        tv: dict | None = None) -> bool:
        """把已下载到 work_dir 的字幕文件（单文件或压缩包）解压、挑选并落盘到视频旁。"""
        sub_files = self._extract_subtitle_files(downloaded_file, work_dir)
        if not sub_files:
            return False

        # 整季包先整包入缓存（同季后续集可直接命中），再挑本集
        if tv and len(sub_files) > 1:
            self._stash_pack(tv, sub_files)
            picked = self._pick_episode_file(sub_files, tv)
            if picked is not None:
                sub_files = [picked]
            elif len(sub_files) > 1:
                # 包里挑不出本集：宁可失败也不乱放别集的字幕
                logger.info(f"[EmbySubtitleSync] 字幕包内未找到 S{tv['season']:02d}E{tv['episode']:02d} 对应文件")
                return False
        elif len(sub_files) > 1:
            # 电影多文件时（如季包误入）尽量按视频名中的 SxxExx 匹配单集
            stem = Path(video_path).stem
            m = re.search(r"[Ss](\d{1,2})[Ee](\d{1,3})", stem)
            if m:
                tag = f"s{int(m.group(1)):02d}e{int(m.group(2)):02d}"
                matched = [f for f in sub_files if tag in f.name.lower()]
                if matched:
                    sub_files = matched[:1]
            sub_files = sub_files[:1]

        src_file = sub_files[0]
        # 保留字幕真实扩展名（.srt/.ass/.ssa/.vtt 等），不要硬编码 .srt
        dest = self._dest_for(video_path, lang, src_file.suffix.lower() or ".srt")
        try:
            # 下载目录（/config）与媒体目录是不同挂载，
            # rename 跨设备会报 Errno 18，必须用复制落盘（copyfile 自带覆盖）
            import shutil
            shutil.copyfile(src_file, dest)
        except Exception as e:
            logger.error(f"[EmbySubtitleSync] 字幕落盘失败: {e}")
            return False
        logger.info(f"[EmbySubtitleSync] 字幕已保存: {dest}")
        return True

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
        if suffix in (".rar", ".7z"):
            # ASSRT 等来源常见 rar/7z 打包：借系统工具解压（无工具则明确记日志）
            import shutil as _sh
            import subprocess as _sp
            out_dir = save_dir / f"ext_{temp_file.stem}"
            out_dir.mkdir(parents=True, exist_ok=True)
            tool_cmd = None
            if _sh.which("unrar"):
                tool_cmd = ["unrar", "x", "-o+", "-inul", str(temp_file), str(out_dir) + "/"]
            elif _sh.which("7z"):
                tool_cmd = ["7z", "x", "-y", f"-o{out_dir}", str(temp_file)]
            elif _sh.which("unar"):
                tool_cmd = ["unar", "-f", "-o", str(out_dir), str(temp_file)]
            if not tool_cmd:
                logger.warning(f"[EmbySubtitleSync] 系统无 rar/7z 解压工具，无法处理: {temp_file.name}")
                return []
            try:
                _sp.run(tool_cmd, capture_output=True, timeout=120)
            except Exception as e:
                logger.error(f"[EmbySubtitleSync] 解压失败 {temp_file}: {e}")
                return []
            return [f for f in out_dir.rglob("*")
                    if f.is_file() and f.suffix.lower() in self._SUBTITLE_EXTS]
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
    # 额外字幕源（v2.3.0）：ASSRT（射手网） / OpenSubtitles
    # 接口实现参考 SubtitleAssistant（字幕助手）的 source/assrt.py、source/opensubtitles.py
    # 站点搜索无果时按 ASSRT → OpenSubtitles 顺序兜底
    # ------------------------------------------------------------------

    _ASSRT_BASE = "https://api.assrt.net/v1"
    _OS_UA = "MoviePilot EmbySubtitleSync/2.6.0"

    @staticmethod
    def _to_float(v) -> float:
        try:
            return float(v or 0)
        except (TypeError, ValueError):
            return 0.0

    @staticmethod
    def _to_int(v) -> int | None:
        try:
            return int(v)
        except (TypeError, ValueError):
            return None

    # ---------------- 匹配精准度工具（v2.4.0） ----------------

    @staticmethod
    def _norm_title(s: str) -> str:
        """标题归一化：转小写，只保留字母、数字与汉字（去标点/空格/符号）。"""
        return re.sub(r"[^0-9a-z\u4e00-\u9fff]+", "", (s or "").lower())

    @staticmethod
    def _find_year(text: str) -> int | None:
        m = re.search(r"(?:19|20)\d{2}", text or "")
        return int(m.group(0)) if m else None

    @staticmethod
    def _res_bucket(text: str) -> int:
        """从文本中提取分辨率档（2160/1080/720/480），无则 0。"""
        t = (text or "").lower()
        if "2160" in t or "4k" in t or "uhd" in t:
            return 2160
        if "1080" in t:
            return 1080
        if "720" in t:
            return 720
        if "480" in t:
            return 480
        return 0

    def _video_specs(self, item: dict) -> tuple[int, set[str]]:
        """目标视频的 (分辨率档, 版本标签集合)：优先媒体流宽高，其次文件名。"""
        fname = Path(item.get("Path") or "").name
        res = 0
        try:
            streams = ((item.get("MediaSources") or [{}])[0].get("MediaStreams") or [])
            for st in streams:
                if st.get("Type") == "Video":
                    w = int(st.get("Width") or 0)
                    if w >= 3000:
                        res = 2160
                    elif w >= 1200:
                        res = 1080
                    elif w >= 900:
                        res = 720
                    elif w >= 600:
                        res = 480
                    break
        except Exception:
            pass
        if not res:
            res = self._res_bucket(fname)
        tags: set[str] = set()
        low = fname.lower().replace("-", "")
        for tag in ("remux", "bluray", "bdrip", "webdl", "webrip", "hdtv", "dvdrip", "uhd"):
            if tag in low:
                tags.add(tag)
        return res, tags

    def _title_matches(self, ctx: dict, text: str) -> bool:
        """候选文本是否确实命中目标作品（防《赤发白雪姬》蹭《白雪公主》式误配）：
        - 候选的任一别名分段（按 / | 、,; 分割）归一化后与目标中文名/原名相等 → 命中；
        - 或某分段内嵌目标英文原名，且原名之后紧跟的不是英文字母 → 命中
          （发布名多为"原名+年份+规格"，原名后跟数字/年份属正常；
          若后跟字母，如 "Snow White with the Red Hair"，那是另一部更长的片名，拒绝）。
        中文名不接受任意包含（"红发的白雪公主"包含"白雪公主"但并非同一作品），
        只接受相等，或以目标名开头且后跟季集/年份后缀（剧集候选的常态）。"""
        targets = set()
        for t in (ctx.get("name"), ctx.get("original")):
            n = self._norm_title(t or "")
            if len(n) >= 2:
                targets.add(n)
        if not targets:
            return True  # 无标题信息可校验时不拦截
        orig = self._norm_title(ctx.get("original") or "")
        # 归一化后紧跟目标名的合法后缀：季集标记/年份（剧集候选几乎必然带 SxxExx，
        # 不放行会把真字幕误杀——v2.6.0 实测教训；仍拒绝"with the Red Hair"式更长片名）
        _suffix_ok = re.compile(
            r"(s\d{1,2}(e\d{1,3})?|season\d*|ep\d{1,3}|e\d{1,3}|"
            r"第[一二三四五六七八九十\d]{1,3}[集季話话]|\d{4})")
        parts = re.split(r"[/|、,，;；·]", text or "")
        # 整段兜底：剧名本身含分隔符（如"阿曼达·诺克斯"里的·）时，分段会把剧名拆散，
        # 整段归一化后仍能前缀命中；整段以目标名开头才可能命中，不削弱防蹭逻辑
        parts.append(text or "")
        for part in parts:
            np = self._norm_title(part)
            if np in targets:
                return True
            # 前缀命中：分段以目标名开头且其后是季集/年份后缀 → 同一作品
            # （前缀判定不怕"红发的白雪公主"——它以"红发"开头而非以目标名开头）
            for t in targets:
                if np.startswith(t) and _suffix_ok.match(np[len(t):]):
                    return True
            if len(orig) >= 4:
                i = np.find(orig)
                if i >= 0:
                    rest = np[i + len(orig):]
                    after = rest[:1]
                    if not (after and after.isascii() and after.isalpha()):
                        return True
                    if _suffix_ok.match(rest):
                        return True
        return False

    def _spec_bonus(self, ctx: dict, text: str) -> float:
        """版本匹配加分：分辨率同档 +30，版本标签（Remux/BluRay/WEB-DL 等）命中每个 +10。"""
        bonus = 0.0
        cres = self._res_bucket(text)
        if ctx.get("res") and cres and cres == ctx["res"]:
            bonus += 30
        low = (text or "").lower().replace("-", "")
        for tag in ctx.get("src_tags") or ():
            if tag in low:
                bonus += 10
        return bonus

    async def _assrt_download_gate(self) -> None:
        """ASSRT 下载限流：每分钟最多 5 个（站点规则），超限等待窗口滑动后再放行。"""
        import time as _time
        now = _time.monotonic()
        self._assrt_dl_times = [t for t in self._assrt_dl_times if now - t < 60]
        if len(self._assrt_dl_times) >= 5:
            wait = 60 - (now - self._assrt_dl_times[0]) + 1
            logger.info(f"[EmbySubtitleSync] ASSRT 下载限流（5 个/分钟），等待 {wait:.0f} 秒")
            await asyncio.sleep(wait)
            now = _time.monotonic()
            self._assrt_dl_times = [t for t in self._assrt_dl_times if now - t < 60]
        self._assrt_dl_times.append(now)

    def _extra_ctx(self, item: dict, media_type: str, series_item: dict | None) -> dict:
        """汇总额外源搜索所需的标题/年份/季集/外部 ID/版本规格。"""
        series = series_item or {}

        def _pid(d: dict, key: str):
            return (d.get("ProviderIds") or {}).get(key)

        res, tags = self._video_specs(item)
        return {
            "is_tv": media_type == "电视剧",
            "name": item.get("SeriesName") or item.get("Name") or "",
            "original": item.get("OriginalTitle") or series.get("OriginalTitle") or "",
            "year": item.get("ProductionYear") or series.get("ProductionYear"),
            "season": item.get("ParentIndexNumber"),
            "episode": item.get("IndexNumber"),
            "tmdb": _pid(item, "Tmdb") or _pid(series, "Tmdb"),
            "imdb": _pid(item, "Imdb") or _pid(series, "Imdb"),
            "res": res,
            "src_tags": tags,
        }

    async def _try_extra_sources(self, item: dict, media_type: str, series_item: dict | None,
                                 video_path: str, lang: str) -> tuple[bool, str | None]:
        """站点无果时的兜底入口：依次尝试已启用的额外字幕源。"""
        ctx = self._extra_ctx(item, media_type, series_item)
        tv = None
        if ctx["is_tv"] and ctx["season"] is not None and ctx["episode"] is not None:
            tv = {"season": int(ctx["season"]), "episode": int(ctx["episode"]),
                  "cache_key": f"{self._norm_title(ctx['name'])}|S{int(ctx['season']):02d}"}
        if self._assrt_enabled and self._assrt_token:
            try:
                ok, name = await self._assrt_fetch(ctx, video_path, lang, tv=tv)
            except Exception as e:
                logger.error(f"[EmbySubtitleSync] ASSRT 异常: {e}")
                ok, name = False, None
            if ok:
                return True, name
        if self._opensubtitles_enabled and self._os_api_key and self._os_username and self._os_password:
            try:
                ok, name = await self._os_fetch(ctx, video_path, lang, tv=tv)
            except Exception as e:
                logger.error(f"[EmbySubtitleSync] OpenSubtitles 异常: {e}")
                ok, name = False, None
            if ok:
                return True, name
        return False, None

    # ---------------- ASSRT（射手网） ----------------

    @staticmethod
    def _assrt_flag(flags, k: str) -> bool:
        v = flags.get(k) if isinstance(flags, dict) else None
        return v in (True, 1, "1") or (isinstance(v, str) and v.lower() in ("true", "yes"))

    @classmethod
    def _assrt_bilingual(cls, sub: dict) -> bool:
        """ASSRT 条目是否为中英双语：desc 含双语标记，或语言列表同时含中文与英文。"""
        lang_data = sub.get("lang") or {}
        desc = str(lang_data.get("desc") or "")
        flags = lang_data.get("langlist") or {}
        if "双语" in desc or "雙語" in desc or "中英" in desc:
            return True
        has_zh = cls._assrt_flag(flags, "langchs") or cls._assrt_flag(flags, "langcht")
        has_en = cls._assrt_flag(flags, "langeng")
        if has_zh and has_en:
            return True
        return any(cls._assrt_flag(flags, k) for k in flags if isinstance(k, str) and "dou" in k)

    @classmethod
    def _assrt_lang_ok(cls, sub: dict, lang: str) -> bool:
        """按 ASSRT 的 lang.desc / lang.langlist 判断是否为目标中文。"""
        lang_data = sub.get("lang") or {}
        desc = str(lang_data.get("desc") or "")
        flags = lang_data.get("langlist") or {}
        if lang == "简体中文":
            if "简" in desc or cls._assrt_flag(flags, "langchs"):
                return True
            # 双语条目 desc 可能只写"双语/中英"不带"简"字：非繁体时按简体接收（双语优先策略需要）
            if cls._assrt_bilingual(sub) and "繁" not in desc and not cls._assrt_flag(flags, "langcht"):
                return True
            return False
        return "繁" in desc or cls._assrt_flag(flags, "langcht")

    async def _assrt_search_gate(self) -> None:
        """ASSRT 搜索限速：两次搜索至少间隔 4 秒（实测连搜数次即 HTTP 509 限流）。"""
        import time as _time
        wait = 4.0 - (_time.monotonic() - self._assrt_last_search)
        if wait > 0:
            await asyncio.sleep(wait)
        self._assrt_last_search = _time.monotonic()

    def _assrt_trip_cooldown(self, why: str) -> None:
        """ASSRT 限流熔断：置冷却期，本轮后续条目直接跳过该源，不再逐集撞限流。"""
        import time as _time
        self._assrt_cooldown_until = _time.monotonic() + 900
        logger.warning(f"[EmbySubtitleSync] ASSRT 触发限流（{why}），冷却 15 分钟，本轮后续跳过该源")

    def _assrt_ep_fit(self, ctx: dict, text: str) -> tuple[bool, float]:
        """剧集候选与目标集的契合度（CSF 式：整季包可用、包内再挑集）：
        - 含目标集 SxxExx → 可用 +15；
        - 含整季/全集标记 → 可用 +8（哪怕也带别的集号，多半是季包）；
        - 明确只有其他单集标记 → 不可用；
        - 无集号信息（只有剧名等）→ 可用 +0，靠标题校验把关。"""
        if not ctx.get("is_tv") or ctx.get("season") is None or ctx.get("episode") is None:
            return True, 0.0
        low = (text or "").lower()
        tag = f"s{int(ctx['season']):02d}e{int(ctx['episode']):02d}"
        if tag in low:
            return True, 15.0
        pack = any(m in low for m in ("全集", "整季", "全季", "合集", "complete", "pack"))
        has_ep = bool(re.search(r"s\d{1,2}e\d{1,3}", low))
        if has_ep and not pack:
            return False, 0.0
        if pack:
            return True, 8.0
        return True, 0.0

    async def _assrt_fetch(self, ctx: dict, video_path: str, lang: str,
                           tv: dict | None = None) -> tuple[bool, str | None]:
        import time as _time
        if _time.monotonic() < self._assrt_cooldown_until:
            logger.debug("[EmbySubtitleSync] ASSRT 处于限流冷却期，跳过")
            return False, None
        headers = {"Accept": "application/json", "Authorization": f"Bearer {self._assrt_token}"}
        client = AsyncRequestUtils(headers=headers, proxies=settings.PROXY or {})
        queries: list[str] = []
        for q in (ctx["name"], ctx["original"]):
            q = (q or "").strip()
            if len(q) >= 2 and q not in queries:
                queries.append(q)
        # 两轮查询的候选汇总后统一打分，避免中文查询先命中弱相关结果就提前收工
        pool: dict[str, dict] = {}
        rejected_mismatch = 0
        for query in queries:
            await self._assrt_search_gate()
            resp = await client.get_res(f"{self._ASSRT_BASE}/sub/search",
                                        params={"q": query, "cnt": 15, "pos": 0})
            if resp and resp.status_code == 509:
                self._assrt_trip_cooldown("HTTP 509")
                return False, None
            if not resp or resp.status_code != 200:
                logger.warning(f"[EmbySubtitleSync] ASSRT 搜索失败 HTTP {resp.status_code if resp else 'N/A'}: {query}")
                continue
            try:
                payload = resp.json()
            except Exception:
                continue
            status = payload.get("status")
            if status == 30900:
                self._assrt_trip_cooldown("30900")
                return False, None
            if status != 0:
                logger.warning(f"[EmbySubtitleSync] ASSRT 返回状态 {status}: {query}")
                continue
            subs = ((payload.get("sub") or {}).get("subs")) or []
            for it in subs:
                if not isinstance(it, dict) or not it.get("id"):
                    continue
                if not self._assrt_lang_ok(it, lang):
                    continue
                text = f"{it.get('native_name') or ''} {it.get('videoname') or ''}"
                # 集号契合：整季包不再被"SxxExx 必须出现在搜索结果文本"误杀（包内再挑集）
                fit, fit_bonus = self._assrt_ep_fit(ctx, text)
                if not fit:
                    continue
                # 精准匹配：标题必须命中目标作品；候选带年份时必须与目标年份一致
                if not self._title_matches(ctx, text):
                    rejected_mismatch += 1
                    continue
                cy = self._find_year(text)
                if cy and ctx["year"] and cy != int(ctx["year"]):
                    rejected_mismatch += 1
                    continue
                score = self._to_float(it.get("vote_score")) * 10 + self._spec_bonus(ctx, text) + fit_bonus
                if cy and ctx["year"] and cy == int(ctx["year"]):
                    score += 20
                it["_match_score"] = score
                pool[str(it["id"])] = it
        if not pool:
            logger.info(f"[EmbySubtitleSync] ASSRT 无合适字幕（标题/年份不匹配过滤 {rejected_mismatch} 条）")
            return False, None
        # 机翻靠后；同档内中英双语优先（v2.5.0），其余按综合分（站点评分+年份+分辨率/版本匹配）降序
        cands = sorted(pool.values(),
                       key=lambda it: (1 if it.get("vote_machine_translate") else 0,
                                       0 if self._assrt_bilingual(it) else 1,
                                       -self._to_float(it.get("_match_score"))))
        best = cands[0]
        name = str(best.get("native_name") or best.get("videoname") or best["id"])
        dresp = await client.get_res(f"{self._ASSRT_BASE}/sub/detail", params={"id": best["id"]})
        if not dresp or dresp.status_code != 200:
            logger.warning("[EmbySubtitleSync] ASSRT 详情请求失败")
            return False, None
        try:
            dpayload = dresp.json()
        except Exception:
            return False, None
        dsubs = ((dpayload.get("sub") or {}).get("subs")) or []
        detail = next((d for d in dsubs if str(d.get("id")) == str(best["id"])),
                      dsubs[0] if dsubs else None)
        url = (detail or {}).get("url")
        if not url:
            logger.warning("[EmbySubtitleSync] ASSRT 详情缺少下载链接")
            return False, None
        file_name = Path(str((detail or {}).get("filename") or f"assrt-{best['id']}.zip")).name
        work_dir = Path(self.get_data_path()) / "downloads" / uuid4().hex
        work_dir.mkdir(parents=True, exist_ok=True)
        try:
            await self._assrt_download_gate()
            dl = AsyncRequestUtils(proxies=settings.PROXY or {})
            fres = await dl.get_res(url)
            if not fres or fres.status_code != 200 or not fres.content:
                logger.warning("[EmbySubtitleSync] ASSRT 文件下载失败")
                return False, None
            tmp = work_dir / file_name
            tmp.write_bytes(fres.content)
            if self._place_subtitle(tmp, work_dir, video_path, lang, tv=tv):
                logger.info(f"[EmbySubtitleSync] ASSRT 字幕补齐: {name}")
                return True, f"[ASSRT] {name}"
            return False, None
        finally:
            import shutil
            shutil.rmtree(work_dir, ignore_errors=True)
        return False, None

    # ---------------- OpenSubtitles ----------------

    def _os_headers(self, auth: bool = False) -> dict:
        headers = {
            "Accept": "application/json",
            "Content-Type": "application/json",
            "Api-Key": self._os_api_key,
            "User-Agent": self._OS_UA,
        }
        if auth and self._os_jwt:
            headers["Authorization"] = f"Bearer {self._os_jwt}"
        return headers

    async def _os_login(self) -> bool:
        """登录 OpenSubtitles 换取下载 JWT（缓存在内存，失效时重登）。"""
        client = AsyncRequestUtils(headers=self._os_headers(), proxies=settings.PROXY or {})
        resp = await client.post_res(
            "https://api.opensubtitles.com/api/v1/login",
            json={"username": self._os_username, "pass" + "word": self._os_password},
        )
        if not resp or resp.status_code != 200:
            logger.warning(f"[EmbySubtitleSync] OpenSubtitles 登录失败 HTTP {resp.status_code if resp else 'N/A'}")
            return False
        try:
            payload = resp.json()
        except Exception:
            return False
        token = payload.get("token")
        if not token:
            logger.warning("[EmbySubtitleSync] OpenSubtitles 登录响应缺少 token")
            return False
        self._os_jwt = token
        base = payload.get("base_url")
        if isinstance(base, str) and base.strip():
            b = base.strip().rstrip("/")
            self._os_base_url = b if b.endswith("/api/v1") else f"{b}/api/v1"
        return True

    async def _os_download_link(self, file_id: int) -> tuple[str | None, str | None]:
        """用 JWT 换取一次性下载链接；401/403 时清 JWT 以便上层重登重试。"""
        client = AsyncRequestUtils(headers=self._os_headers(auth=True), proxies=settings.PROXY or {})
        resp = await client.post_res(f"{self._os_base_url}/download", json={"file_id": int(file_id)})
        if not resp or resp.status_code != 200:
            if resp and resp.status_code in (401, 403):
                self._os_jwt = None
            logger.warning(f"[EmbySubtitleSync] OpenSubtitles 下载授权失败 HTTP {resp.status_code if resp else 'N/A'}")
            return None, None
        try:
            payload = resp.json()
        except Exception:
            return None, None
        if payload.get("remaining") is not None:
            logger.info(f"[EmbySubtitleSync] OpenSubtitles 今日剩余下载额度: {payload.get('remaining')}")
        return payload.get("link"), payload.get("file_name")

    async def _os_fetch(self, ctx: dict, video_path: str, lang: str,
                        tv: dict | None = None) -> tuple[bool, str | None]:
        lang_code = "zh-cn" if lang == "简体中文" else "zh-tw"
        client = AsyncRequestUtils(headers=self._os_headers(), proxies=settings.PROXY or {})
        common = {"languages": lang_code, "type": "episode" if ctx["is_tv"] else "movie"}
        attempts: list[tuple[str, dict]] = []
        # 1) 优先按媒体 ID 搜索
        imdb_int = None
        if ctx["imdb"]:
            digits = str(ctx["imdb"]).lower().removeprefix("tt")
            if digits.isdigit():
                imdb_int = int(digits)
        tmdb_int = self._to_int(ctx["tmdb"])
        idp = dict(common)
        if ctx["is_tv"]:
            if imdb_int:
                idp["parent_imdb_id"] = imdb_int
            elif tmdb_int:
                idp["parent_tmdb_id"] = tmdb_int
            if ctx["season"] is not None:
                idp["season_number"] = int(ctx["season"])
        else:
            if imdb_int:
                idp["imdb_id"] = imdb_int
            elif tmdb_int:
                idp["tmdb_id"] = tmdb_int
        if len(idp) > len(common):
            attempts.append(("id", idp))
        # 2) 英文标题 + 年份搜索
        if ctx["original"]:
            tp = dict(common)
            tp["query"] = ctx["original"]
            if ctx["year"]:
                tp["year"] = int(ctx["year"])
            if ctx["is_tv"] and ctx["season"] is not None:
                tp["season_number"] = int(ctx["season"])
            attempts.append(("title", tp))
        ep_tag = None
        if ctx["is_tv"] and ctx["season"] is not None and ctx["episode"] is not None:
            ep_tag = f"s{int(ctx['season']):02d}e{int(ctx['episode']):02d}"
        for kind, params in attempts:
            resp = await client.get_res(f"{self._os_base_url}/subtitles", params=params)
            if not resp or resp.status_code != 200:
                logger.warning(f"[EmbySubtitleSync] OpenSubtitles 搜索失败 HTTP {resp.status_code if resp else 'N/A'}")
                continue
            try:
                payload = resp.json()
            except Exception:
                continue
            cands = []
            for entry in payload.get("data") or []:
                attrs = entry.get("attributes") or {}
                feature = attrs.get("feature_details") or {}
                ep_ok = True
                if ctx["is_tv"]:
                    fep = self._to_int(feature.get("episode_number"))
                    ep_ok = fep is not None and ctx["episode"] is not None and fep == int(ctx["episode"])
                machine = bool(attrs.get("ai_translated") or attrs.get("machine_translated"))
                for f in attrs.get("files") or []:
                    fid = f.get("file_id")
                    fname = str(f.get("file_name") or "")
                    if not fid:
                        continue
                    # 剧集：feature 无单集信息时（季包等），靠文件名 SxxExx 兜底匹配
                    if ctx["is_tv"] and not ep_ok and ep_tag and ep_tag not in fname.lower():
                        continue
                    if ctx["is_tv"] and not ep_ok and not ep_tag:
                        continue
                    cands.append({
                        "file_id": fid,
                        "file_name": fname,
                        "release": str(attrs.get("release") or fname),
                        "machine": machine,
                        "bilingual": self._is_bilingual_text(
                            str(attrs.get("release") or ""), fname),
                        "downloads": self._to_float(attrs.get("download_count")),
                        "rating": self._to_float(attrs.get("ratings")),
                        "ftitle": str(feature.get("title") or ""),
                        "fyear": self._to_int(feature.get("year")),
                    })
            if kind == "title" and cands:
                # 标题搜索结果做精准校验：年份冲突直接弃，标题对不上目标作品也弃
                kept = []
                for c in cands:
                    if c["fyear"] and ctx["year"] and c["fyear"] != int(ctx["year"]):
                        continue
                    if c["ftitle"] and not self._title_matches(ctx, f"{c['ftitle']} {c['release']}"):
                        continue
                    kept.append(c)
                cands = kept
            if not cands:
                logger.info("[EmbySubtitleSync] OpenSubtitles 无合适字幕")
                continue
            # 机翻靠后；同档内中英双语优先（v2.5.0），再优先分辨率/版本匹配、下载量、评分
            cands.sort(key=lambda c: (1 if c["machine"] else 0,
                                      0 if c["bilingual"] else 1,
                                      -self._spec_bonus(ctx, f"{c['release']} {c['file_name']}"),
                                      -c["downloads"], -c["rating"]))
            best = cands[0]
            if not self._os_jwt and not await self._os_login():
                return False, None
            link, dl_name = await self._os_download_link(best["file_id"])
            if not link and not self._os_jwt and await self._os_login():
                link, dl_name = await self._os_download_link(best["file_id"])
            if not link:
                return False, None
            file_name = Path(str(dl_name or best["file_name"] or f"{best['file_id']}.srt")).name
            work_dir = Path(self.get_data_path()) / "downloads" / uuid4().hex
            work_dir.mkdir(parents=True, exist_ok=True)
            try:
                dl = AsyncRequestUtils(proxies=settings.PROXY or {})
                fres = await dl.get_res(link)
                if not fres or fres.status_code != 200 or not fres.content:
                    logger.warning("[EmbySubtitleSync] OpenSubtitles 文件下载失败")
                    return False, None
                tmp = work_dir / file_name
                tmp.write_bytes(fres.content)
                if self._place_subtitle(tmp, work_dir, video_path, lang, tv=tv):
                    logger.info(f"[EmbySubtitleSync] OpenSubtitles 字幕补齐: {best['release']}")
                    return True, f"[OpenSubtitles] {best['release']}"
                return False, None
            finally:
                import shutil
                shutil.rmtree(work_dir, ignore_errors=True)
        return False, None

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
                    {
                        "component": "VRow",
                        "content": [
                            self._col(3, "VSwitch", {"model": "assrt_enabled", "label": "启用 ASSRT（射手网）兜底"}),
                            self._col(9, "VTextField", {
                                "model": "assrt_token",
                                "label": "ASSRT Token",
                                "type": "password",
                                "placeholder": "在 assrt.net 登录后于个人中心获取 API Token；站点搜索无果时用此源兜底",
                            }),
                        ],
                    },
                    {
                        "component": "VRow",
                        "content": [
                            self._col(3, "VSwitch", {"model": "opensubtitles_enabled", "label": "启用 OpenSubtitles 兜底"}),
                            self._col(3, "VTextField", {
                                "model": "os_api_key",
                                "label": "OpenSubtitles API Key",
                                "type": "password",
                                "placeholder": "opensubtitles.com 开发者页创建应用获取",
                            }),
                            self._col(3, "VTextField", {"model": "os_username", "label": "OpenSubtitles 用户名", "placeholder": "账号用户名"}),
                            self._col(3, "VTextField", {
                                "model": "os_password",
                                "label": "OpenSubtitles 密码",
                                "type": "password",
                                "placeholder": "账号密码（下载需登录，免费账号有每日额度）",
                            }),
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
            "assrt_enabled": False,
            "assrt_token": "",
            "opensubtitles_enabled": False,
            "os_api_key": "",
            "os_username": "",
            "os_password": "",
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
                                    # MP 前端 PageRender 只渲染组件对象同级的 text 字段；
                                    # 写进 props 的 text 只有 VAlert 等自带 text prop 的组件能显示，
                                    # 普通 div 必须把 text 放在同级（v2.5.1 修复记录条目空白）
                                    "component": "div",
                                    "props": {
                                        "class": "font-weight-bold "
                                                 + ("text-success" if success else "text-error"),
                                    },
                                    "text": f"{'✓' if success else '✗'} {entry.get('title', '')}"
                                            f"{' (' + str(entry.get('year')) + ')' if entry.get('year') else ''}"
                                            f" [{entry.get('type', '')}]",
                                },
                                {
                                    "component": "div",
                                    "props": {
                                        "class": "text-caption text-medium-emphasis",
                                    },
                                    "text": f"{entry.get('time', '')}｜补齐{entry.get('lang', '')}｜"
                                            f"{entry.get('sub_name', '') or '未找到合适字幕'}",
                                },
                            ],
                        }
                    ],
                }
            )
        return page
