"""
入库自动订阅插件 (MoviePilot V3)

监听 transfer.complete（整理完成）事件：
- 仅处理剧集（MediaType.TV）
- 用 SubscribeChain.exists(mediainfo, meta) 判断该剧该季是否已订阅
- 未订阅则按入库文件的季调用 SubscribeChain.add 建订阅
"""
from typing import Any

from app.chain.subscribe import SubscribeChain
from app.core.event import eventmanager
from app.log import logger
from app.plugins import _PluginBase
from app.schemas import NotificationType
from app.schemas.types import EventType, MediaType


class AutoSubscribe(_PluginBase):
    # 插件名称
    plugin_name = "入库自动订阅"
    # 插件描述
    plugin_desc = "剧集整理入库完成后，自动按当前季创建订阅"
    # 插件图标
    plugin_icon = "subscribe.png"
    # 插件版本
    plugin_version = "1.0.0"
    # 插件作者
    plugin_author = "muse"
    # 作者主页
    author_url = ""
    # 插件配置项ID前缀
    plugin_config_prefix = "autosubscribe_"
    # 加载顺序
    plugin_order = 10
    # 可使用的用户级别
    auth_level = 1

    def __init__(self) -> None:
        super().__init__()
        self._enabled = False
        self._notify = True

    # ------------------------------------------------------------------
    # 插件生命周期
    # ------------------------------------------------------------------

    def init_plugin(self, config: dict | None = None) -> None:
        if config:
            self._enabled = config.get("enabled", False) or False
            self._notify = config.get("notify", True)
            if self._notify is None:
                self._notify = True
        self._register_events()

    def _register_events(self) -> None:
        @eventmanager.register(EventType.TransferComplete)
        def on_transfer_complete(event) -> None:
            try:
                self._handle_transfer(event)
            except Exception as e:
                logger.error(f"[AutoSubscribe] 处理整理完成事件异常: {e}")

    # ------------------------------------------------------------------
    # 事件处理
    # ------------------------------------------------------------------

    def _handle_transfer(self, event) -> None:
        if not self._enabled:
            return
        event_data = getattr(event, "event_data", None) or {}
        meta = event_data.get("meta")
        mediainfo = event_data.get("mediainfo")
        if not meta or not mediainfo:
            return
        # 仅处理剧集
        if getattr(mediainfo, "type", None) != MediaType.TV:
            return
        tmdbid = getattr(mediainfo, "tmdb_id", None)
        if not tmdbid:
            logger.info("[AutoSubscribe] 剧集缺少 TMDB ID，跳过自动订阅")
            return
        # 按入库文件的季订阅
        season = getattr(meta, "begin_season", None)
        title = getattr(mediainfo, "title", "") or ""
        year = getattr(mediainfo, "year", "") or ""
        season_str = f"S{int(season):02d}" if season else "未知季"

        logger.info(f"[AutoSubscribe] 检测到剧集入库: {title}({year}) {season_str}")

        # 是否已订阅（该剧该季）
        try:
            already = SubscribeChain.exists(mediainfo, meta)
        except Exception as e:
            logger.warning(f"[AutoSubscribe] 订阅存在性检查失败，按未订阅处理: {e}")
            already = False
        if already:
            logger.info(f"[AutoSubscribe] {title} {season_str} 已存在订阅，跳过")
            return

        # 创建订阅
        try:
            sid, msg = SubscribeChain().add(
                title=title,
                year=str(year),
                mtype=MediaType.TV,
                tmdbid=tmdbid,
                season=int(season) if season else None,
                message=False,
            )
        except Exception as e:
            logger.error(f"[AutoSubscribe] 创建订阅异常: {e}")
            return

        if sid:
            logger.info(f"[AutoSubscribe] 已自动订阅: {title} {season_str} (id={sid})")
            if self._notify:
                try:
                    self.post_message(
                        title="入库自动订阅",
                        text=f"剧集《{title}》{season_str} 首次入库，已自动创建订阅",
                        mtype=NotificationType.Plugin,
                    )
                except Exception as e:
                    logger.warning(f"[AutoSubscribe] 发送通知失败: {e}")
        else:
            logger.warning(f"[AutoSubscribe] 创建订阅失败: {title} {season_str}: {msg}")

    # ------------------------------------------------------------------
    # 插件接口
    # ------------------------------------------------------------------

    def get_state(self) -> bool:
        return self._enabled

    def get_service(self) -> list[dict[str, Any]]:
        return []

    def get_api(self) -> list[dict[str, Any]]:
        return []

    def get_form(self) -> tuple[list[dict], dict[str, Any]]:
        return [
            {
                "component": "VForm",
                "content": [
                    {
                        "component": "VRow",
                        "content": [
                            {
                                "component": "VCol",
                                "props": {"cols": 12, "md": 6},
                                "content": [
                                    {
                                        "component": "VSwitch",
                                        "props": {"model": "enabled", "label": "启用插件"},
                                    }
                                ],
                            },
                            {
                                "component": "VCol",
                                "props": {"cols": 12, "md": 6},
                                "content": [
                                    {
                                        "component": "VSwitch",
                                        "props": {"model": "notify", "label": "订阅成功后发送通知"},
                                    }
                                ],
                            },
                        ],
                    },
                    {
                        "component": "VRow",
                        "content": [
                            {
                                "component": "VCol",
                                "props": {"cols": 12},
                                "content": [
                                    {
                                        "component": "VAlert",
                                        "props": {
                                            "type": "info",
                                            "variant": "tonal",
                                            "text": "插件监听文件整理完成事件，仅处理剧集；按入库文件的季创建订阅，已订阅过的剧集/季会自动跳过，不会重复订阅。",
                                        },
                                    }
                                ],
                            },
                        ],
                    },
                ],
            }
        ], {
            "enabled": False,
            "notify": True,
        }

    def get_page(self) -> list[dict]:
        return []

    def stop_service(self) -> None:
        pass
