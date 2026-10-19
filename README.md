# MoviePilot V3 第三方插件仓库

本仓库为 MoviePilot V3 的第三方插件仓库，包含以下插件：

## 插件列表

### 1. Emby存量字幕补齐（`EmbySubtitleSync`）
直连 Emby 扫描存量外语电影和剧集，检查内封及外挂中文字幕，缺失时调用 MoviePilot
核心字幕搜索（与 AutoSubtitle 相同的字幕来源）补齐中文字幕。

- 源码：`plugins.v3/embysubtitlesync/__init__.py`
- 配置：Emby 地址、API Key、媒体库筛选、路径映射、定时 cron

### 2. 入库自动订阅（`AutoSubscribe`）
监听文件整理完成（`transfer.complete`）事件，剧集入库整理完成后自动按当前季创建订阅。

- 源码：`plugins.v3/autosubscribe/__init__.py`
- 行为：
  - 仅处理剧集，电影不受影响
  - 按入库文件的季创建订阅（如入库 S02E01 则订阅 S02）
  - 已订阅过的剧集/季自动跳过，不会重复订阅
  - 手动补入库的老剧如从未订阅过，也会被自动订阅
- 配置：启用开关、订阅成功通知

## 安装方法

1. 在 MoviePilot 管理界面进入「插件」
2. 添加第三方插件仓库，粘贴本仓库地址：
   `https://github.com/dianzhaobao/moviepilot-plugins`
3. 在插件列表中找到需要的插件，安装并启用
4. 按插件说明完成配置（Emby 地址/API Key 等）

## 目录结构

```text
package.v3.json                        # V3 插件市场索引
plugins.v3/
  embysubtitlesync/__init__.py         # Emby存量字幕补齐
  autosubscribe/__init__.py            # 入库自动订阅
```
