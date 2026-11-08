import type { DeepPartialTranslation } from '../utils/DeepPartialTranslation'
import type { en } from './en'

export const zh: DeepPartialTranslation<typeof en> = {
  impressum: {
    title: '版权声明',
  },
  privacy: {
    title: '隐私政策',
  },
  appBar: {
    backToLanding: '返回游戏选择',
    start: '开始',
    home: '首页',
    previous: '上一关',
    previousLevel: '上一关',
    next: '下一关',
    nextLevel: '下一关',
    editorMode: '编辑器模式',
    typewriterMode: '打字机模式',
    showInventory: '打开定理清单面板',
    gameInfo: '游戏信息',
    gameInfoTitle: '游戏信息和致谢',
    download: '下载',
    downloadTitle: '下载进度',
    upload: '上传',
    uploadTitle: '从 JSON 加载进度',
    erase: '删除',
    eraseTitle: '清除进度',
    impressum: '版权声明',
    privacy: '隐私政策',
    preferences: '偏好设置',
  },
  preferences: {
    title: '偏好设置',
    language: '语言',
    layout: '布局',
    layouts: {
      mobile: '移动端',
      auto: '自动',
      desktop: '桌面端',
    },
    savePreferences: '保存我的设置（在浏览器中存储）',
  },
  game: {
    introduction: '介绍',
    inventory: '定理清单',
    worlds: '世界',
  },
  chat: {
    nextHint: '显示更多帮助！',
  },
  inventory: {
    theorems: '定理',
    tactics: '策略',
    definitions: '定义',
    notUnlocked: '尚未解锁',
    notAvailable: '本关卡不提供',
  },
  typewriter: {
    execute: '执行',
    retry: '重试',
    retryTitle: '从这里重新尝试证明',
    failedCommand: '命令失败',
    activeGoal: '当前目标',
    goal: '目标',
    objects: '对象',
    assumptions: '假设',
    levelCompleted: '关卡完成！🎉',
  },
  gameInfo: {
    funding: {
      title: '资助',
    },
  },
  progress: {
    eraseTitle: '删除进度？',
    eraseQuestion: '您确定要永久删除您的游戏进度吗？',
    cancel: '取消',
    uploadTitle: '上传保存的进度',
    uploadDescription:
      '<p>选择一个包含已保存游戏进度的 JSON 文件来加载您的进度。</p><p><strong>警告：</strong>这将删除您当前的游戏进度！请考虑先<downloadLink>下载您当前的进度</downloadLink>！</p>',
    load: '加载所选文件',
  },
  rules: {
    rules: '规则',
    gameRules: '游戏规则',
    levels: '关卡',
    tactics: '策略',
    none: '自由',
    relaxed: '休闲',
    regular: '标准',
    help: '<p>游戏规则决定是否允许跳过关卡，以及游戏是否只允许在证明中使用已解锁的策略和定理。</p><p>注意：“解锁”的策略（或定理）由两个因素决定：解决关卡所需的最小策略集合，加上你在其他关卡中解锁的任何策略。这意味着，如果你在某个关卡中解锁了<code>simp</code>，你可以在任何关卡中使用它。</p>',
  },
  landing: {
    title: 'Lean 游戏服务器',
    subtitle:
      '这是一个为证明助手 <leanLink>Lean</leanLink> <i>(Lean 4)</i> 及其数学库 <mathlibLink>mathlib</mathlibLink> 设计的学习游戏库',
    tile: {
      prerequisites: '前置条件',
      worlds: '世界',
      levels: '关卡',
    },
    development: {
      title: '开发笔记',
    },
    newGames: {
      title: '添加新游戏',
      template:
        '如果你打算编写自己的游戏，可以使用 <skeletonLink>GameSkeleton GitHub Repo</skeletonLink> 作为模板，并参阅 <docsLink>如何创建游戏</docsLink>，其中也详细介绍了如何将游戏加载到服务器并进行游戏。如果你有任何疑问，请随时联系我们。',
      featured:
        '本页上的精选游戏都是手动添加的。如果你想添加你的游戏，请与我们联系，我们非常欢迎。',
    },
    funding: {
      title: '资助',
    },
  },
} as const
