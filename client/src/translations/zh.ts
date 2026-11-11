import type { DeepPartialTranslation } from '../utils/DeepPartialTranslation'
import type { en } from './en'

export const zh: DeepPartialTranslation<typeof en> = {
  errorPage: {
    title: '糟糕！',
    description: '发生了意外情况：',
    createIssue: '请在 <issueLink>GitHub 仓库</issueLink> 上提交 issue。',
  },
  notFound: {
    title: '找不到此页面',
    description:
      '<code>(404)</code> 页面 <code>{{pathname}}</code> 似乎不存在。',
    createIssue:
      '如果你认为它应该存在，请在 <issueLink>GitHub 仓库</issueLink> 上提交 issue。',
  },
  legal: {
    englishBelow: '（英文版见下方）',
    contact: '联系方式：',
    contactDetails: '详细联系方式',
    technicalContact: '技术联系人',
    loadError: '无法加载联系信息。',
  },
  impressum: {
    title: '版权声明',
    legalForm: '法律形式：',
    vatId: '增值税识别号：',
    vatIdBasis: '依据德国增值税法第 27a 条',
  },
  privacy: {
    title: '隐私政策',
    collectedData:
      '我们的服务器会收集元数据（例如 IP 地址、浏览器、操作系统）以及用户在编辑器中输入的数据。这些数据用于计算 Lean 的输出并显示给用户。这些信息仅在用户停留在我们网站期间保存，之后会立即删除。我们保留日志以改进软件，但其中的数据已匿名化。',
    browserStorage:
      '我们不使用 Cookie，但你的游戏进度会作为网站数据保存在浏览器中。你的游戏进度不会保存在服务器上；如果你删除浏览器存储，进度将彻底丢失。',
    serverLocation: '服务器所在地：{{location}}。',
  },
  appBar: {
    backToLanding: '返回游戏选择',
    back: '返回',
    backToGame: '返回游戏概览',
    backToWorld: '返回世界',
    start: '开始',
    home: '首页',
    previousLevel: '上一关',
    next: '下一关',
    nextLevel: '下一关',
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
    github: '在 GitHub 上查看 Lean 游戏服务器',
    openMenu: '打开菜单',
    closeMenu: '关闭菜单',
    openLanguageMenu: '打开语言菜单',
    closeLanguageMenu: '关闭语言菜单',
  },
  preferences: {
    title: '偏好设置',
    language: '语言',
    languageNote:
      '如果游戏没有所选语言的版本，此设置不起作用，将使用游戏的默认语言。',
    useFlags: '使用国旗表示语言',
    layout: '布局',
    layouts: {
      mobile: '移动端',
      auto: '自动',
      desktop: '桌面端',
    },
    showLockedInventory: '显示定理清单中已锁定的项目',
    theme: '主题',
    themes: {
      light: '浅色',
      auto: '自动',
      dark: '深色',
    },
    browserStorage: '浏览器存储',
    savePreferences: '保存我的设置（在浏览器中存储）',
  },
  layout: {
    openPanel: '打开{{title}}',
    closePanel: '关闭{{title}}',
  },
  game: {
    introduction: '介绍',
    conclusion: '总结',
    chat: '聊天',
    inventory: '定理清单',
  },
  chat: {
    nextHint: '下一条提示',
  },
  inventory: {
    theorems: '定理',
    tactics: '策略',
    definitions: '定义',
    notUnlocked: '尚未解锁',
    notAvailable: '本关卡不提供',
    insert: "插入 '{{name}}'",
    close: '关闭',
    unlock: '解锁此项目！',
    furtherDetails: '更多详情',
    provenIn: '证明于：',
    introducedIn: '引入于：',
    mathlibDoc: 'Mathlib 文档',
    worldLevel: '{{world}} 第 {{level}} 关',
  },
  typewriter: {
    execute: '执行',
    inputPlaceholder: '输入策略',
    retry: '重试',
    retryTitle: '从这里重新尝试证明',
    cancelEdit: '取消编辑',
    failedCommand: '命令失败',
    activeGoal: '当前目标',
    goalN: '目标 {{n}}',
    goal: '目标',
    objects: '对象',
    assumptions: '假设',
    theorem: '定理',
    levelCompleted: '关卡完成！🎉',
    levelSolved: '此关卡已成功解决过',
    noGoalsLeft: '没有剩余目标',
    noGoalsLeftDescription:
      '这可能意味着你在带有警告的情况下完成了关卡，或者 Lean 遇到了解析错误。',
    startError: '无法启动 Lean 服务器：',
    checkError: '无法检查证明：',
  },
  popup: {
    close: '关闭',
  },
  gameInfo: {
    progressSaving: {
      title: '进度保存',
      description:
        '游戏会将你的进度保存在浏览器的本地存储中。如果你删除它，进度将会丢失！<br/>警告：在大多数浏览器中，删除 Cookie 也会清除本地存储（或“本地网站数据”）。请务必先下载你的游戏进度！',
    },
    accessibility: {
      title: '无障碍',
      description:
        '如果你遇到任何无障碍方面的困难，请与我们联系！我们将尽最大努力解决这些问题。',
    },
    development: {
      title: '开发',
      description:
        '游戏引擎由 <strong>Alexander Bentkamp</strong>、<strong>Jon Eugster</strong> 在 <strong>Markus Zibrowius</strong> 的领导下创建。此 Lean 游戏引擎的源代码<githubLink>可在 GitHub 上获取</githubLink>。如果你遇到任何问题，请<issueLink>在 GitHub 上提交 issue</issueLink>或直接与我们联系。',
    },
    funding: {
      title: '资助',
      description:
        '本服务器托管于杜塞尔多夫海因里希·海涅大学。leangame 软件是 <adamLink>ADAM: Anticipating the Digital Age of Mathematics</adamLink> 项目的一部分，该项目由 <i>Stiftung Innovation in der Hochschullehre</i> 的 <i>Freiraum 2022</i> 计划资助。后续的维护和开发由 <i>Renaissance Philanthropy</i> 通过 <i>AI for Math Fund</i> 慷慨支持。',
    },
  },
  progress: {
    eraseTitle: '删除进度？',
    eraseQuestion: '您确定要永久删除您的游戏进度吗？',
    deleteLevel: '删除此关卡',
    deleteWorld: '删除此世界',
    deleteAll: '全部删除',
    deleteAllWarning:
      '<p>全部删除将删除您的所有证明和收集的定理与策略！建议先下载您的进度。</p><p>（不会影响其他游戏的保存数据。）</p>',
    downloadAndDeleteAll: '下载并全部删除',
    cancel: '取消',
    uploadTitle: '上传保存的进度',
    uploadDescription:
      '<p>选择一个包含已保存游戏进度的 JSON 文件来加载您的进度。</p><p><strong>警告：</strong>这将删除您当前的游戏进度！请考虑先<downloadLink>下载您当前的进度</downloadLink>！</p>',
    selectFile: '进度文件',
    invalidFile: '这不是有效的进度文件：{{error}}',
    load: '加载所选文件',
  },
  rules: {
    gameRules: '游戏规则',
    levels: '关卡',
    tactics: '策略',
    locked: '已锁定',
    unlocked: '已解锁',
    none: '自由',
    relaxed: '休闲',
    regular: '标准',
    help: '<p>游戏规则决定是否允许跳过关卡，以及游戏是否只允许在证明中使用已解锁的策略和定理。</p><p>注意：“解锁”的策略（或定理）由两个因素决定：解决关卡所需的最小策略集合，加上你在其他关卡中解锁的任何策略。这意味着，如果你在某个关卡中解锁了<code>simp</code>，你可以在任何关卡中使用它。</p>',
  },
  landing: {
    title: 'Lean 游戏服务器',
    subtitle:
      '这是一个为证明助手 <leanLink>Lean</leanLink> <i>(Lean 4)</i> 及其数学库 <mathlibLink>mathlib</mathlibLink> 设计的学习游戏库',
    games: {
      loading: '正在加载游戏…',
      error: '无法加载游戏。',
      none: '没有可用的游戏。',
      noneDev:
        '本地游戏是此仓库旁边包含已构建游戏（即 `.lake/gamedata/game.json`）的文件夹。',
    },
    tile: {
      prerequisites: '前置条件',
      prerequisitesTitle: '建议先玩这些游戏。',
      worlds: '世界',
      levels: '关卡',
      languages: '语言',
    },
    capacity: {
      title: '服务器容量',
      description:
        '由于此服务器在我们大学的机器上运行 Lean，其容量有限。我们估计当前配置可以高性能支持约 50 个同时进行的游戏，以较慢的速度最多支持 180 个。',
      players: '活跃玩家：<strong>{{count}}</strong>',
      memory: 'RAM：已使用 <strong>{{value}} %</strong>。',
      cpu: 'CPU：已使用 <strong>{{value}} %</strong>。',
    },
    development: {
      title: '开发笔记',
      description:
        '游戏和基础设施的大部分内容仍在开发中。如果遇到任何问题，欢迎提交 <issueLink>GitHub Issue</issueLink>！',
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
      description:
        '本服务器托管于杜塞尔多夫海因里希·海涅大学。leangame 软件是 <adamLink>ADAM: Anticipating the Digital Age of Mathematics</adamLink> 项目的一部分，该项目由 <i>Stiftung Innovation in der Hochschullehre</i> 的 <i>Freiraum 2022</i> 计划资助。后续的维护和开发由 <i>Renaissance Philanthropy</i> 通过 <i>AI for Math Fund</i> 慷慨支持。',
    },
  },
} as const
