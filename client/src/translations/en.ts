export const en = {
  errorPage: {
    title: 'Oops!',
    description: 'Something unexpected happened:',
    createIssue:
      'Please create an issue at the <issueLink>GitHub repository</issueLink>.',
  },
  notFound: {
    title: 'This page could not be found',
    description:
      '<code>(404)</code> page <code>{{pathname}}</code> seems not to exist.',
    createIssue:
      'If you believe it should, please create an issue at the <issueLink>GitHub repository</issueLink>.',
  },
  legal: {
    englishBelow: '(English version below)',
    contact: 'Contact:',
    contactDetails: 'Contact Details',
    technicalContact: 'Technical Contact',
    loadError: 'The contact information could not be loaded.',
  },
  impressum: {
    title: 'Impressum',
    legalForm: 'Legal form:',
    vatId: 'VAT identification number:',
    vatIdBasis: 'according to §27a Sales Tax Act',
  },
  privacy: {
    title: 'Privacy Policy',
    collectedData:
      'Our server collects metadata (such as IP address, browser, operating system) and the data that the user enters into the editor. The data is used to compute the Lean output and display it to the user. The information will be stored as long as the user stays on our website and will be deleted immediately afterwards. We keep logs to improve our software, but the contained data is anonymized.',
    browserStorage:
      'We do not use cookies, but your game progress is stored in the browser as site data. Your game progress is not saved on the server; if you delete your browser storage, it is completely gone.',
    serverLocation: 'Our server is located in {{location}}.',
  },
  appBar: {
    backToLanding: 'Back to games selection',
    back: 'Back',
    backToGame: 'Back to the game overview',
    backToWorld: 'Back to the world',
    start: 'Start',
    home: 'Home',
    previousLevel: 'Previous level',
    next: 'Next',
    nextLevel: 'Next level',
    gameInfo: 'Game Info',
    gameInfoTitle: 'Game Info & Credits',
    download: 'Download',
    downloadTitle: 'Download progress',
    upload: 'Upload',
    uploadTitle: 'Load progress from JSON',
    erase: 'Erase',
    eraseTitle: 'Clear progress',
    impressum: 'Impressum',
    privacy: 'Privacy Policy',
    preferences: 'Preferences',
    github: 'View the Lean Game Server on GitHub',
    openMenu: 'Open menu',
    closeMenu: 'Close menu',
    openLanguageMenu: 'Open language menu',
    closeLanguageMenu: 'Close language menu',
  },
  preferences: {
    title: 'Preferences',
    language: 'Language',
    languageNote:
      "If a game does not exist in the selected language, this setting has no effect and the game's default language is used.",
    useFlags: 'Use country flags to represent languages',
    layout: 'Layout',
    layouts: { mobile: 'Mobile', auto: 'Auto', desktop: 'Desktop' },
    showLockedInventory: 'Show locked inventory items',
    theme: 'Theme',
    themes: { light: 'Light', auto: 'Auto', dark: 'Dark' },
    browserStorage: 'Browser Storage',
    savePreferences: 'Save my settings (in the browser storage)',
  },
  import: {
    title: 'Import a game',
    description:
      'A game needs to be published as public github repo and have a running CI workflow \
      which builds the game and uploads a github artifact. Make sure your game has the \
      worklow from <skeletonLink>GameSkeleton</skeletonLink>.',
    owner: 'Github User',
    repo: 'Repository',
    start: 'Start import',
    messages: 'Server messages',
    states: {
      running: 'Importing…',
      done: 'The import has finished.',
      failed: 'The import has failed.',
    },
    invalidName: 'This is not a valid owner or repository name.',
    rateLimited:
      'This game has been imported too often. Try again in {{seconds}} s.',
    startError: 'The import could not be started: {{error}}',
    statusError: 'The status of the import could not be loaded: {{error}}',
  },
  masks: {
    select: 'Choose the interface',
    proof: 'Proof',
    checking: 'Checking the proof…',
    transcript: 'Messages',
    line: 'Line {{line}}',
    kinds: {
      error: 'Error',
      warning: 'Warning',
      information: 'Information',
      introduction: 'Introduction',
      hint: 'Hint',
      conclusion: 'Conclusion',
    },
    // the name of each mask, see `Mask`
    name_typewriter: 'Typewriter',
    name_raw: 'Raw code',
  },
  layout: {
    openPanel: 'Open {{title}}',
    closePanel: 'Close {{title}}',
  },
  game: {
    introduction: 'Introduction',
    conclusion: 'Conclusion',
    chat: 'Chat',
    inventory: 'Inventory',
  },
  chat: {
    nextHint: 'Next hint',
  },
  inventory: {
    theorems: 'Theorems',
    tactics: 'Tactics',
    definitions: 'Definitions',
    notUnlocked: 'Not unlocked yet',
    notAvailable: 'Not available in this level',
    insert: "Insert '{{name}}'",
    close: 'Close',
    unlock: 'Unlock this item!',
    furtherDetails: 'Further details',
    provenIn: 'Proven in:',
    introducedIn: 'Introduced in:',
    mathlibDoc: 'Mathlib documentation',
    worldLevel: '{{world}} level {{level}}',
  },
  typewriter: {
    execute: 'Execute',
    inputPlaceholder: 'Enter a tactic',
    retry: 'Retry',
    retryTitle: 'Retry proof from here',
    cancelEdit: 'Cancel editing',
    failedCommand: 'Failed command',
    activeGoal: 'Active Goal',
    goalN: 'Goal {{n}}',
    goal: 'Goal',
    objects: 'Objects',
    assumptions: 'Assumptions',
    theorem: 'Theorem',
    levelCompleted: 'Level completed! 🎉',
    levelSolved: 'Level has once been solved successfully',
    noGoalsLeft: 'no goals left',
    noGoalsLeftDescription:
      'This probably means you solved the level with warnings or Lean encountered a parsing error.',
    startError: 'The Lean server could not be started:',
    checkError: 'The proof could not be checked:',
  },
  popup: {
    close: 'Close',
  },
  gameInfo: {
    progressSaving: {
      title: 'Progress saving',
      description:
        'The game stores your progress in your local browser storage. If you delete it, your progress will be lost!<br/>Warning: In most browsers, deleting cookies will also clear the local storage (or "local site data"). Make sure to download your game progress first!',
    },
    accessibility: {
      title: 'Accessibility',
      description:
        'If you experience any accessibilty barriers, please get in contact with us! We are dedicated to address such barriers to the best of our abilities.',
    },
    development: {
      title: 'Development',
      description:
        'The game engine has been created by <strong>Alexander Bentkamp</strong>, <strong>Jon Eugster</strong>, under the lead of <strong>Markus Zibrowius</strong>. The source code of this Lean game engine is <githubLink>available on Github</githubLink>. If you experience any problems, please file an <issueLink>Issue on Github</issueLink> or get directly in contact.',
    },
    funding: {
      title: 'Funding',
      description:
        'This server is hosted at Heinrich Heine University Düsseldorf. The lean4game software was developed as part of the project <adamLink>ADAM: Anticipating the Digital Age of Mathematics</adamLink>, funded by the programme <i>Freiraum 2022</i> of the <i>Stiftung Innovation in der Hochschullehre</i>. Ongoing maintenance and development are generously supported by <i>Renaissance Philanthropy</i> through the <i>AI for Math Fund</i>.',
    },
  },
  progress: {
    eraseTitle: 'Delete Progress?',
    eraseQuestion: 'Do you want to delete your saved progress irreversibly?',
    deleteLevel: 'Delete this Level',
    deleteWorld: 'Delete this World',
    deleteAll: 'Delete Everything',
    deleteAllWarning:
      "<p>Deleting everything will delete all your proofs and your collected inventory! It's recommended to download your progress first.</p><p>(Saves from other games are not deleted.)</p>",
    downloadAndDeleteAll: 'Download & Delete everything',
    cancel: 'Cancel',
    uploadTitle: 'Upload Saved Progress',
    uploadDescription:
      '<p>Select a JSON file with the saved game progress to load your progress.</p><p><strong>Warning:</strong> This will delete your current game progress! Consider <downloadLink>downloading your current progress</downloadLink> first!</p>',
    selectFile: 'Progress file',
    invalidFile: 'This is not a valid progress file: {{error}}',
    load: 'Load selected file',
  },
  rules: {
    gameRules: 'Game Rules',
    levels: 'levels',
    tactics: 'tactics',
    locked: 'locked',
    unlocked: 'unlocked',
    none: 'none',
    relaxed: 'relaxed',
    regular: 'regular',
    help: '<p>Game rules determine if it is allowed to skip levels and if the games runs checks to only allow unlocked tactics and theorems in proofs.</p><p>Note: "Unlocked" tactics (or theorems) are determined by two things: The set of minimal tactics needed to solve a level, plus any tactics you unlocked in another level. That means if you unlock <code>simp</code> in a level, you can use it henceforth in any level.</p>',
  },
  landing: {
    title: 'Lean Game Server',
    subtitle:
      'A repository of learning games for the proof assistant <leanLink>Lean</leanLink> <i>(Lean 4)</i> and its mathematical library <mathlibLink>mathlib</mathlibLink>',
    games: {
      loading: 'Loading games…',
      error: 'The games could not be loaded.',
      none: 'No games available.',
      noneDev:
        'Local games are the folders next to this repository which contain a built game, i.e. a `.lake/gamedata/game.json`.',
    },
    tile: {
      prerequisites: 'Prerequisites',
      prerequisitesTitle: 'Consider playing these games first.',
      worlds: 'Worlds',
      levels: 'Levels',
      languages: 'Languages',
    },
    capacity: {
      title: 'Server capacity',
      description:
        'As this server runs Lean on our university machines, it has a limited capacity. We estimate that our setup will support around 50 simultaneous games at high performance, and up to 180 simultaneous games at a slower pace.',
      players: 'Active players: <strong>{{count}}</strong>',
      memory: 'RAM: <strong>{{value}} %</strong> used.',
      cpu: 'CPU: <strong>{{value}} %</strong> used.',
    },
    development: {
      title: 'Development notes',
      description:
        'Most aspects of the games and the infrastructure are still in development. Feel free to file a <issueLink>GitHub Issue</issueLink> about any problems you experience!',
    },
    newGames: {
      title: 'Adding new games',
      template:
        'If you are considering writing your own game, you should use the <skeletonLink>GameSkeleton GitHub Repo</skeletonLink> as a template and read <docsLink>How to Create a Game</docsLink>, which also explains how to load your game into the server and play it. We encourage you to contact us if you have any questions.',
      featured:
        "Featured games on this page are added manually. Please get in contact and we'll happily add yours.",
    },
    funding: {
      title: 'Funding',
      description:
        'This server is hosted at Heinrich Heine University Düsseldorf. The lean4game software was developed as part of the project <adamLink>ADAM: Anticipating the Digital Age of Mathematics</adamLink>, funded by the programme <i>Freiraum 2022</i> of the <i>Stiftung Innovation in der Hochschullehre</i>. Ongoing maintenance and development are generously supported by <i>Renaissance Philanthropy</i> through the <i>AI for Math Fund</i>.',
    },
  },
} as const
