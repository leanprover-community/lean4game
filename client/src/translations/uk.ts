import type { DeepPartialTranslation } from '../utils/DeepPartialTranslation'
import type { en } from './en'

export const uk: DeepPartialTranslation<typeof en> = {
  errorPage: {
    title: 'Ой!',
    description: 'Сталося щось неочікуване:',
    createIssue:
      'Будь ласка, створіть issue в <issueLink>репозиторії GitHub</issueLink>.',
  },
  notFound: {
    title: 'Цю сторінку не знайдено',
    description:
      '<code>(404)</code> Сторінка <code>{{pathname}}</code>, схоже, не існує.',
    createIssue:
      'Якщо ви вважаєте, що вона має існувати, створіть issue в <issueLink>репозиторії GitHub</issueLink>.',
  },
  legal: {
    englishBelow: '(Англійська версія нижче)',
    contact: 'Контактна інформація:',
    contactDetails: 'Контактні дані',
    technicalContact: 'Технічний контакт',
    loadError: 'Не вдалося завантажити контактну інформацію.',
  },
  impressum: {
    title: 'Імпресум',
    legalForm: 'Правова форма:',
    vatId: 'Ідентифікаційний номер платника ПДВ:',
    vatIdBasis: 'згідно з §27a Закону про податок з обороту',
  },
  privacy: {
    title: 'Політика конфіденційності',
    collectedData:
      'Наш сервер збирає метадані (такі як IP-адреса, браузер, операційна система) та дані, які користувач вводить у редактор. Ці дані використовуються для обчислення результату Lean і його відображення користувачеві. Інформація зберігається протягом часу перебування користувача на нашому вебсайті й одразу після цього видаляється. Ми ведемо журнали (логи) для вдосконалення нашого програмного забезпечення, але всі дані в них анонімізовані.',
    browserStorage:
      'Ми не використовуємо файли cookie, проте ваш ігровий прогрес зберігається в браузері як дані сайту. Ваш ігровий прогрес не зберігається на сервері; якщо ви видалите дані сховища браузера, він буде повністю втрачений.',
    serverLocation: 'Розташування нашого сервера: {{location}}.',
  },
  appBar: {
    backToLanding: 'Повернутися до вибору ігор',
    back: 'Назад',
    backToGame: 'Повернутися до огляду гри',
    backToWorld: 'Повернутися до світу',
    start: 'Почати',
    home: 'Головна',
    previousLevel: 'Попередній рівень',
    next: 'Далі',
    nextLevel: 'Наступний рівень',
    gameInfo: 'Інформація про гру',
    gameInfoTitle: 'Інформація про гру та авторів',
    download: 'Скачати',
    downloadTitle: 'Скачати прогрес',
    upload: 'Завантажити',
    uploadTitle: 'Завантажити прогрес із JSON',
    erase: 'Стерти',
    eraseTitle: 'Очистити прогрес',
    impressum: 'Імпресум',
    privacy: 'Політика конфіденційності',
    preferences: 'Уподобання',
    github: 'Переглянути Lean Game Server на GitHub',
    openMenu: 'Відкрити меню',
    closeMenu: 'Закрити меню',
    openLanguageMenu: 'Відкрити меню мови',
    closeLanguageMenu: 'Закрити меню мови',
  },
  preferences: {
    title: 'Уподобання',
    language: 'Мова',
    languageNote:
      'Якщо гра не існує вибраною мовою, це налаштування не діє і використовується мова гри за замовчуванням.',
    useFlags: 'Використовувати прапори країн для представлення мов',
    layout: 'Макет',
    layouts: {
      mobile: 'Мобільний',
      auto: 'Автоматично',
      desktop: 'Десктоп',
    },
    showLockedInventory: 'Показувати заблоковані предмети інвентаря',
    theme: 'Тема',
    themes: {
      light: 'Світла',
      auto: 'Автоматично',
      dark: 'Темна',
    },
    browserStorage: 'Браузерне сховище',
    savePreferences: 'Зберегти мої налаштування (у сховищі браузера)',
  },
  layout: {
    openPanel: 'Відкрити: {{title}}',
    closePanel: 'Закрити: {{title}}',
  },
  game: {
    introduction: 'Вступ',
    conclusion: 'Висновок',
    chat: 'Чат',
    inventory: 'Інвентар',
  },
  chat: {
    nextHint: 'Наступна підказка',
  },
  inventory: {
    theorems: 'Теореми',
    tactics: 'Тактики',
    definitions: 'Визначення',
    notUnlocked: 'Ще не розблоковано',
    notAvailable: 'Недоступно на цьому рівні',
    insert: "Вставити '{{name}}'",
    close: 'Закрити',
    unlock: 'Розблокувати цей елемент!',
    furtherDetails: 'Докладніше',
    provenIn: 'Доведено в:',
    introducedIn: 'Введено в:',
    mathlibDoc: 'Документація Mathlib',
    worldLevel: '{{world}}, рівень {{level}}',
  },
  typewriter: {
    execute: 'Виконати',
    inputPlaceholder: 'Введіть тактику',
    retry: 'Повторити',
    retryTitle: 'Повторіть доказ звідси',
    cancelEdit: 'Скасувати редагування',
    failedCommand: 'Невдала команда',
    activeGoal: 'Активна ціль',
    goalN: 'Мета {{n}}',
    goal: 'Мета',
    objects: "Об'єкти",
    assumptions: 'Припущення',
    theorem: 'Теорема',
    levelCompleted: 'Рівень пройдено! 🎉',
    levelSolved: 'Рівень уже було успішно пройдено',
    noGoalsLeft: 'цілей не залишилося',
    noGoalsLeftDescription:
      'Ймовірно, це означає, що ви пройшли рівень із попередженнями або Lean натрапив на помилку синтаксичного аналізу.',
    startError: 'Не вдалося запустити сервер Lean:',
    checkError: 'Не вдалося перевірити доказ:',
  },
  popup: {
    close: 'Закрити',
  },
  gameInfo: {
    progressSaving: {
      title: 'Збереження прогресу',
      description:
        'Гра зберігає ваш прогрес у локальному сховищі браузера. Якщо ви видалите ці дані, прогрес буде втрачено!<br/>Попередження: у більшості браузерів видалення файлів cookie також призводить до очищення локального сховища (або «локальних даних сайту»). Обов’язково збережіть (завантажте) свій ігровий прогрес перед цим!',
    },
    accessibility: {
      title: 'Доступність',
      description:
        'Якщо у вас виникли будь-які перешкоди з доступністю, зв’яжіться з нами! Ми докладаємо всіх зусиль, щоб усунути такі перешкоди.',
    },
    development: {
      title: 'Розробка',
      description:
        'Ігровий рушій розробили <strong>Александер Бенткамп</strong> і <strong>Йон Ойгстер</strong> під керівництвом <strong>Маркуса Цібровіуса</strong>. Вихідний код цього ігрового рушія на базі Lean <githubLink>доступний на GitHub</githubLink>. Якщо ви зіткнетеся з будь-якими проблемами, будь ласка, створіть <issueLink>запит (Issue) на GitHub</issueLink> або зв’яжіться з нами безпосередньо.',
    },
    funding: {
      title: 'Фінансування',
      description:
        'Цей сервер розміщено в Heinrich Heine University Düsseldorf. Програмне забезпечення lean4game було розроблено як частина проєкту <adamLink>ADAM: Anticipating the Digital Age of Mathematics</adamLink>, профінансованого програмою <i>Freiraum 2022</i> від <i>Stiftung Innovation in der Hochschullehre</i>. Поточна підтримка та розробка щедро підтримуються <i>Renaissance Philanthropy</i> через <i>AI for Math Fund</i>.',
    },
  },
  progress: {
    eraseTitle: 'Видалити прогрес?',
    eraseQuestion: 'Ви хочете безповоротно видалити збережений прогрес?',
    deleteLevel: 'Видалити цей рівень',
    deleteWorld: 'Видалити цей світ',
    deleteAll: 'Видалити все',
    deleteAllWarning:
      '<p>Видалення всього видалить усі ваші докази та зібраний інвентар! Рекомендується спочатку скачати прогрес.</p><p>(Збереження з інших ігор не видаляються.)</p>',
    downloadAndDeleteAll: 'Скачати та видалити все',
    cancel: 'Скасувати',
    uploadTitle: 'Завантажити збережений прогрес',
    uploadDescription:
      '<p>Виберіть файл JSON із збереженим прогресом гри, щоб завантажити ваш прогрес.</p><p><strong>Увага:</strong> Це видалить ваш поточний прогрес у грі! Спершу <downloadLink>скачайте свій поточний прогрес</downloadLink>!</p>',
    selectFile: 'Файл прогресу',
    invalidFile: 'Це недійсний файл прогресу: {{error}}',
    load: 'Завантажити вибраний файл',
  },
  rules: {
    gameRules: 'Правила гри',
    levels: 'рівні',
    tactics: 'тактики',
    locked: 'заблоковано',
    unlocked: 'розблоковано',
    none: 'без правил',
    relaxed: 'послаблений',
    regular: 'звичайний',
    help: '<p>Правила гри визначають, чи можна пропускати рівні та чи перевіряються ігри, щоб дозволити лише розблоковані тактики та теореми в доказах.</p><p>Примітка. "Розблоковані" тактики (або теореми) визначаються двома речами: набором мінімальних тактик, необхідних для проходження рівня, плюс будь-які тактики, які ви розблокували на іншому рівні. Це означає, що якщо ви розблокуєте <code>simp</code> на рівні, ви зможете використовувати його на будь-якому рівні.</p>',
  },
  landing: {
    title: 'Ігровий сервер Lean',
    subtitle:
      'Репозиторій навчальних ігор для помічника з доказів <leanLink>Lean</leanLink> <i>(Lean 4)</i> і його математичної бібліотеки <mathlibLink>mathlib</mathlibLink>',
    games: {
      loading: 'Завантаження ігор…',
      error: 'Не вдалося завантажити ігри.',
      none: 'Немає доступних ігор.',
      noneDev:
        'Локальні ігри — це папки поруч із цим репозиторієм, які містять зібрану гру, тобто файл `.lake/gamedata/game.json`.',
    },
    tile: {
      prerequisites: 'Передумови',
      prerequisitesTitle: 'Радимо спершу пройти ці ігри.',
      worlds: 'Світи',
      levels: 'Рівні',
      languages: 'Мови',
    },
    capacity: {
      title: 'Потужність сервера',
      description:
        'Оскільки цей сервер запускає Lean на машинах нашого університету, він має обмежену потужність. Ми оцінюємо, що наша конфігурація буде підтримувати близько 50 одночасних ігор з високою продуктивністю і до 180 одночасних ігор з меншою швидкістю.',
      players: 'Активні гравці: <strong>{{count}}</strong>',
      memory: 'ОЗП: <strong>{{value}} %</strong> використовується.',
      cpu: 'ЦПУ: <strong>{{value}} %</strong> використовується.',
    },
    development: {
      title: 'Нотатки щодо розробки',
      description:
        'Більшість аспектів ігор та інфраструктури все ще знаходяться в розробці. Не соромтеся надсилати <issueLink>GitHub issue</issueLink> про будь-які проблеми, які виникають!',
    },
    newGames: {
      title: 'Додавання нових ігор',
      template:
        'Якщо ви плануєте написати власну гру, вам слід використовувати <skeletonLink>репозиторій GameSkeleton на GitHub</skeletonLink> як шаблон і прочитати <docsLink>Як створити гру</docsLink>, де також пояснюється, як завантажити гру на сервер і грати в неї. Якщо у вас виникнуть запитання, зв’яжіться з нами.',
      featured:
        'Рекомендовані ігри на цій сторінці додаються вручну. Зв’яжіться з нами, і ми з радістю додамо ваші.',
    },
    funding: {
      title: 'Фінансування',
      description:
        'Цей сервер розміщено в Heinrich Heine University Düsseldorf. Програмне забезпечення lean4game було розроблено як частина проєкту <adamLink>ADAM: Anticipating the Digital Age of Mathematics</adamLink>, профінансованого програмою <i>Freiraum 2022</i> від <i>Stiftung Innovation in der Hochschullehre</i>. Поточна підтримка та розробка щедро підтримуються <i>Renaissance Philanthropy</i> через <i>AI for Math Fund</i>.',
    },
  },
} as const
