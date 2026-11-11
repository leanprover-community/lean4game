import type { DeepPartialTranslation } from '../utils/DeepPartialTranslation'
import type { en } from './en'

export const de: DeepPartialTranslation<typeof en> = {
  errorPage: {
    title: 'Oops!',
    description: 'Etwas Unerwartetes ist passiert:',
    createIssue:
      'Bitte erstelle einen Issue im <issueLink>GitHub-Repository</issueLink>.',
  },
  notFound: {
    title: 'Diese Seite wurde nicht gefunden',
    description:
      '<code>(404)</code> Die Seite <code>{{pathname}}</code> scheint nicht zu existieren.',
    createIssue:
      'Falls Du denkst, dass es sie geben sollte, erstelle bitte einen Issue im <issueLink>GitHub-Repository</issueLink>.',
  },
  legal: {
    englishBelow: '(Englische Version unten)',
    contact: 'Kontakt:',
    contactDetails: 'Kontaktinformationen',
    technicalContact: 'Technischer Kontakt',
    loadError: 'Die Kontaktinformationen konnten nicht geladen werden.',
  },
  impressum: {
    title: 'Impressum',
    legalForm: 'Rechtsform:',
    vatId: 'Umsatzsteuer-Identifikationsnummer:',
    vatIdBasis: 'gemäß §27a Umsatzsteuergesetz',
  },
  privacy: {
    title: 'Datenschutzerklärung',
    collectedData:
      'Unser Server verarbeitet Metadaten (zum Beispiel IP-Adresse, Browser, Betriebssystem) sowie die Eingaben in den Editor. Diese Daten werden verwendet, um die Lean-Ausgabe zu berechnen und anzuzeigen. Die Informationen werden nur gespeichert, solange man auf unserer Webseite bleibt, und anschließend sofort gelöscht. Wir führen Log-Dateien, um die Software zu verbessern, aber die enthaltenen Daten sind anonymisiert.',
    browserStorage:
      'Wir verwenden keine Cookies, aber der Spielstand wird im Browser als „Website-Daten“ gespeichert. Der Spielstand wird nicht auf dem Server gespeichert; wird er im Browser gelöscht, kann er nicht wiederhergestellt werden.',
    serverLocation: 'Unser Server steht in {{location}}.',
  },
  appBar: {
    back: 'Zurück',
    backToLanding: 'Zurück zur Spielauswahl',
    backToGame: 'Zurück zur Spielübersicht',
    backToWorld: 'Zurück zur Welt',
    start: 'Starten',
    home: 'Home',
    previousLevel: 'Vorheriges Level',
    next: 'Weiter',
    nextLevel: 'Nächstes Level',
    gameInfo: 'Spielinfo',
    gameInfoTitle: 'Spielinfo & Credits',
    download: 'Herunterladen',
    downloadTitle: 'Spielstand herunterladen',
    upload: 'Laden',
    uploadTitle: 'Spielstand aus JSON laden',
    erase: 'Löschen',
    eraseTitle: 'Spielstand löschen',
    impressum: 'Impressum',
    privacy: 'Datenschutzerklärung',
    preferences: 'Einstellungen',
    github: 'Den Lean-Game-Server auf GitHub ansehen',
    openMenu: 'Menü öffnen',
    closeMenu: 'Menü schließen',
    openLanguageMenu: 'Sprachmenü öffnen',
    closeLanguageMenu: 'Sprachmenü schließen',
  },
  preferences: {
    title: 'Einstellungen',
    language: 'Sprache',
    languageNote:
      'Wenn ein Spiel nicht in der ausgewählten Sprache existiert, dann hat diese Einstellung keine Wirkung und die Standardsprache des Spiels wird verwendet.',
    useFlags: 'Sprachen durch Flaggen darstellen',
    layout: 'Seitenlayout',
    layouts: { mobile: 'Mobil', auto: 'Auto', desktop: 'Desktop' },
    showLockedInventory: 'Gesperrte Inventar-Einträge anzeigen',
    theme: 'Farbschema',
    themes: { light: 'Hell', auto: 'Auto', dark: 'Dunkel' },
    browserStorage: 'Browserspeicher',
    savePreferences: 'Einstellungen im Browser speichern',
  },
  import: {
    title: 'Spiel importieren',
    description:
      'Ein Spiel muss als öffentliches Github-Repo veröffentlicht sein und einen \
      CI Workflow haben, welcher das Spiel baut und als Artifakt speichert. \
      Das Spiel sollte den aktuellen Workflow von <skeletonLink>GameSkeleton</skeletonLink> \
      kopieren.',
    owner: 'Github Nutzer',
    repo: 'Repository',
    start: 'Import starten',
    messages: 'Meldungen des Servers',
    states: {
      running: 'Wird importiert…',
      done: 'Der Import ist abgeschlossen.',
      failed: 'Der Import ist fehlgeschlagen.',
    },
    invalidName: 'Dies ist kein gültiger Besitzer- oder Repository-Name.',
    rateLimited:
      'Dieses Spiel wurde zu oft importiert. Versuche es in {{seconds}} s erneut.',
    startError: 'Der Import konnte nicht gestartet werden: {{error}}',
    statusError:
      'Der Status des Imports konnte nicht geladen werden: {{error}}',
  },
  masks: {
    select: 'Oberfläche wählen',
    proof: 'Beweis',
    checking: 'Beweis wird geprüft…',
    transcript: 'Meldungen',
    inserted: "'{{text}}' eingefügt",
    copied: "'{{text}}' in die Zwischenablage kopiert",
    copyFailed: "'{{text}}' konnte nicht in die Zwischenablage kopiert werden",
    line: 'Zeile {{line}}',
    kinds: {
      error: 'Fehler',
      warning: 'Warnung',
      information: 'Information',
      introduction: 'Einführung',
      hint: 'Hinweis',
      conclusion: 'Abschluss',
    },
    name_typewriter: 'Schreibmaschine',
    name_raw: 'Quellcode',
  },
  layout: {
    openPanel: '{{title}} öffnen',
    closePanel: '{{title}} schließen',
  },
  game: {
    introduction: 'Einführung',
    conclusion: 'Abschluss',
    chat: 'Chat',
    inventory: 'Inventar',
  },
  chat: {
    nextHint: 'Nächster Hinweis',
  },
  inventory: {
    theorems: 'Sätze',
    tactics: 'Taktiken',
    definitions: 'Definitionen',
    notUnlocked: 'Noch nicht freigeschaltet',
    notAvailable: 'In diesem Level nicht verfügbar',
    insert: "'{{name}}' einfügen",
    close: 'Schließen',
    unlock: 'Freischalten!',
    furtherDetails: 'Weitere Details',
    provenIn: 'Bewiesen in:',
    introducedIn: 'Eingeführt in:',
    mathlibDoc: 'Mathlib-Dokumentation',
    worldLevel: '{{world}} Level {{level}}',
  },
  typewriter: {
    execute: 'Ausführen',
    inputPlaceholder: 'Taktik eingeben',
    retry: 'Ändern',
    retryTitle: 'Beweis ab hier wiederholen',
    cancelEdit: 'Bearbeiten abbrechen',
    failedCommand: 'Fehlgeschlagener Befehl',
    activeGoal: 'Aktuelles Ziel',
    goalN: 'Ziel {{n}}',
    goal: 'Ziel',
    objects: 'Objekte',
    assumptions: 'Annahmen',
    theorem: 'Satz',
    levelCompleted: 'Level abgeschlossen! 🎉',
    levelSolved: 'Level wurde einmal erfolgreich gelöst',
    noGoalsLeft: 'keine Ziele mehr',
    noGoalsLeftDescription:
      'Wahrscheinlich hast du den Level mit Warnungen gelöst oder Lean hatte einen Fehler beim Parsen.',
    startError: 'Der Lean-Server konnte nicht gestartet werden:',
    checkError: 'Der Beweis konnte nicht überprüft werden:',
  },
  popup: {
    close: 'Schließen',
  },
  gameInfo: {
    progressSaving: {
      title: 'Spielstandspeicherung',
      description:
        'Das Spiel speichert den Spielstand im lokalen Browserspeicher. Wird dieser gelöscht, ist der Spielstand nicht wiederherstellbar!<br/>Achtung: In üblichen Browsern bewirkt ein löschen von Cookies auch ein löschen des lokalen Browserspeichers (z.B. "local site data"). Der Spielstand sollte vorgehend heruntergeladen werden!',
    },
    accessibility: {
      title: 'Barrierefreiheit',
      description:
        'Sollten Sie auf Barrieren stoßen, die Ihnen den Zugang erschweren, wenden Sie sich bitte an uns! Wir sind bestrebt, solche Barrieren nach besten Kräften zu beseitigen.',
    },
    development: {
      title: 'Entwicklung',
      description:
        'Der Spieleserver wurde entwickelt von <strong>Alexander Bentkamp</strong>, <strong>Jon Eugster</strong>, unter der Leitung von <strong>Markus Zibrowius</strong>. Der Sourcecode dieses Lean-Game-Engine ist <githubLink>auf Github verfügbar</githubLink>. Bei Problemen, bitte einen <issueLink>Github-Issue</issueLink> ausfüllen oder direkt mit uns Kontakt aufnehmen.',
    },
    funding: {
      title: 'Finanzierung',
      description:
        'Dieser Spiele-Server wird bereitgestellt vom Zentrum für Informations- und Medientechnologie der Heinrich-Heine-Universität Düsseldorf. Die lean4game-Software wurde im Rahmen des Projekts <adamLink>ADAM: Anticipating the Digital Age of Mathematics</adamLink> entwickelt, finanziert durch das Programm <i>Freiraum 2022</i> der <i>Stiftung Innovation in der Hochschullehre</i>. Der laufende Betrieb des Servers und die Weiterentwicklung der Software werden durch Mittel des <i>AI for Math Fund</i> der Stiftung <i>Renaissance Philanthropy</i> ermöglicht.',
    },
  },
  progress: {
    eraseTitle: 'Spielstand löschen?',
    eraseQuestion: 'Soll der Spielstand unwiderruflich gelöscht werden?',
    deleteLevel: 'Dieses Level löschen',
    deleteWorld: 'Diese Welt löschen',
    deleteAll: 'Alles löschen',
    deleteAllWarning:
      '<p>Alles zu löschen löscht sämtliche Beweise und das gesammelte Inventar! Es wird empfohlen, den Spielstand zuerst herunterzuladen.</p><p>(Spielstände anderer Spiele werden nicht gelöscht.)</p>',
    downloadAndDeleteAll: 'Herunterladen & alles löschen',
    cancel: 'Abbrechen',
    uploadTitle: 'Spielstand hochladen',
    uploadDescription:
      '<p>Wähle eine JSON-Datei mit einem Spielstand, um diesen zu laden.</p><p><strong>Achtung:</strong> Der aktuelle Spielstand wird dabei überschrieben! Wenn du noch einmal zum aktuellen Spielstand zurückkehren möchtest, solltest du zunächst den <downloadLink>aktuellen Spielstand herunterladen</downloadLink>!</p>',
    selectFile: 'Spielstand-Datei',
    invalidFile: 'Dies ist keine gültige Spielstand-Datei: {{error}}',
    load: 'Ausgewählte Datei hochladen',
  },
  rules: {
    gameRules: 'Spielregeln',
    levels: 'Level',
    tactics: 'Taktiken',
    locked: 'gesperrt',
    unlocked: 'freigeschaltet',
    none: 'keine',
    relaxed: 'relaxed',
    regular: 'regulär',
    help: '<p>Die Spielregeln bestimmen, ob es erlaubt ist, Levels zu überspringen und ob das Spiel überprüft, welche Taktiken und Sätze freigeschaltet sind und nur diese im Beweis akzeptiert.</p><p>Bemerkung: "Freigeschaltete" Taktiken (und Sätze) werden durch zwei Faktoren bestimmt: Die Menge der Taktiken, die minimal notwendig sind, um den Level zu lösen, und dazu die Menge aller Taktiken, die in einem anderen Level freigeschaltet wurden. Das bedeutet, wenn <code>simp</code> in einem Level freigeschaltet wird, kann diese Taktik danach in jeglichen Levels verwendet werden.</p>',
  },
  landing: {
    title: 'Lean-Lern-Spiel-Server',
    subtitle:
      'Eine Sammlung von Lernspielen für den Beweisassistenten <leanLink>Lean</leanLink> <i>(Lean 4)</i> und dessen mathematische Bibliothek <mathlibLink>mathlib</mathlibLink>',
    games: {
      loading: 'Spiele werden geladen…',
      error: 'Die Spiele konnten nicht geladen werden.',
      none: 'Keine Spiele verfügbar.',
      noneDev:
        'Lokale Spiele sind die Ordner neben diesem Repository, die ein gebautes Spiel enthalten, d.h. eine `.lake/gamedata/game.json`.',
    },
    tile: {
      prerequisites: 'Voraussetzungen',
      prerequisitesTitle: 'Diese Spiele am besten vorher spielen.',
      worlds: 'Welten',
      levels: 'Level',
      languages: 'Sprachen',
    },
    capacity: {
      title: 'Server-Auslastung',
      description:
        'Dieser Server läuft auf universitärer Infrastruktur mit begrenzten Kapazitäten. Wir schätzen, dass unsere Konfiguration etwa 50 gleichzeitige Spiele mit hoher Leistung und bis zu 180 gleichzeitige Spiele mit geringerer Leistung unterstützt.',
      players: 'Aktive Spieler:innen: <strong>{{count}}</strong>',
      memory: 'RAM: <strong>{{value}} %</strong> belegt.',
      cpu: 'CPU: <strong>{{value}} %</strong> ausgelastet.',
    },
    development: {
      title: 'Entwicklungsstand',
      description:
        'Der Spieleserver und alle Spiele befinden sich in fortlaufender Entwicklung. Wir bitten darum, Fehler und Ungereimtheiten als <issueLink>GitHub Issue</issueLink> zu melden.',
    },
    newGames: {
      title: 'Neue Spiele hinzufügen',
      template:
        'Für alle, die selbst ein Spiel entwickeln möchten, gibt es das <skeletonLink>GameSkeleton GitHub Repo</skeletonLink> als Vorlage und die Anleitung <docsLink>How to Create a Game</docsLink>, die auch erklärt, wie ein Spiel auf den Server geladen und gespielt werden kann. Fragen dazu beantworten wir gern.',
      featured:
        'Auf dieser Seite ist nur eine kuratierte Auswahl an Spielen sichtbar. Wir erweitern diese Auswahl auf Anfrage sehr gerne.',
    },
    funding: {
      title: 'Finanzierung',
      description:
        'Dieser Spiele-Server wird von der Heinrich-Heine-Universität Düsseldorf bereitgestellt. Die lean4game-Software wurde im Rahmen des Projekts <adamLink>ADAM: Anticipating the Digital Age of Mathematics</adamLink> entwickelt, finanziert durch das Programm <i>Freiraum 2022</i> der <i>Stiftung Innovation in der Hochschullehre</i>. Der laufende Betrieb des Servers und die Weiterentwicklung der Software werden durch Mittel des <i>AI for Math Fund</i> der Stiftung <i>Renaissance Philanthropy</i> ermöglicht.',
    },
  },
} as const
