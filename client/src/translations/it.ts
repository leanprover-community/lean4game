import type { DeepPartialTranslation } from '../utils/DeepPartialTranslation'
import type { en } from './en'

export const it: DeepPartialTranslation<typeof en> = {
  errorPage: {
    title: 'Ops!',
    description: 'Si è verificato un problema imprevisto:',
    createIssue: 'Apri una issue nel <issueLink>repository GitHub</issueLink>.',
  },
  notFound: {
    title: 'Pagina non trovata',
    description:
      '<code>(404)</code> La pagina <code>{{pathname}}</code> sembra non esistere.',
    createIssue:
      'Se pensi che dovrebbe esistere, apri una issue nel <issueLink>repository GitHub</issueLink>.',
  },
  legal: {
    englishBelow: '(Versione inglese più sotto)',
    contact: 'Contatti:',
    contactDetails: 'Dettagli di contatto',
    technicalContact: 'Contatto tecnico',
    loadError: 'Non è stato possibile caricare le informazioni di contatto.',
  },
  impressum: {
    title: 'Impressum',
    legalForm: 'Forma giuridica:',
    vatId: 'Partita IVA:',
    vatIdBasis: "ai sensi del §27a della legge tedesca sull'IVA",
  },
  privacy: {
    title: 'Informativa sulla privacy',
    collectedData:
      "Il nostro server raccoglie metadati (come indirizzo IP, browser, sistema operativo) e i dati che l'utente inserisce nell'editor. Questi dati vengono usati per calcolare l'output di Lean e mostrarlo all'utente. Le informazioni vengono conservate finché l'utente resta sul nostro sito web e vengono eliminate subito dopo. Conserviamo dei log per migliorare il nostro software, ma i dati in essi contenuti sono anonimizzati.",
    browserStorage:
      'Non usiamo cookie, ma il tuo progresso nel gioco viene salvato nel browser come dati del sito. Il tuo progresso non viene salvato sul server; se elimini la memoria del browser, va perso definitivamente.',
    serverLocation: 'Posizione del nostro server: {{location}}.',
  },
  appBar: {
    backToLanding: 'Torna alla selezione dei giochi',
    back: 'Indietro',
    backToGame: 'Torna alla panoramica del gioco',
    backToWorld: 'Torna al mondo',
    start: 'Via',
    home: 'Home',
    previousLevel: 'Livello precedente',
    next: 'Avanti',
    nextLevel: 'Livello successivo',
    gameInfo: 'Info sul gioco',
    gameInfoTitle: 'Info sul gioco & Riconoscimenti',
    download: 'Scarica',
    downloadTitle: 'Scarica progresso',
    upload: 'Importa',
    uploadTitle: 'Importa progresso da file JSON',
    erase: 'Elimina',
    eraseTitle: 'Elimina progresso',
    impressum: 'Impressum',
    privacy: 'Informativa sulla privacy',
    preferences: 'Preferenze',
    github: 'Vedi il Lean Game Server su GitHub',
    openMenu: 'Apri menu',
    closeMenu: 'Chiudi menu',
    openLanguageMenu: 'Apri menu lingua',
    closeLanguageMenu: 'Chiudi menu lingua',
  },
  preferences: {
    title: 'Preferenze',
    language: 'Lingua',
    languageNote:
      'Se un gioco non esiste nella lingua selezionata, questa opzione non ha effetto e viene usata la lingua predefinita del gioco.',
    useFlags: 'Usa le bandiere dei paesi per rappresentare le lingue',
    layout: 'Layout',
    layouts: {
      mobile: 'Mobile',
      auto: 'Auto',
      desktop: 'Desktop',
    },
    showLockedInventory: "Mostra gli oggetti bloccati dell'inventario",
    theme: 'Tema',
    themes: {
      light: 'Chiaro',
      auto: 'Auto',
      dark: 'Scuro',
    },
    browserStorage: 'Memoria del browser',
    savePreferences: 'Salva le mie opzioni (nella memoria del browser)',
  },
  layout: {
    openPanel: 'Apri {{title}}',
    closePanel: 'Chiudi {{title}}',
  },
  game: {
    introduction: 'Introduzione',
    conclusion: 'Conclusione',
    chat: 'Chat',
    inventory: 'Inventario',
  },
  chat: {
    nextHint: 'Suggerimento successivo',
  },
  inventory: {
    theorems: 'Teoremi',
    tactics: 'Tattiche',
    definitions: 'Definizioni',
    notUnlocked: 'Non ancora sbloccato',
    notAvailable: 'Non disponibile in questo livello',
    insert: "Inserisci '{{name}}'",
    close: 'Chiudi',
    unlock: 'Sblocca questo oggetto!',
    furtherDetails: 'Ulteriori dettagli',
    provenIn: 'Dimostrato in:',
    introducedIn: 'Introdotto in:',
    mathlibDoc: 'Documentazione di Mathlib',
    worldLevel: '{{world}} livello {{level}}',
  },
  typewriter: {
    execute: 'Esegui',
    inputPlaceholder: 'Inserisci una tattica',
    retry: 'Ritenta',
    retryTitle: 'Riprendi la dimostrazione da qui',
    cancelEdit: 'Annulla modifica',
    failedCommand: 'Comando fallito',
    activeGoal: 'Goal corrente',
    goalN: 'Goal {{n}}',
    goal: 'Goal',
    objects: 'Oggetti',
    assumptions: 'Ipotesi',
    theorem: 'Teorema',
    levelCompleted: 'Livello completato! 🎉',
    levelSolved: 'Il livello è già stato risolto con successo',
    noGoalsLeft: 'nessun goal rimasto',
    noGoalsLeftDescription:
      'Probabilmente significa che hai risolto il livello con dei warning o che Lean ha riscontrato un errore di parsing.',
    startError: 'Non è stato possibile avviare il server di Lean:',
    checkError: 'Non è stato possibile verificare la dimostrazione:',
  },
  popup: {
    close: 'Chiudi',
  },
  gameInfo: {
    progressSaving: {
      title: 'Salvataggio del progresso',
      description:
        'Il gioco salva il tuo progresso nella memoria locale del browser. Se la elimini, il tuo progresso andrà perso!<br/>Attenzione: nella maggior parte dei browser, eliminare i cookie cancella anche la memoria locale (o "dati locali dei siti"). Assicurati di scaricare prima il tuo progresso!',
    },
    accessibility: {
      title: 'Accessibilità',
      description:
        'Se incontri barriere di accessibilità, contattaci! Ci impegniamo a eliminarle nel miglior modo possibile.',
    },
    development: {
      title: 'Sviluppo',
      description:
        'Il motore di gioco è stato creato da <strong>Alexander Bentkamp</strong>, <strong>Jon Eugster</strong>, sotto la guida di <strong>Markus Zibrowius</strong>. Il codice sorgente di questo motore di giochi Lean è <githubLink>disponibile su GitHub</githubLink>. Se riscontri problemi, apri una <issueLink>Issue su GitHub</issueLink> o contattaci direttamente.',
    },
    funding: {
      title: 'Fondi',
      description:
        "Questo server è ospitato presso la Heinrich Heine University Düsseldorf. Il software lean4game è stato sviluppato nell'ambito del progetto <adamLink>ADAM: Anticipating the Digital Age of Mathematics</adamLink>, finanziato dal programma <i>Freiraum 2022</i> della <i>Stiftung Innovation in der Hochschullehre</i>. La manutenzione e lo sviluppo continui sono generosamente sostenuti da <i>Renaissance Philanthropy</i> tramite l'<i>AI for Math Fund</i>.",
    },
  },
  progress: {
    eraseTitle: 'Reset del gioco',
    eraseQuestion: 'Vuoi eliminare irreversibilmente il tuo progresso?',
    deleteLevel: 'Elimina questo livello',
    deleteWorld: 'Elimina questo mondo',
    deleteAll: 'Elimina tutto',
    deleteAllWarning:
      '<p>Eliminando tutto perderai tutte le tue dimostrazioni e il tuo inventario! Ti consigliamo di scaricare prima il tuo progresso.</p><p>(I dati di salvataggio di altri giochi non verranno eliminati.)</p>',
    downloadAndDeleteAll: 'Scarica & Elimina tutto',
    cancel: 'Annulla',
    uploadTitle: 'Importa progresso salvato',
    uploadDescription:
      '<p>Seleziona il file JSON con i dati di salvataggio da caricare.</p><p><strong>Attenzione:</strong> Questa operazione eliminerà il tuo progresso corrente! Considera di <downloadLink>scaricare il tuo progresso</downloadLink> prima!</p>',
    selectFile: 'File di progresso',
    invalidFile: 'Questo non è un file di progresso valido: {{error}}',
    load: 'Carica file selezionato',
  },
  rules: {
    gameRules: 'Regole del gioco',
    levels: 'livelli',
    tactics: 'tattiche',
    locked: 'bloccato',
    unlocked: 'sbloccato',
    none: 'nessuna',
    relaxed: 'relax',
    regular: 'normali',
    help: '<p>Le regole del gioco determinano se si possono saltare i livelli e se si possono usare le tattiche e i teoremi non ancora sbloccati nelle dimostrazioni.</p><p>Nota: Le tattiche "sbloccate" per un dato livello sono l\'insieme più piccolo di tattiche necessarie per risolvere il livello, più tutte le tattiche che hai sbloccato fino a quel punto nel gioco (lo stesso discorso vale per i teoremi). Ad esempio, se sblocchi la tattica <code>simp</code> in un livello, puoi usarla da lì in poi nel resto del gioco.</p>',
  },
  landing: {
    title: 'Lean Game Server',
    subtitle:
      'Un repository di giochi didattici per il proof assistant <leanLink>Lean</leanLink> <i>(Lean 4)</i> e la sua libreria matematica <mathlibLink>mathlib</mathlibLink>',
    games: {
      loading: 'Sto caricando i giochi…',
      error: 'Non è stato possibile caricare i giochi.',
      none: 'Nessun gioco disponibile.',
      noneDev:
        'I giochi locali sono le cartelle accanto a questo repository che contengono un gioco compilato, cioè un `.lake/gamedata/game.json`.',
    },
    tile: {
      prerequisites: 'Prerequisiti',
      prerequisitesTitle: 'Ti consigliamo di giocare prima a questi giochi.',
      worlds: 'Mondi',
      levels: 'Livelli',
      languages: 'Lingue',
    },
    capacity: {
      title: 'Capacità del Server',
      description:
        'Il server che esegue il codice Lean gira sulle macchine della nostra università, perciò ha una capacità limitata. Prevediamo che la nostra configurazione supporterà circa 50 partite simultanee ad alte prestazioni e fino a 180 partite simultanee a un ritmo più lento.',
      players: 'Giocatori attivi: <strong>{{count}}</strong>',
      memory: 'RAM: <strong>{{value}} %</strong> in uso.',
      cpu: 'CPU: <strong>{{value}} %</strong> in uso.',
    },
    development: {
      title: 'Note di sviluppo',
      description:
        "Molti aspetti dei giochi e dell'infrastruttura sono ancora in fase di sviluppo. Segnalaci qualsiasi problema con una <issueLink>Issue su GitHub</issueLink>.",
    },
    newGames: {
      title: 'Aggiungere nuovi giochi',
      template:
        'Se stai pensando di creare un nuovo gioco, ti consigliamo di usare il <skeletonLink>GameSkeleton disponibile su GitHub</skeletonLink> come punto di partenza e di leggere la guida <docsLink>How to Create a Game</docsLink>, che spiega anche come caricare il tuo gioco sul server e giocarci. Per qualsiasi altra domanda, ti invitiamo a contattarci.',
      featured:
        'I giochi in evidenza in questa pagina sono curati a mano da noi. Se vuoi vedere il tuo gioco, scrivici e lo aggiungeremo volentieri.',
    },
    funding: {
      title: 'Fondi',
      description:
        "Questo server è ospitato presso la Heinrich Heine University Düsseldorf. Il software lean4game è stato sviluppato nell'ambito del progetto <adamLink>ADAM: Anticipating the Digital Age of Mathematics</adamLink>, finanziato dal programma <i>Freiraum 2022</i> della <i>Stiftung Innovation in der Hochschullehre</i>. La manutenzione e lo sviluppo continui sono generosamente sostenuti da <i>Renaissance Philanthropy</i> tramite l'<i>AI for Math Fund</i>.",
    },
  },
} as const
