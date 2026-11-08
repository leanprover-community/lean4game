import type { DeepPartialTranslation } from '../utils/DeepPartialTranslation'
import { en } from './en'

export const it: DeepPartialTranslation<typeof en> = {
  appBar: {
    backToLanding: 'Torna alla selezione dei giochi',
    start: 'Via',
    home: 'Home',
    previous: 'Indietro',
    previousLevel: 'Livello precedente',
    next: 'Avanti',
    nextLevel: 'Livello successivo',
    editorMode: 'Modalità editor',
    typewriterMode: 'Modalità interattiva',
    showInventory: 'Mostra inventario',
    gameInfo: 'Info sul gioco',
    gameInfoTitle: 'Info sul gioco & Riconoscimenti',
    download: 'Scarica',
    downloadTitle: 'Scarica progresso',
    upload: 'Importa',
    uploadTitle: 'Importa progresso da file JSON',
    erase: 'Elimina',
    eraseTitle: 'Elimina progresso',
    preferences: 'Preferenze',
  },
  preferences: {
    title: 'Preferenze',
    language: 'Lingua',
    layout: 'Layout',
    layouts: {
      mobile: 'Mobile',
      auto: 'Auto',
      desktop: 'Desktop',
    },
    savePreferences: 'Salva le mie opzioni (nella memoria del browser)',
  },
  game: {
    introduction: 'Introduzione',
    inventory: 'Inventario',
    worlds: 'Mondi',
  },
  chat: {
    nextHint: 'Aiutami!',
  },
  inventory: {
    theorems: 'Teoremi',
    tactics: 'Tattiche',
    definitions: 'Definizioni',
    notUnlocked: 'Non ancora sbloccato',
    notAvailable: 'Non disponibile in questo livello',
  },
  typewriter: {
    execute: 'Esegui',
    retry: 'Ritenta',
    retryTitle: 'Riprendi la dimostrazione da qui',
    failedCommand: 'Comando fallito',
    activeGoal: 'Goal corrente',
    goal: 'Goal',
    objects: 'Oggetti',
    assumptions: 'Ipotesi',
    levelCompleted: 'Livello completato! 🎉',
  },
  gameInfo: {
    funding: {
      title: 'Fondi',
    },
  },
  progress: {
    eraseTitle: 'Reset del gioco',
    eraseQuestion: 'Vuoi eliminare irreversibilmente il tuo progresso?',
    cancel: 'Annulla',
    uploadTitle: 'Importa progresso salvato',
    uploadDescription:
      '<p>Seleziona il file JSON con i dati di salvataggio da caricare.</p><p><strong>Attenzione:</strong> Questa operazione eliminerà il tuo progresso corrente! Considera di <downloadLink>scaricare il tuo progresso</downloadLink> prima!</p>',
    load: 'Carica file selezionato',
  },
  rules: {
    rules: 'Regole',
    gameRules: 'Regole del gioco',
    levels: 'livelli',
    tactics: 'tattiche',
    none: 'nessuna',
    relaxed: 'relax',
    regular: 'normali',
    help: '<p>Le regole del gioco determinano se si possono saltare i livelli e se si possono usare le tattiche e i teoremi non ancora sbloccati nelle dimostrazioni.</p><p>Nota: Le tattiche "sbloccate" per un dato livello sono l\'insieme più piccolo di tattiche necessarie per risolvere il livello, più tutte le tattiche che hai sbloccato fino a quel punto nel gioco (lo stesso discorso vale per i teoremi). Ad esempio, se sblocchi la tattica <code>simp</code> in un livello, puoi usarla da lì in poi nel resto del gioco.</p>',
  },
  landing: {
    title: 'Lean Game Server',
    subtitle:
      'Un repository di giochi didattici per il proof assistant <leanLink>Lean</leanLink> <i>(Lean 4)</i> e la sua libreria matematica <mathlibLink>mathlib</mathlibLink>',
    tile: {
      prerequisites: 'Prerequisiti',
      worlds: 'Mondi',
      levels: 'Livelli',
    },
    capacity: {
      title: 'Capacità del Server',
      description:
        'Il server che esegue il codice Lean gira sulle macchine della nostra università, perciò ha una capacità limitata. Prevediamo che la nostra configurazione supporterà circa 50 partite simultanee ad alte prestazioni e fino a 180 partite simultanee a un ritmo più lento.',
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
    },
  },
} as const
