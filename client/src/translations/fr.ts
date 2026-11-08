import type { DeepPartialTranslation } from '../utils/DeepPartialTranslation'
import type { en } from './en'

export const fr: DeepPartialTranslation<typeof en> = {
  appBar: {
    backToLanding: 'Retour à la sélection des jeux',
    start: 'Commencer',
    home: 'Accueil',
    previous: 'Précédent',
    previousLevel: 'Niveau précédent',
    next: 'Suivant',
    nextLevel: 'Niveau suivant',
    editorMode: 'Mode éditeur',
    typewriterMode: 'Mode machine à écrire',
    showInventory: "Afficher l'inventaire",
    gameInfo: 'Infos du jeu',
    gameInfoTitle: 'Infos du jeu et crédits',
    download: 'Télécharger',
    downloadTitle: 'Télécharger la progression',
    upload: 'Téléverser',
    uploadTitle: 'Charger la progression depuis JSON',
    erase: 'Effacer',
    eraseTitle: 'Effacer la progression',
    preferences: 'Préférences',
  },
  preferences: {
    title: 'Préférences',
    language: 'Langue',
    layout: 'Disposition',
    layouts: {
      mobile: 'Mobile',
      auto: 'Auto',
      desktop: 'Bureau',
    },
    savePreferences:
      'Sauvegarder mes paramètres (dans le stockage du navigateur)',
  },
  game: {
    introduction: 'Introduction',
    inventory: 'Inventaire',
    worlds: 'Mondes',
  },
  chat: {
    nextHint: "Afficher plus d'aide !",
  },
  inventory: {
    theorems: 'Théorèmes',
    tactics: 'Tactiques',
    definitions: 'Définitions',
    notUnlocked: 'Pas encore déverrouillé',
    notAvailable: 'Non disponible à ce niveau',
  },
  typewriter: {
    execute: 'Exécuter',
    retry: 'Recommencer',
    retryTitle: "Recommencer la preuve à partir d'ici",
    failedCommand: 'Commande échouée',
    activeGoal: 'Objectif en cours',
    goal: 'Objectif',
    objects: 'Objets',
    assumptions: 'Hypothèses',
    levelCompleted: 'Niveau terminé ! 🎉',
  },
  gameInfo: {
    funding: {
      title: 'Financement',
    },
  },
  progress: {
    eraseTitle: 'Supprimer la progression ?',
    eraseQuestion:
      'Voulez-vous supprimer définitivement votre progression sauvegardée ?',
    cancel: 'Annuler',
    uploadTitle: 'Téléverser la progression sauvegardée',
    uploadDescription:
      "<p>Sélectionnez un fichier JSON avec la progression du jeu sauvegardée pour charger votre progression.</p><p><strong>Attention :</strong> Cela va supprimer votre progression actuelle du jeu ! Pensez à <downloadLink>télécharger votre progression actuelle</downloadLink> d'abord !</p>",
    load: 'Charger le fichier sélectionné',
  },
  rules: {
    rules: 'Règles',
    gameRules: 'Règles du jeu',
    levels: 'niveaux',
    tactics: 'tactiques',
    none: 'aucun',
    relaxed: 'détendu',
    regular: 'régulier',
    help: "<p>Les règles du jeu déterminent s'il est autorisé de passer des niveaux et si le jeu effectue des vérifications pour n'autoriser que les tactiques et théorèmes déverrouillés dans les preuves.</p><p>Remarque : Les tactiques (ou théorèmes) \"déverrouillées\" sont déterminées par deux choses : L'ensemble des tactiques minimales nécessaires pour résoudre un niveau, plus toutes les tactiques que vous avez déverrouillées dans un autre niveau. Cela signifie que si vous déverrouillez <code>simp</code> dans un niveau, vous pouvez l'utiliser désormais dans n'importe quel niveau.</p>",
  },
  landing: {
    title: 'Serveur de jeux Lean',
    subtitle:
      "Un répertoire de jeux d'apprentissage pour l'assistant de preuve <leanLink>Lean</leanLink> <i>(Lean 4)</i> et sa bibliothèque mathématique <mathlibLink>mathlib</mathlibLink>",
    tile: {
      prerequisites: 'Prérequis',
      worlds: 'Mondes',
      levels: 'Niveaux',
    },
    capacity: {
      title: 'Capacité du serveur',
      description:
        "Comme ce serveur exécute Lean sur nos machines universitaires, il a une capacité limitée. Nous estimons que notre configuration permettra de prendre en charge environ 50 parties simultanées à haute performance et jusqu'à 180 parties simultanées à un rythme plus lent.",
      memory: 'RAM : <strong>{{value}} %</strong> utilisé.',
      cpu: 'CPU : <strong>{{value}} %</strong> utilisé.',
    },
    development: {
      title: 'Notes de développement',
      description:
        "La plupart des aspects des jeux et de l'infrastructure sont encore en développement. N'hésitez pas à créer un <issueLink>GitHub Issue</issueLink> pour tout problème que vous rencontrez !",
    },
    newGames: {
      title: 'Ajouter de nouveaux jeux',
      template:
        "Si vous envisagez d'écrire votre propre jeu, vous devriez utiliser le <skeletonLink>GameSkeleton GitHub Repo</skeletonLink> comme modèle et lire <docsLink>Comment créer un jeu</docsLink>, qui explique également comment charger votre jeu sur le serveur et y jouer. Nous vous encourageons à nous contacter si vous avez des questions.",
      featured:
        'Les jeux en vedette sur cette page sont ajoutés manuellement. Contactez-nous et nous ajouterons volontiers le vôtre.',
    },
    funding: {
      title: 'Financement',
    },
  },
} as const
