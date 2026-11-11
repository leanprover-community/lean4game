import type { DeepPartialTranslation } from '../utils/DeepPartialTranslation'
import type { en } from './en'

export const fr: DeepPartialTranslation<typeof en> = {
  errorPage: {
    title: 'Oups !',
    description: "Un événement inattendu s'est produit :",
    createIssue:
      'Veuillez créer un issue sur le <issueLink>dépôt GitHub</issueLink>.',
  },
  notFound: {
    title: 'Cette page est introuvable',
    description:
      '<code>(404)</code> La page <code>{{pathname}}</code> ne semble pas exister.',
    createIssue:
      "Si vous pensez qu'elle devrait exister, veuillez créer un issue sur le <issueLink>dépôt GitHub</issueLink>.",
  },
  legal: {
    englishBelow: '(Version anglaise ci-dessous)',
    contact: 'Contact :',
    contactDetails: 'Coordonnées',
    technicalContact: 'Contact technique',
    loadError: "Les coordonnées n'ont pas pu être chargées.",
  },
  impressum: {
    title: 'Mentions légales',
    legalForm: 'Forme juridique :',
    vatId: "Numéro d'identification à la TVA :",
    vatIdBasis: 'selon le §27a de la loi allemande sur la TVA',
  },
  privacy: {
    title: 'Politique de confidentialité',
    collectedData:
      "Notre serveur collecte des métadonnées (telles que l'adresse IP, le navigateur, le système d'exploitation) et les données que l'utilisateur saisit dans l'éditeur. Ces données servent à calculer la sortie de Lean et à l'afficher à l'utilisateur. Les informations sont conservées tant que l'utilisateur reste sur notre site web et sont supprimées immédiatement après. Nous conservons des journaux pour améliorer notre logiciel, mais les données qu'ils contiennent sont anonymisées.",
    browserStorage:
      "Nous n'utilisons pas de cookies, mais votre progression dans le jeu est stockée dans le navigateur en tant que données du site. Votre progression n'est pas enregistrée sur le serveur ; si vous supprimez le stockage de votre navigateur, elle est définitivement perdue.",
    serverLocation: 'Emplacement de notre serveur : {{location}}.',
  },
  appBar: {
    backToLanding: 'Retour à la sélection des jeux',
    back: 'Retour',
    backToGame: "Retour à la vue d'ensemble du jeu",
    backToWorld: 'Retour au monde',
    start: 'Commencer',
    home: 'Accueil',
    previousLevel: 'Niveau précédent',
    next: 'Suivant',
    nextLevel: 'Niveau suivant',
    gameInfo: 'Infos du jeu',
    gameInfoTitle: 'Infos du jeu et crédits',
    download: 'Télécharger',
    downloadTitle: 'Télécharger la progression',
    upload: 'Téléverser',
    uploadTitle: 'Charger la progression depuis JSON',
    erase: 'Effacer',
    eraseTitle: 'Effacer la progression',
    impressum: 'Mentions légales',
    privacy: 'Politique de confidentialité',
    preferences: 'Préférences',
    github: 'Voir le serveur de jeux Lean sur GitHub',
    openMenu: 'Ouvrir le menu',
    closeMenu: 'Fermer le menu',
    openLanguageMenu: 'Ouvrir le menu des langues',
    closeLanguageMenu: 'Fermer le menu des langues',
  },
  preferences: {
    title: 'Préférences',
    language: 'Langue',
    languageNote:
      "Si un jeu n'existe pas dans la langue sélectionnée, ce paramètre n'a aucun effet et la langue par défaut du jeu est utilisée.",
    useFlags: 'Utiliser des drapeaux pour représenter les langues',
    layout: 'Disposition',
    layouts: {
      mobile: 'Mobile',
      auto: 'Auto',
      desktop: 'Bureau',
    },
    showLockedInventory: "Afficher les éléments verrouillés de l'inventaire",
    theme: 'Thème',
    themes: {
      light: 'Clair',
      auto: 'Auto',
      dark: 'Sombre',
    },
    browserStorage: 'Stockage du navigateur',
    savePreferences:
      'Sauvegarder mes paramètres (dans le stockage du navigateur)',
  },
  layout: {
    openPanel: 'Ouvrir {{title}}',
    closePanel: 'Fermer {{title}}',
  },
  game: {
    introduction: 'Introduction',
    conclusion: 'Conclusion',
    chat: 'Chat',
    inventory: 'Inventaire',
  },
  chat: {
    nextHint: 'Indice suivant',
  },
  inventory: {
    theorems: 'Théorèmes',
    tactics: 'Tactiques',
    definitions: 'Définitions',
    notUnlocked: 'Pas encore déverrouillé',
    notAvailable: 'Non disponible à ce niveau',
    insert: "Insérer '{{name}}'",
    close: 'Fermer',
    unlock: 'Déverrouiller cet élément !',
    furtherDetails: 'Plus de détails',
    provenIn: 'Démontré dans :',
    introducedIn: 'Introduit dans :',
    mathlibDoc: 'Documentation de Mathlib',
    worldLevel: '{{world}} niveau {{level}}',
  },
  typewriter: {
    execute: 'Exécuter',
    inputPlaceholder: 'Saisissez une tactique',
    retry: 'Recommencer',
    retryTitle: "Recommencer la preuve à partir d'ici",
    cancelEdit: 'Annuler la modification',
    failedCommand: 'Commande échouée',
    activeGoal: 'Objectif en cours',
    goalN: 'Objectif {{n}}',
    goal: 'Objectif',
    objects: 'Objets',
    assumptions: 'Hypothèses',
    theorem: 'Théorème',
    levelCompleted: 'Niveau terminé ! 🎉',
    levelSolved: 'Ce niveau a déjà été résolu avec succès',
    noGoalsLeft: 'plus aucun objectif',
    noGoalsLeftDescription:
      "Cela signifie probablement que vous avez résolu le niveau avec des avertissements ou que Lean a rencontré une erreur d'analyse syntaxique.",
    startError: "Le serveur Lean n'a pas pu être démarré :",
    checkError: "La preuve n'a pas pu être vérifiée :",
  },
  popup: {
    close: 'Fermer',
  },
  gameInfo: {
    progressSaving: {
      title: 'Sauvegarde de la progression',
      description:
        'Le jeu enregistre votre progression dans le stockage local de votre navigateur. Si vous le supprimez, votre progression sera perdue !<br/>Attention : dans la plupart des navigateurs, supprimer les cookies efface aussi le stockage local (ou « données locales du site »). Pensez à télécharger votre progression avant !',
    },
    accessibility: {
      title: 'Accessibilité',
      description:
        "Si vous rencontrez des obstacles d'accessibilité, contactez-nous ! Nous nous engageons à les éliminer du mieux que nous pouvons.",
    },
    development: {
      title: 'Développement',
      description:
        'Le moteur de jeu a été créé par <strong>Alexander Bentkamp</strong>, <strong>Jon Eugster</strong>, sous la direction de <strong>Markus Zibrowius</strong>. Le code source de ce moteur de jeux Lean est <githubLink>disponible sur GitHub</githubLink>. Si vous rencontrez un problème, veuillez créer un <issueLink>issue sur GitHub</issueLink> ou nous contacter directement.',
    },
    funding: {
      title: 'Financement',
      description:
        "Ce serveur est hébergé à l'Université Heinrich Heine de Düsseldorf. Le logiciel leangame a été développé dans le cadre du projet <adamLink>ADAM: Anticipating the Digital Age of Mathematics</adamLink>, financé par le programme <i>Freiraum 2022</i> de la <i>Stiftung Innovation in der Hochschullehre</i>. La maintenance et le développement continus sont généreusement soutenus par <i>Renaissance Philanthropy</i> via l'<i>AI for Math Fund</i>.",
    },
  },
  progress: {
    eraseTitle: 'Supprimer la progression ?',
    eraseQuestion:
      'Voulez-vous supprimer définitivement votre progression sauvegardée ?',
    deleteLevel: 'Supprimer ce niveau',
    deleteWorld: 'Supprimer ce monde',
    deleteAll: 'Tout supprimer',
    deleteAllWarning:
      "<p>Tout supprimer effacera toutes vos preuves et votre inventaire collecté ! Il est recommandé de télécharger d'abord votre progression.</p><p>(Les sauvegardes d'autres jeux ne sont pas supprimées.)</p>",
    downloadAndDeleteAll: 'Télécharger et tout supprimer',
    cancel: 'Annuler',
    uploadTitle: 'Téléverser la progression sauvegardée',
    uploadDescription:
      "<p>Sélectionnez un fichier JSON avec la progression du jeu sauvegardée pour charger votre progression.</p><p><strong>Attention :</strong> Cela va supprimer votre progression actuelle du jeu ! Pensez à <downloadLink>télécharger votre progression actuelle</downloadLink> d'abord !</p>",
    selectFile: 'Fichier de progression',
    invalidFile: "Ce fichier de progression n'est pas valide : {{error}}",
    load: 'Charger le fichier sélectionné',
  },
  rules: {
    gameRules: 'Règles du jeu',
    levels: 'niveaux',
    tactics: 'tactiques',
    locked: 'verrouillé',
    unlocked: 'déverrouillé',
    none: 'aucun',
    relaxed: 'détendu',
    regular: 'régulier',
    help: "<p>Les règles du jeu déterminent s'il est autorisé de passer des niveaux et si le jeu effectue des vérifications pour n'autoriser que les tactiques et théorèmes déverrouillés dans les preuves.</p><p>Remarque : Les tactiques (ou théorèmes) \"déverrouillées\" sont déterminées par deux choses : L'ensemble des tactiques minimales nécessaires pour résoudre un niveau, plus toutes les tactiques que vous avez déverrouillées dans un autre niveau. Cela signifie que si vous déverrouillez <code>simp</code> dans un niveau, vous pouvez l'utiliser désormais dans n'importe quel niveau.</p>",
  },
  landing: {
    title: 'Serveur de jeux Lean',
    subtitle:
      "Un répertoire de jeux d'apprentissage pour l'assistant de preuve <leanLink>Lean</leanLink> <i>(Lean 4)</i> et sa bibliothèque mathématique <mathlibLink>mathlib</mathlibLink>",
    games: {
      loading: 'Chargement des jeux…',
      error: "Les jeux n'ont pas pu être chargés.",
      none: 'Aucun jeu disponible.',
      noneDev:
        "Les jeux locaux sont les dossiers situés à côté de ce dépôt qui contiennent un jeu compilé, c'est-à-dire un `.lake/gamedata/game.json`.",
    },
    tile: {
      prerequisites: 'Prérequis',
      prerequisitesTitle: "Nous vous conseillons de jouer d'abord à ces jeux.",
      worlds: 'Mondes',
      levels: 'Niveaux',
      languages: 'Langues',
    },
    capacity: {
      title: 'Capacité du serveur',
      description:
        "Comme ce serveur exécute Lean sur nos machines universitaires, il a une capacité limitée. Nous estimons que notre configuration permettra de prendre en charge environ 50 parties simultanées à haute performance et jusqu'à 180 parties simultanées à un rythme plus lent.",
      players: 'Joueurs actifs : <strong>{{count}}</strong>',
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
      description:
        "Ce serveur est hébergé à l'Université Heinrich Heine de Düsseldorf. Le logiciel leangame a été développé dans le cadre du projet <adamLink>ADAM: Anticipating the Digital Age of Mathematics</adamLink>, financé par le programme <i>Freiraum 2022</i> de la <i>Stiftung Innovation in der Hochschullehre</i>. La maintenance et le développement continus sont généreusement soutenus par <i>Renaissance Philanthropy</i> via l'<i>AI for Math Fund</i>.",
    },
  },
} as const
