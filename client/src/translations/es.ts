import type { DeepPartialTranslation } from '../utils/DeepPartialTranslation'
import type { en } from './en'

export const es: DeepPartialTranslation<typeof en> = {
  errorPage: {
    title: '¡Ups!',
    description: 'Ha ocurrido algo inesperado:',
    createIssue:
      'Por favor, crea un issue en el <issueLink>repositorio de GitHub</issueLink>.',
  },
  notFound: {
    title: 'No se ha encontrado esta página',
    description:
      '<code>(404)</code> Parece que la página <code>{{pathname}}</code> no existe.',
    createIssue:
      'Si crees que debería existir, crea un issue en el <issueLink>repositorio de GitHub</issueLink>.',
  },
  legal: {
    englishBelow: '(Versión en inglés más abajo)',
    contact: 'Contacto:',
    contactDetails: 'Datos de contacto',
    technicalContact: 'Contacto técnico',
    loadError: 'No se ha podido cargar la información de contacto.',
  },
  impressum: {
    title: 'Impressum',
    legalForm: 'Forma jurídica:',
    vatId: 'Número de identificación a efectos del IVA:',
    vatIdBasis: 'según el §27a de la Ley alemana del IVA',
  },
  privacy: {
    title: 'Política de privacidad',
    collectedData:
      'Nuestro servidor recopila metadatos (como la dirección IP, el navegador o el sistema operativo) y los datos que el usuario introduce en el editor. Estos datos se utilizan para calcular la salida de Lean y mostrársela al usuario. La información se almacena mientras el usuario permanece en nuestro sitio web y se elimina inmediatamente después. Guardamos registros para mejorar nuestro software, pero los datos que contienen están anonimizados.',
    browserStorage:
      'No usamos cookies, pero tu progreso en el juego se guarda en el navegador como datos del sitio. Tu progreso no se guarda en el servidor; si borras el almacenamiento del navegador, se pierde por completo.',
    serverLocation: 'Ubicación de nuestro servidor: {{location}}.',
  },
  appBar: {
    backToLanding: 'Volver a la selección de juegos',
    back: 'Volver',
    backToGame: 'Volver a la vista general del juego',
    backToWorld: 'Volver al mundo',
    start: 'Empezar',
    home: 'Inicio',
    previousLevel: 'Nivel anterior',
    next: 'Siguiente',
    nextLevel: 'Siguiente nivel',
    gameInfo: 'Información del juego',
    gameInfoTitle: 'Información del juego y créditos',
    download: 'Descargar',
    downloadTitle: 'Descargar progreso',
    upload: 'Subir',
    uploadTitle: 'Cargar progreso desde JSON',
    erase: 'Borrar',
    eraseTitle: 'Borrar el progreso',
    impressum: 'Impressum',
    privacy: 'Política de privacidad',
    preferences: 'Preferencias',
    github: 'Ver el servidor de juegos de Lean en GitHub',
    openMenu: 'Abrir menú',
    closeMenu: 'Cerrar menú',
    openLanguageMenu: 'Abrir menú de idiomas',
    closeLanguageMenu: 'Cerrar menú de idiomas',
  },
  preferences: {
    title: 'Preferencias',
    language: 'Idioma',
    languageNote:
      'Si un juego no existe en el idioma seleccionado, este ajuste no tiene efecto y se usa el idioma predeterminado del juego.',
    useFlags: 'Usar banderas de países para representar los idiomas',
    layout: 'Diseño',
    layouts: {
      mobile: 'Móvil',
      auto: 'Automático',
      desktop: 'Escritorio',
    },
    showLockedInventory: 'Mostrar los elementos bloqueados del inventario',
    theme: 'Tema',
    themes: {
      light: 'Claro',
      auto: 'Automático',
      dark: 'Oscuro',
    },
    browserStorage: 'Almacenamiento del navegador',
    savePreferences: 'Guardar mis ajustes (en el navegador)',
  },
  layout: {
    openPanel: 'Abrir {{title}}',
    closePanel: 'Cerrar {{title}}',
  },
  game: {
    introduction: 'Introducción',
    conclusion: 'Conclusión',
    chat: 'Chat',
    inventory: 'Inventario',
  },
  chat: {
    nextHint: 'Siguiente pista',
  },
  inventory: {
    theorems: 'Teoremas',
    tactics: 'Tácticas',
    definitions: 'Definiciones',
    notUnlocked: 'Aún no desbloqueado',
    notAvailable: 'No disponible en este nivel',
    insert: "Insertar '{{name}}'",
    close: 'Cerrar',
    unlock: '¡Desbloquea este elemento!',
    furtherDetails: 'Más detalles',
    provenIn: 'Demostrado en:',
    introducedIn: 'Introducido en:',
    mathlibDoc: 'Documentación de Mathlib',
    worldLevel: '{{world}} nivel {{level}}',
  },
  typewriter: {
    execute: 'Ejecutar',
    inputPlaceholder: 'Introduce una táctica',
    retry: 'Reintentar',
    retryTitle: 'Reintentar la prueba desde aquí',
    cancelEdit: 'Cancelar la edición',
    failedCommand: 'Comando fallido',
    activeGoal: 'Objetivo activo',
    goalN: 'Objetivo {{n}}',
    goal: 'Objetivo',
    objects: 'Objetos',
    assumptions: 'Hipótesis',
    theorem: 'Teorema',
    levelCompleted: 'Nivel completado 🎉',
    levelSolved: 'El nivel ya se ha resuelto correctamente',
    noGoalsLeft: 'no quedan objetivos',
    noGoalsLeftDescription:
      'Probablemente esto significa que has resuelto el nivel con advertencias o que Lean ha encontrado un error de análisis sintáctico.',
    startError: 'No se ha podido iniciar el servidor de Lean:',
    checkError: 'No se ha podido comprobar la prueba:',
  },
  popup: {
    close: 'Cerrar',
  },
  gameInfo: {
    progressSaving: {
      title: 'Guardado del progreso',
      description:
        'El juego guarda tu progreso en el almacenamiento local del navegador. Si lo borras, ¡perderás tu progreso!<br/>Advertencia: en la mayoría de los navegadores, borrar las cookies también borra el almacenamiento local (o "datos locales del sitio"). ¡Asegúrate de descargar antes tu progreso!',
    },
    accessibility: {
      title: 'Accesibilidad',
      description:
        'Si encuentras alguna barrera de accesibilidad, ¡ponte en contacto con nosotros! Nos comprometemos a eliminar esas barreras lo mejor que podamos.',
    },
    development: {
      title: 'Desarrollo',
      description:
        'El motor del juego ha sido creado por <strong>Alexander Bentkamp</strong>, <strong>Jon Eugster</strong>, bajo la dirección de <strong>Markus Zibrowius</strong>. El código fuente de este motor de juegos de Lean está <githubLink>disponible en GitHub</githubLink>. Si tienes algún problema, crea un <issueLink>issue en GitHub</issueLink> o ponte en contacto directamente.',
    },
    funding: {
      title: 'Financiación',
      description:
        'Este servidor está alojado en la Universidad Heinrich Heine de Düsseldorf. El software leangame se desarrolló como parte del proyecto <adamLink>ADAM: Anticipating the Digital Age of Mathematics</adamLink>, financiado por el programa <i>Freiraum 2022</i> de la <i>Stiftung Innovation in der Hochschullehre</i>. El mantenimiento y el desarrollo continuos cuentan con el generoso apoyo de <i>Renaissance Philanthropy</i> a través del <i>AI for Math Fund</i>.',
    },
  },
  progress: {
    eraseTitle: '¿Borrar Progreso?',
    eraseQuestion: '¿Deseas borrar tu progreso para siempre?',
    deleteLevel: 'Borrar este nivel',
    deleteWorld: 'Borrar este mundo',
    deleteAll: 'Borrar todo',
    deleteAllWarning:
      '<p>¡Borrar todo eliminará todas tus pruebas y tu inventario recopilado! Se recomienda descargar antes tu progreso.</p><p>(El progreso de otros juegos no se eliminará.)</p>',
    downloadAndDeleteAll: 'Descargar y borrar todo',
    cancel: 'Cancelar',
    uploadTitle: 'Subir progreso guardado',
    uploadDescription:
      '<p>Selecciona un archivo JSON con el progreso del juego para cargarlo.</p><p><strong>Advertencia:</strong> Esto borrará tu progreso actual en el juego. ¡Considera antes <downloadLink>descargar tu progreso actual</downloadLink>!</p>',
    selectFile: 'Archivo de progreso',
    invalidFile: 'Este no es un archivo de progreso válido: {{error}}',
    load: 'Cargar archivo seleccionado',
  },
  rules: {
    gameRules: 'Reglas del juego',
    levels: 'niveles',
    tactics: 'tácticas',
    locked: 'bloqueado',
    unlocked: 'desbloqueado',
    none: 'ninguna',
    relaxed: 'relajadas',
    regular: 'normales',
    help: '<p>Las reglas del juego determinan si puedes saltarte niveles y si puedes usar tácticas y teoremas aún no desbloqueados.</p><p>Nota: las tácticas o teoremas "Desbloqueados" están determinados por dos cosas: el conjunto mínimo de tácticas necesarias para resolver un nivel, más cualquier táctica que hayas desbloqueado en otro nivel. Esto significa que si desbloqueas <code>simp</code> en un nivel, puedes usarlo en cualquier otro nivel a partir de entonces.</p>',
  },
  landing: {
    title: 'Servidor de Juegos de Lean',
    subtitle:
      'Un repositorio de juegos educativos sobre el asistente de demostración <leanLink>Lean</leanLink> <i>(Lean 4)</i> y su librería matemática <mathlibLink>mathlib</mathlibLink>',
    games: {
      loading: 'Cargando juegos…',
      error: 'No se han podido cargar los juegos.',
      none: 'No hay juegos disponibles.',
      noneDev:
        'Los juegos locales son las carpetas junto a este repositorio que contienen un juego compilado, es decir, un `.lake/gamedata/game.json`.',
    },
    tile: {
      prerequisites: 'Requisitos previos',
      prerequisitesTitle: 'Te recomendamos jugar primero a estos juegos.',
      worlds: 'Mundos',
      levels: 'Niveles',
      languages: 'Idiomas',
    },
    capacity: {
      title: 'Capacidad del servidor',
      description:
        'Como este servidor corre en máquinas de nuestra universidad, tiene una capacidad limitada. Estimamos que nuestra configuración admitirá alrededor de 50 partidas simultáneas con un alto rendimiento y hasta 180 partidas simultáneas a un ritmo más lento.',
      players: 'Jugadores activos: <strong>{{count}}</strong>',
      memory: 'RAM: <strong>{{value}} %</strong> usada.',
      cpu: 'CPU: <strong>{{value}} %</strong> usada.',
    },
    development: {
      title: 'Notas de desarrollo',
      description:
        'La mayoría de los aspectos de los juegos y la infraestructura siguen en desarrollo. Por favor, reporta cualquier problema que encuentres en <issueLink>GitHub</issueLink>.',
    },
    newGames: {
      title: 'Cómo añadir juegos',
      template:
        'Si quieres escribir tu propio juego, utiliza el repositorio de GitHub <skeletonLink>GameSkeleton</skeletonLink> como plantilla y lee el tutorial sobre <docsLink>cómo crear un juego</docsLink>, que también explica cómo cargar tu juego en el servidor y jugarlo. Si tienes preguntas, puedes ponerte en contacto con nosotros.',
      featured:
        'Los juegos en esta página son añadidos manualmente. Por favor, contáctanos y añadiremos el tuyo con gusto.',
    },
    funding: {
      title: 'Financiación',
      description:
        'Este servidor está alojado en la Universidad Heinrich Heine de Düsseldorf. El software leangame se desarrolló como parte del proyecto <adamLink>ADAM: Anticipating the Digital Age of Mathematics</adamLink>, financiado por el programa <i>Freiraum 2022</i> de la <i>Stiftung Innovation in der Hochschullehre</i>. El mantenimiento y el desarrollo continuos cuentan con el generoso apoyo de <i>Renaissance Philanthropy</i> a través del <i>AI for Math Fund</i>.',
    },
  },
} as const
