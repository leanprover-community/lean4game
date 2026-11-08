import type { DeepPartialTranslation } from '../utils/DeepPartialTranslation'
import { en } from './en'

export const es: DeepPartialTranslation<typeof en> = {
  appBar: {
    backToLanding: 'Volver a la selección de juegos',
    start: 'Empezar',
    home: 'Inicio',
    previous: 'Anterior',
    previousLevel: 'Nivel anterior',
    next: 'Siguiente',
    nextLevel: 'Siguiente nivel',
    editorMode: 'Modo editor',
    typewriterMode: 'Modo línea a línea',
    showInventory: 'Mostrar inventario',
    gameInfo: 'Información del juego',
    gameInfoTitle: 'Información del juego y créditos',
    download: 'Descargar',
    downloadTitle: 'Descargar progreso',
    upload: 'Subir',
    uploadTitle: 'Cargar progreso desde JSON',
    erase: 'Borrar',
    eraseTitle: 'Borrar el progreso',
    preferences: 'Preferencias',
  },
  preferences: {
    title: 'Preferencias',
    language: 'Idioma',
    layout: 'Diseño',
    layouts: {
      mobile: 'Móvil',
      auto: 'Automático',
      desktop: 'Escritorio',
    },
    savePreferences: 'Guardar mis ajustes (en el navegador)',
  },
  game: {
    introduction: 'Introducción',
    inventory: 'Inventario',
    worlds: 'Mundos',
  },
  chat: {
    nextHint: '¡Mostrar más ayuda!',
  },
  inventory: {
    theorems: 'Teoremas',
    tactics: 'Tácticas',
    definitions: 'Definiciones',
    notUnlocked: 'Aún no desbloqueado',
    notAvailable: 'No disponible en este nivel',
  },
  typewriter: {
    execute: 'Ejecutar',
    retry: 'Reintentar',
    retryTitle: 'Reintentar la prueba desde aquí',
    failedCommand: 'Comando fallido',
    activeGoal: 'Objetivo activo',
    goal: 'Objetivo',
    objects: 'Objetos',
    assumptions: 'Hipótesis',
    levelCompleted: 'Nivel completado 🎉',
  },
  gameInfo: {
    funding: {
      title: 'Financiación',
    },
  },
  progress: {
    eraseTitle: '¿Borrar Progreso?',
    eraseQuestion: '¿Deseas borrar tu progreso para siempre?',
    cancel: 'Cancelar',
    uploadTitle: 'Subir progreso guardado',
    uploadDescription:
      '<p>Selecciona un archivo JSON con el progreso del juego para cargarlo.</p><p><strong>Advertencia:</strong> Esto borrará tu progreso actual en el juego. ¡Considera antes <downloadLink>descargar tu progreso actual</downloadLink>!</p>',
    load: 'Cargar archivo seleccionado',
  },
  rules: {
    rules: 'Reglas',
    gameRules: 'Reglas del juego',
    levels: 'niveles',
    tactics: 'tácticas',
    none: 'ninguna',
    relaxed: 'relajadas',
    regular: 'normales',
    help: '<p>Las reglas del juego determinan si puedes saltarte niveles y si puedes usar tácticas y teoremas aún no desbloqueados.</p><p>Nota: las tácticas o teoremas "Desbloqueados" están determinados por dos cosas: el conjunto mínimo de tácticas necesarias para resolver un nivel, más cualquier táctica que hayas desbloqueado en otro nivel. Esto significa que si desbloqueas <code>simp</code> en un nivel, puedes usarlo en cualquier otro nivel a partir de entonces.</p>',
  },
  landing: {
    title: 'Servidor de Juegos de Lean',
    subtitle:
      'Un repositorio de juegos educativos sobre el asistente de demostración <leanLink>Lean</leanLink> <i>(Lean 4)</i> y su librería matemática <mathlibLink>mathlib</mathlibLink>',
    tile: {
      prerequisites: 'Requisitos previos',
      worlds: 'Mundos',
      levels: 'Niveles',
    },
    capacity: {
      title: 'Capacidad del servidor',
      description:
        'Como este servidor corre en máquinas de nuestra universidad, tiene una capacidad limitada. Estimamos que nuestra configuración admitirá alrededor de 50 partidas simultáneas con un alto rendimiento y hasta 180 partidas simultáneas a un ritmo más lento.',
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
    },
  },
} as const
