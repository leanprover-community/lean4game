import type { DeepPartialTranslation } from '../utils/DeepPartialTranslation'
import { en } from './en'

export const ptBR: DeepPartialTranslation<typeof en> = {
  legal: {
    contact: 'Contato:',
    contactDetails: 'Dados de contato',
  },
  impressum: {
    title: 'Impressum',
    legalForm: 'Forma jurídica:',
    vatId: 'Número de identificação fiscal (VAT):',
    vatIdBasis: 'conforme §27a Sales Tax Act',
  },
  privacy: {
    title: 'Política de privacidade',
    collectedData:
      'Nosso servidor coleta metadados (como endereço IP, navegador, sistema operacional) e os dados que o usuário digita no editor. Esses dados são usados para calcular a saída do Lean e exibi-la ao usuário. As informações ficam armazenadas enquanto o usuário permanece em nosso site e são excluídas logo em seguida. Mantemos registros (logs) para melhorar nosso software, mas os dados neles contidos são anonimizados.',
    browserStorage:
      'Não usamos cookies, mas seu progresso no jogo é guardado no navegador como dados do site. Seu progresso não é salvo no servidor; se você apagar o armazenamento do navegador, ele se perde por completo.',
  },
  appBar: {
    backToLanding: 'Voltar à seleção de jogos',
    start: 'Começar',
    home: 'Início',
    previous: 'Anterior',
    previousLevel: 'Nível anterior',
    next: 'Próximo',
    nextLevel: 'Próximo nível',
    editorMode: 'Modo editor',
    typewriterMode: 'Modo máquina de escrever',
    showInventory: 'Mostrar inventário',
    gameInfo: 'Informações do jogo',
    gameInfoTitle: 'Informações do jogo e créditos',
    download: 'Baixar',
    downloadTitle: 'Baixar progresso',
    upload: 'Enviar',
    uploadTitle: 'Carregar progresso de JSON',
    erase: 'Apagar',
    eraseTitle: 'Limpar progresso',
    impressum: 'Impressum',
    privacy: 'Política de privacidade',
    preferences: 'Preferências',
    github: 'Ver o servidor do jogo Lean no Github',
    openMenu: 'Abrir menu',
    closeMenu: 'Fechar menu',
    openLanguageMenu: 'Abrir menu de idiomas',
    closeLanguageMenu: 'Fechar menu de idiomas',
  },
  preferences: {
    title: 'Preferências',
    language: 'Idioma',
    useFlags: 'Usar bandeiras de países para representar idiomas',
    layout: 'Layout',
    layouts: {
      mobile: 'Celular',
      auto: 'Automático',
      desktop: 'Desktop',
    },
    showLockedInventory: 'Mostrar itens bloqueados do inventário',
    browserStorage: 'Armazenamento do navegador',
    savePreferences:
      'Salvar minhas configurações (no armazenamento do navegador)',
  },
  game: {
    introduction: 'Introdução',
    inventory: 'Inventário',
    worlds: 'Mundos',
  },
  chat: {
    nextHint: 'Mostrar mais ajuda!',
  },
  inventory: {
    theorems: 'Teoremas',
    tactics: 'Táticas',
    definitions: 'Definições',
    notUnlocked: 'Ainda não desbloqueado',
    notAvailable: 'Não disponível neste nível',
    unlock: 'Desbloqueie este item!',
  },
  typewriter: {
    execute: 'Executar',
    retry: 'Tentar de novo',
    retryTitle: 'Tentar a prova de novo a partir daqui',
    failedCommand: 'Comando que falhou',
    activeGoal: 'Objetivo ativo',
    goal: 'Objetivo',
    objects: 'Objetos',
    assumptions: 'Hipóteses',
    theorem: 'Teorema',
    levelCompleted: 'Nível completado! 🎉',
  },
  gameInfo: {
    progressSaving: {
      title: 'Salvamento do progresso',
      description:
        'O jogo guarda seu progresso no armazenamento local do navegador. Se você apagá-lo, seu progresso será perdido!<br/>Atenção: na maioria dos navegadores, apagar os cookies também limpa o armazenamento local (ou "dados locais do site"). Baixe seu progresso antes!',
    },
    accessibility: {
      title: 'Acessibilidade',
      description:
        'Se você encontrar qualquer barreira de acessibilidade, entre em contato conosco! Temos o compromisso de resolver essas barreiras da melhor forma possível.',
    },
    development: {
      title: 'Desenvolvimento',
      description:
        'O motor do jogo foi criado por <strong>Alexander Bentkamp</strong>, <strong>Jon Eugster</strong>, sob a liderança de <strong>Markus Zibrowius</strong>. O código-fonte deste motor de jogos Lean está <githubLink>disponível no Github</githubLink>. Se você tiver algum problema, abra uma <issueLink>Issue no Github</issueLink> ou entre em contato diretamente.',
    },
    funding: {
      title: 'Financiamento',
      description:
        'Este servidor é hospedado na Heinrich Heine University Düsseldorf. O software lean4game foi desenvolvido como parte do projeto <adamLink>ADAM: Anticipating the Digital Age of Mathematics</adamLink>, financiado pelo programa <i>Freiraum 2022</i> da <i>Stiftung Innovation in der Hochschullehre</i>. A manutenção e o desenvolvimento contínuos contam com o generoso apoio da <i>Renaissance Philanthropy</i> por meio do <i>AI for Math Fund</i>.',
    },
  },
  progress: {
    eraseTitle: 'Excluir progresso?',
    eraseQuestion:
      'Você quer excluir seu progresso salvo de forma irreversível?',
    deleteLevel: 'Excluir este nível',
    deleteWorld: 'Excluir este mundo',
    deleteAll: 'Excluir tudo',
    downloadAndDeleteAll: 'Baixar e excluir tudo',
    cancel: 'Cancelar',
    uploadTitle: 'Enviar progresso salvo',
    uploadDescription:
      '<p>Selecione um arquivo JSON com o progresso salvo para carregar seu progresso.</p><p><strong>Atenção:</strong> Isso vai excluir seu progresso atual no jogo! Considere <downloadLink>baixar seu progresso atual</downloadLink> antes!</p>',
    load: 'Carregar arquivo selecionado',
  },
  rules: {
    rules: 'Regras',
    gameRules: 'Regras do jogo',
    levels: 'níveis',
    tactics: 'táticas',
    none: 'nenhum',
    relaxed: 'relaxado',
    regular: 'normal',
    help: '<p>As regras do jogo determinam se é permitido pular níveis e se o jogo verifica as provas para permitir apenas táticas e teoremas desbloqueados.</p><p>Observação: as táticas (ou teoremas) "desbloqueados" são determinados por duas coisas: o conjunto mínimo de táticas necessárias para resolver um nível, mais quaisquer táticas que você desbloqueou em outro nível. Ou seja, se você desbloquear <code>simp</code> em um nível, poderá usá-la daí em diante em qualquer nível.</p>',
  },
  landing: {
    title: 'Servidor de Jogos Lean',
    subtitle:
      'Um repositório de jogos de aprendizado para o assistente de provas <leanLink>Lean</leanLink> <i>(Lean 4)</i> e sua biblioteca matemática <mathlibLink>mathlib</mathlibLink>',
    tile: {
      prerequisites: 'Pré-requisitos',
      worlds: 'Mundos',
      levels: 'Níveis',
    },
    capacity: {
      title: 'Capacidade do servidor',
      description:
        'Como este servidor executa o Lean em máquinas da nossa universidade, ele tem capacidade limitada. Estimamos que nossa configuração suporte cerca de 50 jogos simultâneos com alto desempenho e até 180 jogos simultâneos em ritmo mais lento.',
      memory: 'RAM: <strong>{{value}} %</strong> usado.',
      cpu: 'CPU: <strong>{{value}} %</strong> usado.',
    },
    development: {
      title: 'Notas de desenvolvimento',
      description:
        'A maioria dos aspectos dos jogos e da infraestrutura ainda está em desenvolvimento. Fique à vontade para abrir uma <issueLink>Issue no GitHub</issueLink> sobre qualquer problema que você encontrar!',
    },
    newGames: {
      title: 'Adicionando novos jogos',
      template:
        'Se você está pensando em escrever seu próprio jogo, use o <skeletonLink>Repo GameSkeleton no GitHub</skeletonLink> como modelo e leia <docsLink>How to Create a Game</docsLink>, que também explica como carregar seu jogo no servidor e jogá-lo. Se tiver dúvidas, entre em contato conosco.',
      featured:
        'Os jogos em destaque nesta página são adicionados manualmente. Entre em contato e teremos prazer em adicionar o seu.',
    },
    funding: {
      title: 'Financiamento',
      description:
        'Este servidor é hospedado na Heinrich Heine University Düsseldorf. O software lean4game foi desenvolvido como parte do projeto <adamLink>ADAM: Anticipating the Digital Age of Mathematics</adamLink>, financiado pelo programa <i>Freiraum 2022</i> da <i>Stiftung Innovation in der Hochschullehre</i>. A manutenção e o desenvolvimento contínuos contam com o generoso apoio da <i>Renaissance Philanthropy</i> por meio do <i>AI for Math Fund</i>.',
    },
  },
} as const
