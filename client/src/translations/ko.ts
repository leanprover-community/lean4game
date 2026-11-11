import type { DeepPartialTranslation } from '../utils/DeepPartialTranslation'
import type { en } from './en'

export const ko: DeepPartialTranslation<typeof en> = {
  errorPage: {
    title: '이런!',
    description: '예기치 않은 문제가 발생했습니다:',
    createIssue: '<issueLink>깃허브 저장소</issueLink>에 이슈를 제출해 주세요.',
  },
  notFound: {
    title: '이 페이지를 찾을 수 없습니다',
    description:
      '<code>(404)</code> <code>{{pathname}}</code> 페이지는 없는 것 같습니다.',
    createIssue:
      '이 페이지가 있어야 한다고 생각하면 <issueLink>깃허브 저장소</issueLink>에 이슈를 제출해 주세요.',
  },
  legal: {
    englishBelow: '(영어판은 아래에 있습니다)',
    contact: '연락처:',
    contactDetails: '연락처 세부 정보',
    technicalContact: '기술 담당 연락처',
    loadError: '연락처 정보를 불러올 수 없습니다.',
  },
  impressum: {
    title: '관리자 정보',
    legalForm: '법적 형태:',
    vatId: '부가가치세 식별 번호:',
    vatIdBasis: '독일 부가가치세법 제27a조에 따름',
  },
  privacy: {
    title: '사생활 정책',
    collectedData:
      '저희 서버는 메타데이터(IP 주소, 브라우저, 운영 체제 등)와 사용자가 편집기에 입력한 데이터를 수집합니다. 이 데이터는 린의 출력을 계산해 사용자에게 보여 주는 데 쓰입니다. 이 정보는 사용자가 저희 웹사이트에 머무는 동안에만 저장되며 그 뒤 바로 삭제됩니다. 소프트웨어를 개선하기 위해 로그를 보관하지만, 그 안의 데이터는 익명으로 처리됩니다.',
    browserStorage:
      '저희는 쿠키를 쓰지 않지만, 게임 진도는 사이트 데이터로 브라우저에 저장됩니다. 게임 진도는 서버에 저장되지 않으므로, 브라우저 저장소를 삭제하면 완전히 사라집니다.',
    serverLocation: '서버 위치: {{location}}.',
  },
  appBar: {
    backToLanding: '게임 선택하러 돌아가기',
    back: '뒤로',
    backToGame: '게임 개요로 돌아가기',
    backToWorld: '세계로 돌아가기',
    start: '시작하기',
    home: '홈',
    previousLevel: '이전 단계',
    next: '다음',
    nextLevel: '다음 단계',
    gameInfo: '게임 정보',
    gameInfoTitle: '게임 정보 및 제작자 명단',
    download: '내려받기',
    downloadTitle: '진도 내려받기',
    upload: '업로드',
    uploadTitle: 'JSON에서 진도 불러오기',
    erase: '지우기',
    eraseTitle: '진도 없애기',
    impressum: '관리자 정보',
    privacy: '사생활 정책',
    preferences: '기본 설정',
    github: '깃허브에서 린 게임 서버 보기',
    openMenu: '메뉴 열기',
    closeMenu: '메뉴 닫기',
    openLanguageMenu: '언어 메뉴 열기',
    closeLanguageMenu: '언어 메뉴 닫기',
  },
  preferences: {
    title: '기본 설정',
    language: '언어',
    languageNote:
      '게임이 선택한 언어로 제공되지 않으면 이 설정은 효과가 없으며 게임의 기본 언어가 쓰입니다.',
    useFlags: '언어를 국기로 표시하기',
    layout: '레이아웃',
    layouts: {
      mobile: '모바일',
      auto: '자동',
      desktop: '데스크톱',
    },
    showLockedInventory: '잠긴 인벤토리 항목 보기',
    theme: '테마',
    themes: {
      light: '밝게',
      auto: '자동',
      dark: '어둡게',
    },
    browserStorage: '브라우저 저장소',
    savePreferences: '(브라우저에) 설정 저장하기',
  },
  layout: {
    openPanel: '{{title}} 열기',
    closePanel: '{{title}} 닫기',
  },
  game: {
    introduction: '소개',
    conclusion: '마무리',
    chat: '채팅',
    inventory: '인벤토리',
  },
  chat: {
    nextHint: '다음 힌트',
  },
  inventory: {
    theorems: '정리',
    tactics: '전략',
    definitions: '정의',
    notUnlocked: '아직 잠금 해제가 안 됨',
    notAvailable: '이 단계에서 쓸 수 없음',
    insert: "'{{name}}' 넣기",
    close: '닫기',
    unlock: '이 항목 잠금 해제하기!',
    furtherDetails: '자세히',
    provenIn: '증명된 곳:',
    introducedIn: '소개된 곳:',
    mathlibDoc: '매스리브 문서',
    worldLevel: '{{world}} {{level}}단계',
  },
  typewriter: {
    execute: '실행하기',
    inputPlaceholder: '전략을 입력하십시오',
    retry: '다시 시도하기',
    retryTitle: '여기부터 증명 다시 시도하기',
    cancelEdit: '편집 취소하기',
    failedCommand: '실패한 명령',
    activeGoal: '활성화된 목표',
    goalN: '목표 {{n}}',
    goal: '목표',
    objects: '객체',
    assumptions: '가정',
    theorem: '정리',
    levelCompleted: '단계 완료! 🎉',
    levelSolved: '이 단계는 이미 성공적으로 풀었습니다',
    noGoalsLeft: '남은 목표 없음',
    noGoalsLeftDescription:
      '아마도 경고가 있는 채로 단계를 풀었거나 린에서 구문 분석 오류가 발생했다는 뜻입니다.',
    startError: '린 서버를 시작할 수 없습니다:',
    checkError: '증명을 검사할 수 없습니다:',
  },
  popup: {
    close: '닫기',
  },
  gameInfo: {
    progressSaving: {
      title: '진도 저장',
      description:
        '이 게임은 진도를 브라우저의 로컬 저장소에 저장합니다. 이를 삭제하면 진도가 사라집니다!<br/>경고: 대부분의 브라우저에서는 쿠키를 삭제하면 로컬 저장소(또는 "로컬 사이트 데이터")도 지워집니다. 먼저 게임 진도를 내려받으십시오!',
    },
    accessibility: {
      title: '접근성',
      description:
        '접근성에 어려움을 겪으면 저희에게 연락해 주세요! 저희는 그런 어려움을 해결하기 위해 최선을 다하겠습니다.',
    },
    development: {
      title: '개발',
      description:
        '이 게임 엔진은 <strong>Markus Zibrowius</strong>의 지휘 아래 <strong>Alexander Bentkamp</strong>, <strong>Jon Eugster</strong>가 만들었습니다. 이 린 게임 엔진의 소스 코드는 <githubLink>깃허브에서 볼 수 있습니다</githubLink>. 문제를 겪으면 <issueLink>깃허브 이슈</issueLink>를 제출하거나 저희에게 직접 연락해 주세요.',
    },
    funding: {
      title: '재정 지원',
      description:
        "이 서버는 뒤셀도르프의 하인리히-하이네 대학에서 호스팅합니다. leangame 소프트웨어는 <i>Stiftung Innovation in der Hochschullehre</i>의 <i>Freiraum 2022</i> 프로그램이 재정을 지원한 <adamLink>'아담(ADAM): 수학의 디지털 시대 준비하기'</adamLink> 프로젝트의 일환으로 개발됐습니다. 지속적인 유지 보수와 개발은 <i>AI for Math Fund</i>를 통해 <i>Renaissance Philanthropy</i>가 아낌없이 지원하고 있습니다.",
    },
  },
  progress: {
    eraseTitle: '진도를 삭제하시겠습니까?',
    eraseQuestion: '저장된 진도를 불가역적으로 삭제하시겠습니까?',
    deleteLevel: '이 단계 삭제하기',
    deleteWorld: '이 세계 삭제하기',
    deleteAll: '모두 삭제하기',
    deleteAllWarning:
      '<p>모두 삭제하면 모든 증명과 인벤토리 안의 수집 항목들이 삭제됩니다! 먼저 진도를 내려받기를 권장합니다.</p><p>(다른 게임에 저장된 정보는 삭제되지 않습니다.)</p>',
    downloadAndDeleteAll: '내려받고 모두 삭제하기',
    cancel: '취소하기',
    uploadTitle: '저장된 진도 업로드',
    uploadDescription:
      '<p>저장된 게임 진도가 있는 JSON 파일을 선택해 진도를 불러오십시오.</p><p><strong>경고:</strong> 이를 실행하면 현재의 게임 진도가 삭제됩니다! <downloadLink>현재의 게임 진도</downloadLink>를 먼저 내려받을지 판단하십시오!</p>',
    selectFile: '진도 파일',
    invalidFile: '올바른 진도 파일이 아닙니다: {{error}}',
    load: '선택한 파일 열기',
  },
  rules: {
    gameRules: '게임 규칙',
    levels: '단계',
    tactics: '전략',
    locked: '잠김',
    unlocked: '잠금 해제됨',
    none: '없음',
    relaxed: '완화됨',
    regular: '일반',
    help: "<p>게임 규칙에 따라, 단계들을 건너뛰어도 되는지 그리고 증명을 작성할 때 잠금 해제가 된 전략과 정리만 이용할 수 있는지가 정해집니다.</p><p>참고: '잠금 해제'가 된 전략이나 정리는 다음 두 부류로 정해집니다. (1) 해당 단계를 푸는 데 필요한 최소한의 전략이나 정리의 모임, (2) 다른 단계에서 잠금 해제를 한 전략이나 정리. 따라서 여러분이 <code>simp</code> 전략을 잠금 해제 하면, 그 뒤로 어느 단계에서든 이 전략을 이용할 수 있습니다.</p>",
  },
  landing: {
    title: '린 게임 서버',
    subtitle:
      '<leanLink>린(Lean 4)</leanLink> 증명 보조기와 그 수학 라이브러리 <mathlibLink>매스리브(mathlib)</mathlibLink>를 학습하기 위한 게임들의 저장소',
    games: {
      loading: '게임 불러오는 중…',
      error: '게임을 불러올 수 없습니다.',
      none: '이용할 수 있는 게임이 없습니다.',
      noneDev:
        '로컬 게임은 이 저장소 옆에 있는 폴더 중 빌드된 게임, 즉 `.lake/gamedata/game.json`이 들어 있는 폴더입니다.',
    },
    tile: {
      prerequisites: '선행 요건',
      prerequisitesTitle: '이 게임들을 먼저 해 보기를 권장합니다.',
      worlds: '세계',
      levels: '단계',
      languages: '언어',
    },
    capacity: {
      title: '서버 이용량',
      description:
        '이 서버는 저희 대학의 여러 컴퓨터에서 린을 실행하므로 그 이용량이 제한돼 있습니다. 저희 구성은 고성능으로 약 50개의 동시 게임을 지원할 수 있으며, 속도를 낮출 경우 최대 180개의 동시 게임을 지원할 수 있을 것으로 예상됩니다.',
      players: '활동 중인 플레이어: <strong>{{count}}</strong>',
      memory: '램: <strong>{{value}} %</strong> 쓰임.',
      cpu: 'CPU: <strong>{{value}} %</strong> 쓰임.',
    },
    development: {
      title: '개발 노트',
      description:
        '게임과 그 기반 시설의 상당 부분은 여전히 개발 중입니다. 문제를 겪으면 거리낌 없이 <issueLink>깃허브 이슈</issueLink>를 제출해 주세요!',
    },
    newGames: {
      title: '새 게임 추가하기',
      template:
        "여러분이 직접 게임을 작성할 생각이 있다면, <skeletonLink>GameSkeleton 깃허브 저장소</skeletonLink>를 양식[템플릿]으로 이용하고 <docsLink>'게임 만들기(Creating a Game)'</docsLink> 문서를 읽으십시오. 여러분의 게임을 서버에서 불러오고 그 게임을 하는 방법에 관한 세부 사항도 이 문서에 나와 있습니다. 궁금한 점이 있으면 저희에게 연락해 주십시오.",
      featured:
        '이 페이지에 실린 게임들은 수동으로 추가됐습니다. 저희에게 연락하시면 여러분의 게임을 기꺼이 추가하겠습니다.',
    },
    funding: {
      title: '재정 지원',
      description:
        "이 서버는 뒤셀도르프의 하인리히-하이네 대학에서 호스팅합니다. leangame 소프트웨어는 <i>Stiftung Innovation in der Hochschullehre</i>의 <i>Freiraum 2022</i> 프로그램이 재정을 지원한 <adamLink>'아담(ADAM): 수학의 디지털 시대 준비하기'</adamLink> 프로젝트의 일환으로 개발됐습니다. 지속적인 유지 보수와 개발은 <i>AI for Math Fund</i>를 통해 <i>Renaissance Philanthropy</i>가 아낌없이 지원하고 있습니다.",
    },
  },
} as const
