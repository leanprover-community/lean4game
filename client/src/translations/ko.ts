import type { DeepPartialTranslation } from '../utils/DeepPartialTranslation'
import { en } from './en'

export const ko: DeepPartialTranslation<typeof en> = {
  appBar: {
    backToLanding: '게임 선택하러 돌아가기',
    start: '시작하기',
    home: '홈',
    previous: '이전',
    previousLevel: '이전 단계',
    next: '다음',
    nextLevel: '다음 단계',
    editorMode: '편집기 모드',
    typewriterMode: '타자기 모드',
    showInventory: '인벤토리 보기',
    gameInfo: '게임 정보',
    gameInfoTitle: '게임 정보 및 제작자 명단',
    download: '내려받기',
    downloadTitle: '진도 내려받기',
    upload: '업로드',
    uploadTitle: 'JSON에서 진도 불러오기',
    erase: '지우기',
    eraseTitle: '진도 없애기',
    preferences: '기본 설정',
  },
  preferences: {
    title: '기본 설정',
    language: '언어',
    layout: '레이아웃',
    layouts: {
      mobile: '모바일',
      auto: '자동',
      desktop: '데스크톱',
    },
    savePreferences: '(브라우저에) 설정 저장하기',
  },
  game: {
    introduction: '소개',
    inventory: '인벤토리',
    worlds: '세계',
  },
  chat: {
    nextHint: '도움말 더 보기!',
  },
  inventory: {
    theorems: '정리',
    tactics: '전략',
    definitions: '정의',
    notUnlocked: '아직 잠금 해제가 안 됨',
    notAvailable: '이 단계에서 쓸 수 없음',
  },
  typewriter: {
    execute: '실행하기',
    retry: '다시 시도하기',
    retryTitle: '여기부터 증명 다시 시도하기',
    failedCommand: '실패한 명령',
    activeGoal: '활성화된 목표',
    goal: '목표',
    objects: '객체',
    assumptions: '가정',
    levelCompleted: '단계 완료! 🎉',
  },
  gameInfo: {
    funding: {
      title: '재정 지원',
    },
  },
  progress: {
    eraseTitle: '진도를 삭제하시겠습니까?',
    eraseQuestion: '저장된 진도를 불가역적으로 삭제하시겠습니까?',
    cancel: '취소하기',
    uploadTitle: '저장된 진도 업로드',
    uploadDescription:
      '<p>저장된 게임 진도가 있는 JSON 파일을 선택해 진도를 불러오십시오.</p><p><strong>경고:</strong> 이를 실행하면 현재의 게임 진도가 삭제됩니다! <downloadLink>현재의 게임 진도</downloadLink>를 먼저 내려받을지 판단하십시오!</p>',
    load: '선택한 파일 열기',
  },
  rules: {
    rules: '규칙',
    gameRules: '게임 규칙',
    levels: '단계',
    tactics: '전략',
    none: '없음',
    relaxed: '완화됨',
    regular: '일반',
    help: "<p>게임 규칙에 따라, 단계들을 건너뛰어도 되는지 그리고 증명을 작성할 때 잠금 해제가 된 전략과 정리만 이용할 수 있는지가 정해집니다.</p><p>참고: '잠금 해제'가 된 전략이나 정리는 다음 두 부류로 정해집니다. (1) 해당 단계를 푸는 데 필요한 최소한의 전략이나 정리의 모임, (2) 다른 단계에서 잠금 해제를 한 전략이나 정리. 따라서 여러분이 <code>simp</code> 전략을 잠금 해제 하면, 그 뒤로 어느 단계에서든 이 전략을 이용할 수 있습니다.</p>",
  },
  landing: {
    title: '린 게임 서버',
    subtitle:
      '<leanLink>린(Lean 4)</leanLink> 증명 보조기와 그 수학 라이브러리 <mathlibLink>매스리브(mathlib)</mathlibLink>를 학습하기 위한 게임들의 저장소',
    tile: {
      prerequisites: '선행 요건',
      worlds: '세계',
      levels: '단계',
    },
    capacity: {
      title: '서버 이용량',
      description:
        '이 서버는 저희 대학의 여러 컴퓨터에서 린을 실행하므로 그 이용량이 제한돼 있습니다. 저희 구성은 고성능으로 약 50개의 동시 게임을 지원할 수 있으며, 속도를 낮출 경우 최대 180개의 동시 게임을 지원할 수 있을 것으로 예상됩니다.',
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
    },
  },
} as const
