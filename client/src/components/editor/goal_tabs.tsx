import * as React from 'react';
import { useTranslation } from "react-i18next";
import { InteractiveGoalWithHints } from "../Defs";
import { Goal } from './goal';

const goalFilter = {
  reverse: false,
  showType: true,
  showInstance: true,
  showHiddenAssumption: true,
  showLetValue: true
}

/** The tabs of goals that lean has after the command of this step has been processed */
export function GoalTabs({ goals, last, onClick, onGoalChange=(n)=>{}}: { goals: InteractiveGoalWithHints[], last : boolean, onClick? : any, onGoalChange?: (n?: number) => void }) {
  let { t } = useTranslation()
  const [selectedGoal, setSelectedGoal] = React.useState<number>(0)

  if (goals.length == 0) {
    return <></>
  }

  return <div className="goal-tabs" onClick={onClick}>
    <div className={`tab-bar ${last ? 'current' : ''}`}>
      {goals.map((goal, i) => (
        // TODO: Should not use index as key.
        <div key={`proof-goal-${i}`} className={`tab ${i == (selectedGoal) ? "active" : ""}`} onClick={(ev) => { onGoalChange(i); setSelectedGoal(i); ev.stopPropagation() }}>
          {i ? t("Goal") + ` ${i + 1}` : t("Active Goal")}
        </div>
      ))}
    </div>
    <div className="goal-tab vscode-light">
      <Goal typewriter={false} filter={goalFilter} goal={goals[selectedGoal]?.goal} unbundle={false} />
    </div>
  </div>
}
