// TODO: Should not use index as key.
import React from "react";

import { InteractiveDiagnostic } from "@leanprover/infoview-api";
import { DiagnosticSeverity } from "vscode-languageserver-types";

/** A list of messages (info/warning/error) that are produced after this command */
export function Errors ({errors, typewriterMode} : {errors : InteractiveDiagnostic[], typewriterMode : boolean}) {
  return <div>
    {errors.map((err, i) => (<Error key={`error-${i}`} error={err} typewriterMode={typewriterMode}/>))}
  </div>
}

/** A list of messages (info/warning/error) that are produced after this command */
function Error({error, typewriterMode} : {error : InteractiveDiagnostic, typewriterMode : boolean}) {
  // The first step will always have an empty command

  const severityClass = error.severity ? {
    [DiagnosticSeverity.Error]: 'error',
    [DiagnosticSeverity.Warning]: 'warning',
    [DiagnosticSeverity.Information]: 'information',
    [DiagnosticSeverity.Hint]: 'hint',
  }[error.severity] : '';

  const {line, character} = error.range.start;
  const title = `Line ${line+1}, Character ${character}`;

  // Hide "unsolved goals" messages
  let message;
  if ("append" in error.message && "text" in error.message.append[0] &&
  error.message?.append[0].text === "unsolved goals") {
      message = error.message.append[0]
  } else {
      message = error.message
  }

  return <div className={severityClass + ' ml1 message'}>
    {!typewriterMode && <p className="mv2">{title}</p>}
    <pre className="font-code pre-wrap">
      <p>message</p>
    </pre>
  </div>
}
