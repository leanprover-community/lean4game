// TODO: Should not use index as key.
import React from "react";

import { InteractiveDiagnostic, MsgEmbed, TaggedText, TaggedText_stripTags } from "@leanprover/infoview-api";
import { DiagnosticSeverity } from "vscode-languageserver-types";

/** A list of messages (info/warning/error) that are produced after this command */
export function Errors ({errors, typewriterMode} : {errors : InteractiveDiagnostic[], typewriterMode : boolean}) {
  return <div>
    {errors.map((err, i) => (<Error key={`error-${i}`} error={err} typewriterMode={typewriterMode}/>))}
  </div>
}

/**
 * The plain text of a message. Unlike `TaggedText_stripTags`, this keeps the text inside
 * embedded expressions, goals, widgets and traces: Lean puts most of a message's text into
 * `expr` embeds, so stripping the tags would leave e.g. "Invalid rewrite argument ..." empty.
 */
function messageToString(msg: TaggedText<MsgEmbed>): string {
  if ("text" in msg) {
    return msg.text
  } else if ("append" in msg) {
    return msg.append.map(messageToString).join("")
  }
  const [embed, inner] = msg.tag
  if ("expr" in embed) {
    return TaggedText_stripTags(embed.expr)
  } else if ("goal" in embed) {
    const hyps = embed.goal.hyps.map(h => `${h.names.join(" ")} : ${TaggedText_stripTags(h.type)}\n`)
    return hyps.join("") + (embed.goal.goalPrefix ?? "⊢ ") + TaggedText_stripTags(embed.goal.type)
  } else if ("widget" in embed) {
    return messageToString(embed.widget.alt)
  } else if ("trace" in embed) {
    return messageToString(embed.trace.msg)
  }
  return messageToString(inner)
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
  let message: TaggedText<MsgEmbed>;
  if ("append" in error.message && "text" in error.message.append[0] &&
  error.message?.append[0].text === "unsolved goals") {
      message = error.message.append[0]
  } else {
      message = error.message
  }

  const messageString = messageToString(message);

  return (messageString.trim().length > 0 && (
  <div className={severityClass + ' ml1 message'}>
    {!typewriterMode && <p className="mv2">{title}</p>}
    <pre className="font-code pre-wrap">
      <p>{messageString}</p>
    </pre>
  </div>
  ))
}
