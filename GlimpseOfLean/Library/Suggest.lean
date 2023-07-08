import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Propose

open Lean Elab Server Lsp RequestM Parser Mathlib Tactic LibrarySearch Meta Std.Tactic.TryThis
  Propose

structure TryThisInfo where
  replacement : Syntax
  deriving TypeName

@[codeActionProvider] def tryThisProvider : CodeActionProvider := fun params snap => do
  let doc ← readDoc
  let startPos := doc.meta.text.lspPosToUtf8Pos params.range.start
  let endPos := doc.meta.text.lspPosToUtf8Pos params.range.end
  have results := snap.infoTree.foldInfo (init := #[]) fun _ctx info result => Id.run do
    let .ofCustomInfo info := info | result
    let some tti := info.value.get? TryThisInfo | result
    let (some head, some tail) := (info.stx.getPos?, info.stx.getTailPos?) | result
    unless head ≤ endPos && startPos ≤ tail do return result
    result.push (head, tail, tti)
  results.mapM fun (head, tail, tti) => do
    let eager : CodeAction := { title := "Apply 'Try this'", kind? := "refactor" }
    let lazy? : IO CodeAction := do
      let td := params.textDocument
      let action := PrettyPrinter.ppCategory `tactic tti.replacement
      let fmt ← match ← (snap.runCoreM doc.meta action).toBaseIO with
      | .ok e => pure e
      | .error e => throw (.userError (← e.toMessageData.toString))
      let edit? := WorkspaceEdit.ofTextEdit td.uri {
        range.start := doc.meta.text.utf8PosToLspPos head
        range.end := doc.meta.text.utf8PosToLspPos tail
        newText := Format.pretty fmt
      }
      return { eager with edit? }
    return { eager, lazy? }

@[widget] def tryThisWidget : Widget.UserWidgetDefinition where
  name := "Tactic replacement"
  javascript := "
import * as React from 'react';
import { EditorContext, RpcContext } from '@leanprover/infoview';
const e = React.createElement;
export default function(props) {
  const editorConnection = React.useContext(EditorContext)
  function onClick() {
    editorConnection.api.applyEdit({
      changes: { [props.pos.uri]: [{ range: props.range, newText: props.replacement }] }
    })
  }
  return e('div', {className: 'ml1'}, e('pre', {className: 'font-code pre-wrap'},
    ['Try this: ', e('a', { onClick, style: { cursor: 'pointer' } }, props.replacement), props.info]))
}"

def tryThisAt (ref stx : Syntax) (msg : Format := "") : CoreM Unit := do
  pushInfoLeaf (.ofCustomInfo { stx := ref, value := Dynamic.mk (TryThisInfo.mk stx) })
  let text := Format.pretty (← PrettyPrinter.ppCategory `tactic stx)
  let info := Format.pretty msg
  if let (some head, some tail) := (stx.getPos?, stx.getTailPos?) then
    let map ← getFileMap
    let range := Lsp.Range.mk (map.utf8PosToLspPos head) (map.utf8PosToLspPos tail)
    let json := Json.mkObj [("replacement", text), ("range", toJson range), ("info", toJson info)]
    Widget.saveWidgetInfo ``tryThisWidget json ref

syntax (name := suggest) "suggest" (config)? (simpArgs)?
  (" using " (colGt term),+)? : tactic

/-- Add a `exact e` or `refine e` suggestion. (TODO: this depends on code action support) -/
def addExactSuggestion2 (origTac : Syntax) (e : Expr) : TermElabM Unit := do
  let stx ← delabToRefinableSyntax e
  let tac ← if e.hasExprMVar then `(tactic| refine $stx) else `(tactic| exact $stx)
  tryThisAt origTac tac

/-- Add a `refine e` suggestion, also printing the type of the subgoals.
(TODO: this depends on code action support) -/
def addRefineSuggestion2 (origTac : Syntax) (e : Expr) : TermElabM Unit := do
  let stx ← delabToRefinableSyntax e
  let tac ← if e.hasExprMVar then `(tactic| refine $stx) else `(tactic| exact $stx)
  let subgoals := Std.Format.prefixJoin "\n⊢ "
    (← (← getMVars e).mapM fun g => do ppExpr (← g.getType)).toList
  -- We resort to using `logInfoAt` here rather than `addSuggestion`,
  -- as I've never worked out how to have `addSuggestion` render comments.
  -- logInfoAt origTac m!"{tac}\n-- Remaining subgoals:{subgoals}"
  tryThisAt origTac tac f!"\nRemaining subgoals:{subgoals}"

elab_rules : tactic | `(tactic| suggest%$tk $[using $[$required:term],*]?) => do
  let mvar ← getMainGoal
  let (_, goal) ← (← getMainGoal).intros
  goal.withContext do
    let required := (← (required.getD #[]).mapM getFVarId).toList.map .fvar
    if let some suggestions ← librarySearch goal required then
      reportOutOfHeartbeats tk
      for suggestion in suggestions do
        withMCtx suggestion.1 do
          addRefineSuggestion2 tk (← instantiateMVars (mkMVar mvar)).headBeta
      if suggestions.isEmpty then logError "suggest didn't find any relevant lemmas"
      else logInfoAt tk m!"Suggestions found!"
      admitGoal goal
    else
      logInfoAt tk m!"Suggestions found!"
      addExactSuggestion2 tk (← instantiateMVars (mkMVar mvar)).headBeta

/-- Add a suggestion for `have : t := e`. (TODO: this depends on code action support) -/
def addHaveSuggestion2 (origTac : Syntax) (t? : Option Expr) (e : Expr) :
    TermElabM Unit := do
  let estx ← delabToRefinableSyntax e
  let prop ← isProp (← inferType e)
  let tac ← if let some t := t? then
    let tstx ← delabToRefinableSyntax t
    if prop then
      `(tactic| have : $tstx := $estx)
    else
      `(tactic| let this : $tstx := $estx)
  else
    if prop then
      `(tactic| have := $estx)
    else
      `(tactic| let this := $estx)
  tryThisAt origTac tac

syntax (name := recommend) "recommend" "!"? (" : " term)? (" using " (colGt term),+) : tactic

elab_rules : tactic |
    `(tactic| recommend%$tk $[!%$lucky]? $[ : $type:term]? using $[$terms:term],*) => do
  let goal ← getMainGoal
  goal.withContext do
    let required ← terms.mapM (elabTerm · none)
    let type ← match type with
    | some stx => elabTermWithHoles stx none (← getMainTag) true <&> (·.1)
    | none => mkFreshTypeMVar
    let proposals ← propose (← proposeLemmas.get) type required
    if proposals.isEmpty then
      throwError "recommend could not find any lemmas using the given hypotheses"
    else
      logInfoAt tk m!"Suggestions found!"
    -- TODO we should have `proposals` return a lazy list, to avoid unnecessary computation here.
    for p in proposals.toList.take 10 do
      addHaveSuggestion2 tk (← inferType p.2) p.2
    if lucky.isSome then
      let mut g := goal
      for p in proposals.toList.take 10 do
        (_, g) ← g.let p.1 p.2
      replaceMainGoal [g]
