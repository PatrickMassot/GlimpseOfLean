import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Trigonometric

@[inherit_doc Mathlib.Tactic.RingNF.ring]
macro "ring" : tactic =>
  `(tactic| first | ring1 | ring_nf)

lemma ge_max_iff {α : Type*} [LinearOrder α] {p q r : α} : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q :=
  max_le_iff

open Lean PrettyPrinter Delaborator SubExpr in
@[app_delab Max.max]
def delabMax : Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity ``Max.max 4
  let m := mkIdent `max
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  `($(m) $(x) $(y))

open Lean PrettyPrinter Delaborator SubExpr in
@[app_delab Min.min]
def delabMin : Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity ``Min.min 4
  let m := mkIdent `min
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  `($(m) $(x) $(y))

