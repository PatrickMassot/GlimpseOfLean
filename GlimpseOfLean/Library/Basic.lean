import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Defs

set_option warningAsError false
-- it would be nice to do this persistently
-- set_option linter.unnecessarySeqFocus false
-- set_option linter.unreachableTactic false
-- set_option linter.unusedVariables false

section

open Lean Parser Tactic

macro (name := ring) "ring" : tactic =>
  `(tactic| first | ring1 | ring_nf)

end

-- The mathlib version is unusable because it is stated in terms of ≤
lemma ge_max_iff {α : Type _} [LinearOrder α] {p q r : α} : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q :=
  max_le_iff

lemma abs_sub_le' {α : Type _} [LinearOrderedAddCommGroup α] (a b c : α) :
    |a - c| ≤ |a - b| + |c - b| :=
  abs_sub_comm c b ▸ abs_sub_le _ _ _

open BigOperators

lemma Finset.sum_univ_eq_single {β : Type u} {α : Type v} [Fintype α] [AddCommMonoid β]
    {f : α → β} (a : α) (h : ∀ b,  b ≠ a → f b = 0) : ∑ x, f x = f a := by
  rw [Finset.sum_eq_single]
  · exact fun b _ a ↦ h b a
  · exact fun ha ↦ (ha <| Finset.mem_univ a).elim

section prelim
open RingHom Function PiNotation

end prelim

@[simp]
lemma lowerBounds_range {α ι : Type _} [Preorder α] {s : ι → α} {x : α} :
    x ∈ lowerBounds (Set.range s) ↔ ∀ i, x ≤ s i :=
  ⟨fun hx i => hx (Set.mem_range_self i), by rintro hx y ⟨i, rfl⟩; exact hx i⟩

@[simp]
lemma upperBounds_range {α ι : Type _} [Preorder α] {s : ι → α} {x : α} :
    x ∈ upperBounds (Set.range s) ↔ ∀ i, s i ≤ x :=
  lowerBounds_range (α := OrderDual α)

open Lean PrettyPrinter Delaborator

@[delab app.Real.exp]
def my : Delab := do
  let args := (← SubExpr.getExpr).getAppArgs
  let stx ← delab args[0]!
  let e := mkIdent `exp
  `(term|$e $stx)
