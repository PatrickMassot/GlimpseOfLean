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

/- No idea why this is not in mathlib-/
lemma eq_of_abs_sub_le_all (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y := by
  refine fun h ↦ eq_of_abs_sub_nonpos ?_
  by_contra H
  push_neg at H
  specialize h (|x-y|/2) (by linarith)
  rw [← sub_nonpos, sub_half] at h
  linarith

lemma abs_sub_le' {α : Type _} [LinearOrderedAddCommGroup α] (a b c : α) :
    |a - c| ≤ |a - b| + |c - b| :=
  abs_sub_comm c b ▸ abs_sub_le _ _ _

def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

lemma unique_limit {u l l'} : seq_limit u l → seq_limit u l' → l = l' := by
  refine fun hl hl' ↦ eq_of_abs_sub_le_all _ _ fun ε ε_pos ↦ ?_
  rcases hl (ε/2) (by linarith) with ⟨N, hN⟩
  rcases hl' (ε/2) (by linarith) with ⟨N', hN'⟩
  specialize hN (max N N') (le_max_left _ _)
  specialize hN' (max N N') (le_max_right _ _)
  calc |l - l'| = |(l-u (max N N')) + (u (max N N') -l')| := by ring_nf
  _ ≤ |l - u (max N N')| + |u (max N N') - l'| := abs_add_le _ _
  _ = |u (max N N') - l| + |u (max N N') - l'| := by rw [abs_sub_comm]
  _ ≤ ε/2 + ε/2 := add_le_add hN hN'
  _ = ε := add_halves _

def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m

def cluster_point (u : ℕ → ℝ) (a : ℝ) := ∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a

open BigOperators

lemma Finset.sum_univ_eq_single {β : Type u} {α : Type v} [Fintype α] [AddCommMonoid β]
    {f : α → β} (a : α) (h : ∀ b,  b ≠ a → f b = 0) : ∑ x, f x = f a := by
  rw [Finset.sum_eq_single]
  · exact fun b _ a ↦ h b a
  · exact fun ha ↦ (ha <| Finset.mem_univ a).elim

section prelim
open RingHom Function PiNotation

namespace Ideal
variable [CommRing R] {ι : Type _} [CommRing S] (I : Ideal R)
  (f : R →+* S) (H : ∀ (a : R), a ∈ I → f a = 0)

lemma ker_mk : RingHom.ker (Quotient.mk I) = I := by
  ext x
  rw [mem_ker, Quotient.eq_zero_iff_mem]

lemma ker_lift : ker (Quotient.lift I f H) = map (Quotient.mk I) (ker f) := by
  have : comap ((Quotient.lift I f H).comp (Quotient.mk I)) ⊥ = ker f := rfl
  rw [← comap_comap] at this
  apply_fun map (Quotient.mk I) at this
  rwa [map_comap_of_surjective _ Quotient.mk_surjective] at this

variable {I f H}

lemma injective_lift_iff : Injective (Quotient.lift I f H) ↔ ker f = I := by
  have : I ≤ ker f := H
  rw [injective_iff_ker_eq_bot, ker_lift, map_eq_bot_iff_le_ker, ker_mk]
  exact ⟨fun h ↦ le_antisymm h this, fun a ↦ le_of_eq_of_le a fun _ a ↦ a⟩

end Ideal
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

