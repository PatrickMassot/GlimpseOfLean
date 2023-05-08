import Lean

import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Propose
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.RingTheory.Ideal.Operations

import GlimpseOfLean.Lib.Suggest

set_option warningAsError false

/-
Lemmas from that file were hidden in my course, or restating things which
were proved without name in previous files.
-/

macro (name := ring) "ring" : tactic =>
  `(tactic| first | ring1 | ring_nf)

@[app_unexpander Function.comp] def unexpandFunctionComp : Lean.PrettyPrinter.Unexpander
  | `($(_) $f:term $g:term $x:term) => `(($f ∘ $g) $x)
  | _ => throw ()

namespace PiNotation
open Lean.Parser Term
open Lean.PrettyPrinter.Delaborator

/-- A direct copy of forall notation but with `Π`/`Pi` instead of `∀`/`Forall`. -/
@[scoped term_parser]
def piNotation := leading_parser:leadPrec
  unicodeSymbol "Π" "Pi" >>
  many1 (ppSpace >> (binderIdent <|> bracketedBinder)) >>
  optType >> ", " >> termParser

/--
A copy of forall notation from `Std.Util.ExtendedBinder` for pi notation
-/
syntax "Π " binderIdent binderPred ", " term : term

macro_rules
  | `(Π $x:ident $pred:binderPred, $p) =>
    `(Π $x:ident, satisfies_binder_pred% $x $pred → $p)
  | `(Π _ $pred:binderPred, $p) =>
    `(Π x, satisfies_binder_pred% x $pred → $p)

/-- Since pi notation and forall notation are interchangable, we can
parse it by simply using the forall parser. -/
@[scoped macro PiNotation.piNotation] def replacePiNotation : Lean.Macro
  | .node info _ args => return .node info ``Lean.Parser.Term.forall args
  | _ => Lean.Macro.throwUnsupported

/-- Override the Lean 4 pi notation delaborator with one that uses `Π`.
Note that this takes advantage of the fact that `(x : α) → p x` notation is
never used for propositions, so we can match on this result and rewrite it. -/
@[scoped delab forallE]
def delabPi : Delab := whenPPOption Lean.getPPNotation do
  let stx ← delabForall
  -- Replacements
  let stx : Term ←
    match stx with
    | `($group:bracketedBinder → $body) => `(Π $group:bracketedBinder, $body)
    | _ => pure stx
  -- Cute binders
  let stx : Term ←
    match stx with
    | `(∀ ($i:ident : $_), $j:ident ∈ $s → $body) =>
      if i == j then `(∀ $i:ident ∈ $s, $body) else pure stx
    -- | `(∀ ($x:ident : $_), $y:ident > $z → $body) =>
    --   if x == y then `(∀ $x:ident > $z, $body) else pure stx
    | `(Π ($i:ident : $_), $j:ident ∈ $s → $body) =>
      if i == j then `(Π $i:ident ∈ $s, $body) else pure stx
    | _ => pure stx
  -- Merging
  match stx with
  | `(Π $group, Π $groups*, $body) => `(Π $group $groups*, $body)
  | _ => pure stx

end PiNotation

section SupInfNotation
open Lean Lean.PrettyPrinter.Delaborator

/-!
Improvements to the unexpanders in `Mathlib.Order.CompleteLattice`.

These are implemented as delaborators directly.
-/

@[delab app.supᵢ]
def supᵢ_delab : Delab := whenPPOption Lean.getPPNotation do
  let #[_, _, ι, f] := (← SubExpr.getExpr).getAppArgs | failure
  unless f.isLambda do failure
  let prop ← Meta.isProp ι
  let dep := f.bindingBody!.hasLooseBVar 0
  let ppTypes ← getPPOption getPPFunBinderTypes
  let stx ← SubExpr.withAppArg do
    let dom ← SubExpr.withBindingDomain delab
    withBindingBodyUnusedName $ fun x => do
      let x : TSyntax `ident := .mk x
      let body ← delab
      if prop && !dep then
        `(⨆ (_ : $dom), $body)
      else if prop || ppTypes then
        `(⨆ ($x:ident : $dom), $body)
      else
        `(⨆ $x:ident, $body)
  -- Cute binders
  let stx : Term ←
    match stx with
    | `(⨆ $x:ident, ⨆ (_ : $y:ident ∈ $s), $body)
    | `(⨆ ($x:ident : $_), ⨆ (_ : $y:ident ∈ $s), $body) =>
      if x == y then `(⨆ $x:ident ∈ $s, $body) else pure stx
    | _ => pure stx
  return stx

@[delab app.infᵢ]
def infᵢ_delab : Delab := whenPPOption Lean.getPPNotation do
  let #[_, _, ι, f] := (← SubExpr.getExpr).getAppArgs | failure
  unless f.isLambda do failure
  let prop ← Meta.isProp ι
  let dep := f.bindingBody!.hasLooseBVar 0
  let ppTypes ← getPPOption getPPFunBinderTypes
  let stx ← SubExpr.withAppArg do
    let dom ← SubExpr.withBindingDomain delab
    withBindingBodyUnusedName $ fun x => do
      let x : TSyntax `ident := .mk x
      let body ← delab
      if prop && !dep then
        `(⨅ (_ : $dom), $body)
      else if prop || ppTypes then
        `(⨅ ($x:ident : $dom), $body)
      else
        `(⨅ $x:ident, $body)
  -- Cute binders
  let stx : Term ←
    match stx with
    | `(⨅ $x:ident, ⨅ (_ : $y:ident ∈ $s), $body)
    | `(⨅ ($x:ident : $_), ⨅ (_ : $y:ident ∈ $s), $body) =>
      if x == y then `(⨅ $x:ident ∈ $s, $body) else pure stx
    | _ => pure stx
  return stx

end SupInfNotation

-- The mathlib version is unusable because it is stated in terms of ≤
lemma ge_max_iff {α : Type _} [LinearOrder α] {p q r : α} : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q :=
max_le_iff

/- No idea why this is not in mathlib-/
lemma eq_of_abs_sub_le_all (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y := by
  intro h
  apply eq_of_abs_sub_nonpos
  by_contra H
  push_neg at H
  specialize h (|x-y|/2) (by linarith)
  rw [← sub_nonpos, sub_half] at h
  linarith


lemma abs_sub_le' {α : Type _} [LinearOrderedAddCommGroup α] (a b c : α) :
  |a - c| ≤ |a - b| + |c - b| := by
  rw [abs_sub_comm c b]
  apply abs_sub_le

def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

lemma unique_limit {u l l'} : seq_limit u l → seq_limit u l' → l = l' := by
  intros hl hl'
  apply eq_of_abs_sub_le_all
  intros ε ε_pos
  rcases hl (ε/2) (by linarith) with ⟨N, hN⟩
  rcases hl' (ε/2) (by linarith) with ⟨N', hN'⟩
  specialize hN (max N N') (le_max_left _ _)
  specialize hN' (max N N') (le_max_right _ _)
  calc |l - l'| = |(l-u (max N N')) + (u (max N N') -l')| := by ring_nf
  _ ≤ |l - u (max N N')| + |u (max N N') - l'| := by apply abs_add
  _ = |u (max N N') - l| + |u (max N N') - l'| := by rw [abs_sub_comm]
  _ ≤ ε/2 + ε/2 := by linarith
  _ = ε := by ring

def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m

def cluster_point (u : ℕ → ℝ) (a : ℝ) := ∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a

open BigOperators

lemma Finset.sum_univ_eq_single {β : Type u} {α : Type v} [Fintype α] [AddCommMonoid β] {f : α → β} (a : α)
    (h : ∀ b,  b ≠ a → f b = 0) : ∑ x, f x = f a := by
  rw [Finset.sum_eq_single]
  · tauto
  · exact λ ha ↦ (ha <| Finset.mem_univ a).elim

section prelim
open RingHom Function PiNotation

namespace Ideal
variable [CommRing R] {ι : Type _} [CommRing S] (I : Ideal R)
  (f : R →+* S) (H : ∀ (a : R), a ∈ I → f a = 0)

lemma add_eq_one_iff {I J : Ideal R} : I + J = 1 ↔ ∃ i ∈ I, ∃ j ∈ J, i + j = 1 := by
  rw [one_eq_top, eq_top_iff_one, add_eq_sup, Submodule.mem_sup]

lemma ker_mk : ker (Quotient.mk I) = I := by
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
  constructor
  · exact fun h ↦ le_antisymm h this
  · rintro rfl ; rfl

end Ideal

lemma Pi.ker_ringHom {ι : Type _} {R : ι → Type _} {S : Type _} [Π i, Semiring (R i)] [Semiring S]
  (φ : Π i, S →+* R i) : RingHom.ker (Pi.ringHom φ) = ⨅ i, RingHom.ker (φ i) := by
  ext x
  simp [RingHom.mem_ker, Ideal.mem_infᵢ, funext_iff]

end prelim

@[simp]
lemma lowerBounds_range {α ι : Type _} [Preorder α] {s : ι → α} {x : α} : x ∈ lowerBounds (Set.range s) ↔ ∀ i, x ≤ s i  := by
  constructor
  · intros hx i
    apply hx
    exact Set.mem_range_self i
  · rintro hx y ⟨i, rfl⟩
    exact hx i

@[simp]
lemma upperBounds_range {α ι : Type _} [Preorder α] {s : ι → α} {x : α} : x ∈ upperBounds (Set.range s) ↔ ∀ i, s i ≤ x :=
  lowerBounds_range (α := OrderDual α)