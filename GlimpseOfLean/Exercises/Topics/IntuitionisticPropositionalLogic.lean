import GlimpseOfLean.Library.Basic
open Set

namespace IntuitionisticPropositionalLogic

/- Let's try to implement a language of intuitionistic propositional logic.

This files assumes you already know what is intuitionistic logic and what are Heyting algebras.
Note that there is also version of this file for classical logic:
`ClassicalPropositionalLogic.lean` which has no such pre-requisites (but still assumes you are
interested in setting up a logic framework).
-/

def Variable : Type := ℕ

/- We define propositional formula, and some notation for them. -/

inductive Formula : Type where
  | var : Variable → Formula
  | bot : Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  | impl : Formula → Formula → Formula

open Formula
local notation:max (priority := high) "#" x:max => var x
local infix:30 (priority := high) " || " => disj
local infix:35 (priority := high) " && " => conj
local infix:28 (priority := high) " ⇒ " => impl

def neg (A : Formula) : Formula := A ⇒ bot
local notation:(max+2) (priority := high) "~" x:max => neg x
def top := ~bot
def equiv (A B : Formula) : Formula := (A ⇒ B) && (B ⇒ A)
local infix:29 (priority := high) " ⇔ " => equiv

/-
Next we define Heyting algebra semantics.

A valuation valued in Heyting algebra `H` is just a map from variables to `H`
Let's define how to evaluate a valuation on propositional formulae. -/
variable {H : Type*} [HeytingAlgebra H]
@[simp]
def eval (φ : Variable → H) : Formula → H
  | bot    => ⊥
  | # P    => φ P
  | A || B => eval φ A ⊔ eval φ B
  | A && B => eval φ A ⊓ eval φ B
  | A ⇒ B => eval φ A ⇨ eval φ B

/- We say that `A` is a consequence of `Γ` if for all valuations in any Heyting algebra, if
  `eval φ B` is above a certain element for all `B ∈ Γ` then `eval φ A` is above this element.
  Note that for finite sets `Γ` this corresponds exactly to
  `Infimum { eval φ B | B ∈ Γ } ≤ eval φ A`.
  This "yoneda'd" version of the definition of validity is very convenient to work with. -/
def Models (Γ : Set Formula) (A : Formula) : Prop :=
  ∀ {H : Type} [HeytingAlgebra H] {φ : Variable → H} {c}, (∀ B ∈ Γ, c ≤ eval φ B) → c ≤ eval φ A

local infix:27 (priority := high) " ⊨ " => Models
def Valid (A : Formula) : Prop := ∅ ⊨ A

/- Here are some basic properties of validity.

  The tactic `simp` will automatically simplify definitions tagged with `@[simp]` and rewrite
  using theorems tagged with `@[simp]`. -/

variable {φ : Variable → H} {A B : Formula}
@[simp] lemma eval_neg : eval φ ~A = (eval φ A)ᶜ := by simp [neg]

@[simp] lemma eval_top : eval φ top = ⊤ := by
  sorry

@[simp]
lemma isTrue_equiv : eval φ (A ⇔ B) = (eval φ A ⇨ eval φ B) ⊓ (eval φ B ⇨ eval φ A) := by
  sorry

/- As an exercise, let's prove the following proposition, which holds in intuitionistic logic. -/

example : Valid (~(A && ~A)) := by
  sorry

/- Let's define provability w.r.t. intuitionistic logic. -/
section
set_option hygiene false -- this is a hacky way to allow forward reference in notation
local infix:27 " ⊢ " => ProvableFrom


/- `Γ ⊢ A` is the predicate that there is a proof tree with conclusion `A` with assumptions from
  `Γ`. This is a typical list of rules for natural deduction with intuitionistic logic. -/
inductive ProvableFrom : Set Formula → Formula → Prop
  | ax    : ∀ {Γ A},   A ∈ Γ   → Γ ⊢ A
  | impI  : ∀ {Γ A B},  insert A Γ ⊢ B                → Γ ⊢ A ⇒ B
  | impE  : ∀ {Γ A B},           Γ ⊢ (A ⇒ B) → Γ ⊢ A  → Γ ⊢ B
  | andI  : ∀ {Γ A B},           Γ ⊢ A       → Γ ⊢ B  → Γ ⊢ A && B
  | andE1 : ∀ {Γ A B},           Γ ⊢ A && B           → Γ ⊢ A
  | andE2 : ∀ {Γ A B},           Γ ⊢ A && B           → Γ ⊢ B
  | orI1  : ∀ {Γ A B},           Γ ⊢ A                → Γ ⊢ A || B
  | orI2  : ∀ {Γ A B},           Γ ⊢ B                → Γ ⊢ A || B
  | orE   : ∀ {Γ A B C}, Γ ⊢ A || B → insert A Γ ⊢ C → insert B Γ ⊢ C → Γ ⊢ C
  | botE  : ∀ {Γ A},             Γ ⊢ bot              → Γ ⊢ A

end

local infix:27 (priority := high) " ⊢ " => ProvableFrom
def Provable (A : Formula) := ∅ ⊢ A

export ProvableFrom (ax impI impE botE andI andE1 andE2 orI1 orI2 orE)
variable {Γ Δ : Set Formula}

syntax "solve_mem" : tactic
syntax "apply_ax" : tactic
macro_rules
  | `(tactic| solve_mem) => `(tactic| first | apply mem_insert | apply mem_insert_of_mem; solve_mem)
  | `(tactic| apply_ax)  => `(tactic| { apply ax; solve_mem })

/- To practice with the proof system, let's prove the following.
  You can either use the `apply_ax` tactic defined on the previous lines, which proves a goal that
  is provable using the `ax` rule.
  Or you can do it manually, using the following lemmas about insert.
```
  mem_insert x s : x ∈ insert x s
  mem_insert_of_mem y : x ∈ s → x ∈ insert y s
```
-/
example : Provable ((~A || ~B) ⇒ ~(A && B)) := by
  sorry

/- Optional exercise -/
example : Provable (~(A && ~A)) := by
  sorry

/- Optional exercise -/
example : Provable ((~A && ~B) ⇒ ~(A || B)) := by
  sorry

/- You can prove the following using `induction` on `h`. You will want to tell Lean that you want
  to prove it for all `Δ` simultaneously using `induction h generalizing Δ`.
  Lean will mark created assumptions as inaccessible (marked with †)
  if you don't explicitly name them.
  You can name the last inaccessible variables using for example `rename_i ih` or
  `rename_i A B h ih`. Or you can prove a particular case using `case impI ih => <proof>`.
  You will probably need to use the lemma
  `insert_subset_insert : s ⊆ t → insert x s ⊆ insert x t`. -/
lemma weakening (h : Γ ⊢ A) (h2 : Γ ⊆ Δ) : Δ ⊢ A := by
  sorry

/- Use the `apply?` tactic to find the lemma that states `Γ ⊆ insert x Γ`.
  You can click the blue suggestion in the right panel to automatically apply the suggestion. -/

lemma ProvableFrom.insert (h : Γ ⊢ A) : insert B Γ ⊢ A := by
  sorry

/- Proving the deduction theorem is now easy. -/
lemma deduction_theorem (h : Γ ⊢ A) : insert (A ⇒ B) Γ ⊢ B := by
  sorry

lemma Provable.mp (h1 : Provable (A ⇒ B)) (h2 : Γ ⊢ A) : Γ ⊢ B := by
  sorry

/- This is tricky, since you need to compute using operations in a Heyting algebra. -/
set_option maxHeartbeats 0 in
theorem soundness_theorem (h : Γ ⊢ A) : Γ ⊨ A := by
  sorry

theorem valid_of_provable (h : Provable A) : Valid A := by
  sorry

/-
  If you want, you can now try some these longer projects.

  1. Define Kripke semantics and prove soundness w.r.t. Kripke semantics.

  2. Prove completeness w.r.t. either Heyting algebra semantics or Kripke semantics.

-/

end IntuitionisticPropositionalLogic

