import GlimpseOfLean.Library.Basic
open Set

namespace ClassicalPropositionalLogic

/- Let's try to implement a language of classical propositional logic.

Note that there is also version of this file for intuitionistic logic:
`IntuitionisticPropositionalLogic.lean`
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
local notation (priority := high) "⊥" => bot

def neg (A : Formula) : Formula := A ⇒ ⊥
local notation:(max+2) (priority := high) "~" x:max => neg x
def top : Formula := ~⊥
local notation (priority := high) "⊤" => top
def equiv (A B : Formula) : Formula := (A ⇒ B) && (B ⇒ A)
local infix:29 (priority := high) " ⇔ " => equiv

/- Let's define truth w.r.t. a valuation, i.e. classical validity -/

@[simp]
def IsTrue (φ : Variable → Prop) : Formula → Prop
  | ⊥      => False
  | # P    => φ P
  | A || B => IsTrue φ A ∨ IsTrue φ B
  | A && B => IsTrue φ A ∧ IsTrue φ B
  | A ⇒ B => IsTrue φ A → IsTrue φ B

def Satisfies (φ : Variable → Prop) (Γ : Set Formula) : Prop := ∀ {A}, A ∈ Γ → IsTrue φ A
def Models (Γ : Set Formula) (A : Formula) : Prop := ∀ {φ}, Satisfies φ Γ → IsTrue φ A
local infix:27 (priority := high) " ⊨ " => Models
def Valid (A : Formula) : Prop := ∅ ⊨ A

/- Here are some basic properties of validity.

  The tactic `simp` will automatically simplify definitions tagged with `@[simp]` and rewrite
  using theorems tagged with `@[simp]`. -/

variable {φ : Variable → Prop} {A B : Formula}
@[simp] lemma isTrue_neg : IsTrue φ ~A ↔ ¬ IsTrue φ A := by simp [neg]

@[simp] lemma isTrue_top : IsTrue φ ⊤ := by
  sorry

@[simp] lemma isTrue_equiv : IsTrue φ (A ⇔ B) ↔ (IsTrue φ A ↔ IsTrue φ B) := by
  sorry

/- As an exercise, let's prove (using classical logic) the double negation elimination principle.
  `by_contra h` might be useful to prove something by contradiction. -/

example : Valid (~~A ⇔ A) := by
  sorry

/- We will frequently need to add an element to a set. This is done using
the `insert` function: `insert A Γ` means `Γ ∪ {A}`. -/

@[simp] lemma satisfies_insert_iff : Satisfies φ (insert A Γ) ↔ IsTrue φ A ∧ Satisfies φ Γ := by
  simp [Satisfies]

/- Let's define provability w.r.t. classical logic. -/
section
set_option hygiene false -- this is a hacky way to allow forward reference in notation
local infix:27 " ⊢ " => ProvableFrom

/- `Γ ⊢ A` is the predicate that there is a proof tree with conclusion `A` with assumptions from
  `Γ`. This is a typical list of rules for natural deduction with classical logic. -/
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
  | botC  : ∀ {Γ A},   insert ~A Γ ⊢ ⊥                → Γ ⊢ A

end

local infix:27 (priority := high) " ⊢ " => ProvableFrom

/- A formula is provable if it is provable from an empty set of assumption. -/
def Provable (A : Formula) := ∅ ⊢ A

export ProvableFrom (ax impI impE botC andI andE1 andE2 orI1 orI2 orE)
variable {Γ Δ : Set Formula}

/- We define a simple tactic `apply_ax` to prove something using the `ax` rule. -/
syntax "solve_mem" : tactic
syntax "apply_ax" : tactic
macro_rules
  | `(tactic| solve_mem) =>
    `(tactic| first | apply mem_singleton | apply mem_insert |
                      apply mem_insert_of_mem; solve_mem
                    | fail "tactic \'apply_ax\' failed")
  | `(tactic| apply_ax)  => `(tactic| { apply ax; solve_mem })

/- To practice with the proof system, let's prove the following.
  You can either use the `apply_ax` tactic defined on the previous lines, which proves a goal that
  is provable using the `ax` rule.
  Or you can do it manually, using the following lemmas about insert.
```
  mem_singleton x : x ∈ {x}
  mem_insert x s : x ∈ insert x s
  mem_insert_of_mem y : x ∈ s → x ∈ insert y s
```
-/

-- Let’s first see an example using the `apply_ax` tactic
example : {A, B} ⊢ A && B := by
  apply andI
  apply_ax
  apply_ax

-- And the same one done by hand in one go.
example : {A, B} ⊢ A && B := by
  exact andI (ax (mem_insert _ _)) (ax (mem_insert_of_mem _ (mem_singleton _)))


example : Provable (~~A ⇔ A) := by
  sorry

/- Optional exercise: prove the law of excluded middle. -/
example : Provable (A || ~A) := by
  sorry

/- Optional exercise: prove one of the de-Morgan laws.
  If you want to say that the argument called `A` of the axiom `impE` should be `X && Y`,
  you can do this using `impE (A := X && Y)` -/
example : Provable (~(A && B) ⇔ ~A || ~B) := by
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

/-- You will want to use the tactics `left` and `right` to prove a disjunction, and the
  tactic `cases h` if `h` is a disjunction to do a case distinction. -/
theorem soundness_theorem (h : Γ ⊢ A) : Γ ⊨ A := by
  sorry

theorem valid_of_provable (h : Provable A) : Valid A := by
  sorry

/-
  If you want, you can now try some these longer projects.

  1. Prove completeness: if a formula is valid, then it is provable
  Here is one possible strategy for this proof:
  * If a formula is valid, then so is its negation normal form (NNF);
  * If a formula in NNF is valid, then so is its conjunctive normal form (CNF);
  * If a formula in CNF is valid then it is syntactically valid:
      all its clauses contain both `A` and `¬ A` in it for some `A` (or contain `⊤`);
  * If a formula in CNF is syntactically valid, then its provable;
  * If the CNF of a formula in NNF is provable, then so is the formula itself.
  * If the NNF of a formula is provable, then so is the formula itself.

  2. Define Gentzen's sequent calculus for propositional logic, and prove that this gives rise
  to the same provability.
-/

end ClassicalPropositionalLogic

