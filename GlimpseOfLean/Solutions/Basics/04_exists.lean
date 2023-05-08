import GlimpseOfLean.Lib.TutoLib

open Function

/-
In this file, we learn how to handle the existential quantifier.

In order to prove `∃ x, P x`, we give some `x₀` using tactic `use x₀` and
then prove `P x₀`. This `x₀` can be an object from the local context
or a more complicated expression. In the example below, the property
to check after `use` is true by definition so the proof is over.
-/
example : ∃ n : ℕ, 8 = 2*n := by
  use 4

/-
In order to use `h : ∃ x, P x`, we use the `cases` tactic to fix
one `x₀` that works.

Again `h` can come straight from the local context or can be a more
complicated expression.
-/
example (n : ℕ) (h : ∃ k : ℕ, n = k + 1) : n > 0 := by
  -- Let's fix k₀ such that n = k₀ + 1.
  rcases h with ⟨k₀, hk₀⟩
  -- It now suffices to prove k₀ + 1 > 0.
  rw [hk₀]
  -- and we have a lemma about this
  exact Nat.succ_pos k₀

/-
The next exercises use divisibility in ℤ (beware the ∣ symbol which is
not ASCII).

By definition, `a ∣ b ↔ ∃ k, b = a*k`, so you can prove `a ∣ b` using the
`use` tactic.
-/

example (a b c : ℤ) (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c := by
  -- sorry
  rcases h₁ with ⟨k, hk⟩
  rcases h₂ with ⟨l, hl⟩
  use k*l
  calc c = b*l     := hl
     _ = (a*k)*l := by rw [hk]
     _ = a*(k*l) := by ring
  -- sorry


/-
We can now start combining quantifiers, using the definition

  `Surjective (f : X → Y) := ∀ y, ∃ x, f x = y`
-/

example (f g : ℝ → ℝ) (h : Surjective (g ∘ f)) : Surjective g := by
  -- sorry
  intro y
  rcases h y with ⟨w, rfl⟩
  use f w
  rfl
  -- sorry

/-
## Conjunctions

In Lean the conjunction of two statements `P` and `Q` is denoted by `P ∧ Q`, read as "P and Q".

The `cases` tactic decomposes an assumption. For instance given an assumption `h : P ∧ Q`,
the command `cases h with hP hQ` will gives two new assumptions `hP : P` and `hQ : Q`.

Analogously, given `h : P ↔ Q`, the command `cases h with hPQ hQP` will gives two new
assumptions `hPQ : P → Q` and `hQP : Q → P`.

The `cases` tactic operates on assumptions (or on expressions built from assumptions).
In order to constructor the *goal*, one uses `constructor`. If the current goal is `P ∧ Q` then `constructor`
will create two goals, one for `P` and one for `Q`. If the current goal is `P ↔ Q` then `constructor`
will create two goals, one for `P → Q` and one for `Q → P`.

The next example is a really silly proof, but our goal here is simply to give a simple example
where everything is done by hand.
-/

example (p q r s) (h : p → r) (h' : q → s) : p ∧ q → r ∧ s := by
  intro h
  rcases h with ⟨hp, hq⟩
  constructor
  exact h hp
  exact h' hq
