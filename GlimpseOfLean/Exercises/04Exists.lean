import GlimpseOfLean.Library.Basic

open Function

/-
## Conjunctions

In this file, we learn how to handle the conjunction ("logical and") operator
and the existential quantifier.

In Lean the conjunction of two statements `P` and `Q` is denoted by `P ∧ Q`, read as "P and Q".

We can use a conjunction similarly to the `↔`:
* If `h : P ∧ Q` then `h.1 : P` and `h.2 : Q`.
* To prove `P ∧ Q` use the `constructor` tactic.

Furthermore, we can decompose conjunction and equivalences.
* If `h : P ∧ Q`, the tactic `rcases h with ⟨hP, hQ⟩`
  gives two new assumptions `hP : P` and `hQ : Q`.
* If `h : P ↔ Q`, the tactic `rcases h with ⟨hPQ, hQP⟩`
  gives two new assumptions `hPQ : P → Q` and `hQP : Q → P`.
-/

example (p q r s : Prop) (h : p → r) (h' : q → s) : p ∧ q → r ∧ s := by
  intro hpq
  rcases hpq with ⟨hp, hq⟩
  constructor
  · exact h hp
  · exact h' hq

/- One can also prove a conjunction without the constructor tactic by gathering both sides
using the `⟨`/`⟩` brackets, so the above proof can be rewritten as. -/

example (p q r s : Prop) (h : p → r) (h' : q → s) : p ∧ q → r ∧ s := by
  intro hpq
  exact ⟨h hpq.1, h' hpq.2⟩

/- You can choose your own style in the next exercise. -/

example (p q r : Prop) : (p → (q → r)) ↔ p ∧ q → r := by
  sorry

/- Of course Lean doesn't need any help to prove this kind of logical tautologies.
This is the job of the `tauto` tactic, which can prove true statements in propositional logic. -/
example (p q r : Prop) : (p → (q → r)) ↔ p ∧ q → r := by
  tauto

/- # Extential quantifiers

In order to prove `∃ x, P x`, we give some `x₀` using tactic `use x₀` and
then prove `P x₀`. This `x₀` can be an object from the local context
or a more complicated expression. In the example below, the property
to check after `use` is true by definition so the proof is over.
-/
example : ∃ n : ℕ, 8 = 2*n := by
  use 4

/-
In order to use `h : ∃ x, P x`, we use the `rcases` tactic to fix
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
  sorry


/-
We can now start combining quantifiers, using the definition

  `Surjective (f : X → Y) := ∀ y, ∃ x, f x = y`
-/

example (f g : ℝ → ℝ) (h : Surjective (g ∘ f)) : Surjective g := by
  sorry

/- This is the end of this file about `∃` and `∧`. You've learned about tactics
* `rcases`
* `tauto`
* `use`

This is the end of the `Basics` folder. We deliberately left out the logical or operator
and everything around negation so that you could move as quickly as possible into
actual mathematical content. You now get to choose one file from the `Topics`.

See the bottom of `03Forall` for descriptions of the choices.
-/

