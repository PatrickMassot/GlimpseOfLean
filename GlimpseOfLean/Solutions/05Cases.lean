import GlimpseOfLean.Library.Basic

/-!
## Disjunctions and Cases

In this file, we learn how to handle the disjuction ("logical or") operator and to prove by splitting a hypothesis into cases, using a simple instance of the `cases` tactic.

In Lean the disjunction of two statements `P` and `Q` is denoted by `P ∨ Q`, read as "P or Q".

* To prove `P ∨ Q`, we can use the `left` or `right` tactic to prove one of the two cases. This is a generalization of the `constructor` tactic, which is used to prove (for instance) a conjunction.
* If `h : P ∨ Q`, we know one of the two cases is true. We can use the `cases` tactic to split the proof into two cases, one for each hypothesis.
-/

example (p q r s : Prop) (h : p → r) (h' : q → s) : p ∨  q → r ∨  s := by
  intro hpq
  cases hpq with
  | inl hp =>
    -- We have `p` so we can use `h` to get `r`
    left -- the "left" conclusion `r` of `r ∨ s` holds
    exact h hp
  | inr hq =>
    -- We have `q` so we can use `h'` to get `s`
    right -- the "right" conclusion `s` of `r ∨ s` holds
    exact h' hq


/-! One can also prove a disjunction without the left and right tactics by instead using the functions `Or.inl` and `Or.inr`, so the above proof can be rewritten as. -/

example (p q r s : Prop) (h : p → r) (h' : q → s) : p ∨  q → r ∨  s := by
  intro hpq
  cases hpq with
  | inl hp => exact Or.inl (h hp)
  | inr hq => exact Or.inr (h' hq)

/-! In the following exercises, you prove some disjunctions. In the third case you have a choice of which side to prove. -/
example (p q : Prop) : p → p ∨ q := by
  intro hp
  -- We have `p` so we can use `left` to get `p ∨ q`
  left
  exact hp

example (p q : Prop) : q → p ∨ q := by
  intro hq
  -- We have `q` so we can use `right` to get `p ∨ q`
  right
  exact hq

example (p q : Prop) : p ∧ q → p ∨ q := by
  intro hpq
  -- We have `p ∧ q` so we can use `left` to get `p ∨ q`
  left
  exact hpq.1


/-
We consider two more examples of splitting a proof into cases.
-/
example {k m n :ℕ} : k ∣ m ∨ k ∣ n → k ∣ m * n := by
  intro hk
  cases hk with
  | inl hkm =>
    rcases hkm with ⟨a, ha⟩
    use a * n
    rw [ha]
    ring
  | inr hkn =>
    rcases hkn with ⟨b, hb⟩
    use m * b
    rw [hb]
    ring

example {n :ℕ} : n = 0 ∨ n = 1 → n * n = n := by
  intro hn
  cases hn with
  | inl h₀ =>
    rw [h₀]
  | inr h₁ =>
    rw [h₁]
