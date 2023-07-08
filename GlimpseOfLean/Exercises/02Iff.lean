import Mathlib.Data.Real.Basic

/- # Implications

## Using implications

Lean denotes implication by the symbol `→` instead of `⇒` because it sees a proof
of `P → Q` as a function sending any proof of `P` to a proof of `Q`
(increase font size if you can't see the difference between → and ⇒).

For instance, given a real number `a`, the lemma `sq_pos_of_pos` claims `a > 0 → a^2 > 0`
so the proof belows apply the "function" `sq_pos_of_pos` to the assumption `ha`.
-/

example (a : ℝ) (ha : a > 0) : a^2 > 0:= by
  exact sq_pos_of_pos ha

/-
The above proof is a direct proof, or forward reasonning: we already know `a > 0` and we
feed this fact into the implication. We can also use backward reasonning using the `apply`
tactic. In the this simple example, this will sound a bit silly, but it can be very
convenient in longer proofs.
-/

example (a : ℝ) (ha : a > 0) : a^2 > 0:= by
  apply sq_pos_of_pos -- Thanks to `sq_pos_of_pos`, it suffices to prove `0 < a`
  exact ha -- this is exactly our assumption `ha`.

-- Try to do the next exercise in both forward and backward reasonning style.

example (a : ℝ) (ha : a > 0) : (a^2)^2 > 0:= by
  sorry


/- ## Proving implications

In order to prove an implication, we need to assume to premise and prove the conclusion.
This is done using the `intros` tactic. Secretely the exercice above was proving the
implication `a > 0 → (a^2)^2 > 0` but the premise was already introduced for us.
-/

example (a : ℝ) : a > 0 → (a^2)^2 > 0 := by
  intros ha -- You can choose any name instead of `ha`
  exact sq_pos_of_pos (sq_pos_of_pos ha)


/- # Equivalences

## Using equivalences to rewrite statements

In the previous file, we saw how to rewrite using equalities.
The analogue operation with mathematical statements is rewriting using
equivalences. This is also done using the `rw` tactic.
Lean uses `↔` to denote equivalence instead of `⇔`
(increase font size if you can't see the difference).

In the following exercises we will use the lemma:

  `sub_nonneg : 0 ≤ y - x ↔ x ≤ y`

In order to announce an intermediate statement we use:

  `have my_name : my statement,`

This triggers the apparition of a new goal: proving the statement. The proof
need to start with a central dot `·` and, if the proof is more than one line long,
it should be indented.
After the proof is done, the statement becomes available under the name `my_name`.
-/

example {a b c : ℝ} : c + a ≤ c + b ↔ a ≤ b := by
  rw [← sub_nonneg]
  have key : (c + b) - (c + a) = b - a -- Here we introduce an intermediate statement named key
  · ring   -- and prove it after a `·`
  rw [key] -- we can now use `key`. This `rw` uses an equality result, not an equivalence
  rw [sub_nonneg] -- and switch back to reach the tautology a ≤ b ↔ a ≤ b


/-
We can also write the above proof using `calc`:
-/

example {a b c : ℝ} : c + a ≤ c + b ↔ a ≤ b := by
  have key : (c + b) - (c + a) = b - a
  · ring
  calc c + a ≤ c + b ↔ 0 ≤ (c + b) - (c + a) := by rw [sub_nonneg]
  _                  ↔ 0 ≤ b - a             := by rw [key]
  _                  ↔ a ≤ b                 := by rw [sub_nonneg]

/-
Let's prove a variation (without invoking commutativity of addition to reduce to the previous proof
since this would spoil our fun).
-/

example {a b : ℝ} (c : ℝ) : a + c ≤ b + c ↔ a ≤ b := by
  sorry


/-
Let's see how we could use this lemma. It is already in the core library, under the name
`add_le_add_iff_right`:

`add_le_add_iff_right (c : ℝ) : a + c ≤ b + c ↔ a ≤ b`

This can be read as: "`add_le_add_iff_right` is a function that will take as input a real
number `c` and will output a proof of `a + c ≤ b + c ↔ a ≤ b`".
-/

example {a b : ℝ}  (ha : 0 ≤ a) : b ≤ a + b := by
  calc b = 0 + b := by ring
  _      ≤ a + b := by { rw [add_le_add_iff_right b] ; exact ha  }

/-
## Using equivalences as pairs of implications

In the second line in the above proof is a bit silly: we use statement rewriting to reduce
the goal to our assumption `ha`, but it would be more natural to see the equivalence as a
double implication. We can access the two implications of an equivalence `h : P ↔ Q` as
`h.1 : P → Q` and `h.2 : Q → P`. This allows to rewrite the above proof as:
-/

example {a b : ℝ}  (ha : 0 ≤ a) : b ≤ a + b := by
  calc b = 0 + b := by ring
  _      ≤ a + b := by exact (add_le_add_iff_right b).2 ha


/- Let's do a variant using `add_le_add_iff_left a : a + b ≤ a + c ↔ b ≤ c` instead. -/

example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by
  sorry
/-
## Proving equivalences

In order to prove an equivalence one can use `rw` until the
goal is the tautology `P ↔ P`, just as one can do with equalities.

One can also separately prove the two implications using the `constructor`
tactic. As suggested by its name, this tactic has greater scope.

At this stage we don't have a lot of smart things to prove by double implication,
so let's see a really silly proof.
-/

example (a b : ℝ) : (a-b)*(a+b) = 0 ↔ a^2 = b^2 := by
  constructor
  · intro h
    calc a ^ 2 = b^2 + (a - b) * (a + b)  := by ring
    _          = b^2 + 0                  := by rw [h]
    _          = b^2                      := by ring
  · intro h
    calc (a-b)*(a+b) = a^2 - b^2  := by ring
    _                = b^2 - b^2  := by rw [h]
    _                = 0          := by ring

/- You can try it on the following easier case. -/

example (a b : ℝ) : a = b ↔ b - a = 0 := by
  sorry


/-
Before moving on, let us make sure Lean doesn't need so much help to
prove equalities or inequalities that linearly follow from known
equalities and inequalities. This is the job of the linear arithmetic
tactic: `linarith`.
-/

example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by
  linarith

/-
Let's enjoy this for a while.
-/

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by
  sorry

example (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d := by
  sorry

/-
This is the end of this file where you learned how to handle implications and
equivalences. You learned about tactics:
* `apply`
* `have`
* `constructor`
* `linarith`

-/
