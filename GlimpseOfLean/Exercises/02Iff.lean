import GlimpseOfLean.Library.Basic

/- # Implications

## Using implications

Lean denotes implication by the symbol `→` instead of `⇒` because it sees a proof
of `P → Q` as a function sending any proof of `P` to a proof of `Q`
(increase font size if you can't see the difference between → and ⇒).

For instance, given a real number `a`, the lemma `sq_pos_of_pos` claims `0 < a → 0 < a^2`
so the proof belows apply the "function" `sq_pos_of_pos` to the assumption `ha`.

Remember that whenever you see in a Lean file a symbol that you don't see on
your keyboard, such as →, you can put your mouse cursor above it and learn from
a tooltip how to type it. In the case of →, you can type it by typing "\to ", so
backslash-t-o-space.
-/

example (a : ℝ) (ha : 0 < a) : 0 < a^2 := by
  exact sq_pos_of_pos ha

/-
The above proof is a direct proof: we already know `0 < a` and we feed this fact into the
implication.
We can also use backward reasoning using the `apply` tactic.
-/

example (a : ℝ) (ha : 0 < a) : 0 < (a^2)^2 := by
  apply sq_pos_of_pos -- Thanks to `sq_pos_of_pos`, it suffices to prove `0 < a^2`
  apply sq_pos_of_pos -- Thanks to `sq_pos_of_pos`, it suffices to prove `0 < a`
  exact ha -- this is exactly our assumption `ha`.

/-
Try to do the next exercise using the lemma `add_pos : 0 < x → 0 < y → 0 < x + y`.
Note that after you `apply add_pos` you will have two goals, that you will have to
prove one-by-one.
-/

example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a^2 + b^2 := by
  sorry

/-
You can also give a proof with forward reasoning, using the `have` tactic.
In order to announce an intermediate statement we use:

  `have my_name : my_statement := by`

and then increase the indentation level.
This triggers the apparition of a new goal: proving the statement.
After the proof is done, the statement becomes available under the name `my_name`.
If the proof is a single `exact` tactic then you can get rid
of `by` and `exact` and directly put the argument of `exact` after the `:=`.
-/

example (a : ℝ) (ha : 0 < a) : 0 < (a^2)^2 := by
  have h2 : 0 < a^2 := by     -- we declare `0 < a^2` as a subgoal
    apply sq_pos_of_pos  -- we start proving the subgoal
    exact ha             -- this line is indented, so part of the proof of the subgoal
  exact sq_pos_of_pos h2 -- we finished the subgoal, and now we prove the main goal using it.

/- Now prove the same lemma as before using forwards reasoning. -/

example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a^2 + b^2 := by
  sorry


/- ## Proving implications

In order to prove an implication, we need to assume the premise and prove the conclusion.
This is done using the `intro` tactic. Secretly the exercise above was proving the
implication `a > 0 → (a^2)^2 > 0` but the premise was already introduced for us.
-/

example (a b : ℝ) : a > 0 → b > 0 → a + b > 0 := by
  intro ha hb -- You can choose any names here
  exact add_pos ha hb

/- Now prove the following simple statement in propositional logic.
Note that `p → q → r` means `p → (q → r)`. -/
example (p q r : Prop) : (p → q) → (p → q → r) → p → r := by
  sorry

/-
Note that, when using `intro`, you need to give a name to the assumption.
Lean will let you use a name that was already used. In that case the new
assumption will shadow the existing one which becomes inaccessible. So the safe
thing to do by default is to use a new name.
-/

/- # Equivalences

## Using equivalences to rewrite statements

In the previous file, we saw how to rewrite using equalities.
The analogue operation with mathematical statements is rewriting using
equivalences. This is also done using the `rw` tactic.
Lean uses `↔` to denote equivalence instead of `⇔`
(increase font size if you can't see the difference).

In the following exercises we will use the lemma:

  `sub_nonneg : 0 ≤ y - x ↔ x ≤ y`
-/

example {a b c : ℝ} : c + a ≤ c + b ↔ a ≤ b := by
  rw [← sub_nonneg] -- This `rw` uses an equivalence
  have key : (c + b) - (c + a) = b - a := by
    ring
  rw [key] -- This `rw` uses an equality result, not an equivalence
  rw [sub_nonneg] -- and we switch back to reach the tautology a ≤ b ↔ a ≤ b

/-
Let's prove a variation
-/

example {a b : ℝ} (c : ℝ) : a + c ≤ b + c ↔ a ≤ b := by
  sorry

/-
The above lemma is already in the mathematical library, under the name `add_le_add_iff_right`:

`add_le_add_iff_right (c : ℝ) : a + c ≤ b + c ↔ a ≤ b`

This can be read as: "`add_le_add_iff_right` is a function that will take as input a real
number `c` and will output a proof of `a + c ≤ b + c ↔ a ≤ b`". Here is an example where this lemma
is used.
-/

example {a b : ℝ}  (ha : 0 ≤ a) : b ≤ a + b := by
  calc
    b = 0 + b := by ring
    _ ≤ a + b := by rw [add_le_add_iff_right b] ; exact ha

/-
## Using equivalences as pairs of implications

The second line in the above proof is a bit silly: we use statement rewriting to reduce
the goal to our assumption `ha`, but it would be more natural to see the equivalence as a
double implication. We can access the two implications of an equivalence `h : P ↔ Q` as
`h.1 : P → Q` and `h.2 : Q → P`. This allows us to rewrite the above proof as:
-/

example {a b : ℝ}  (ha : 0 ≤ a) : b ≤ a + b := by
  calc
    b = 0 + b := by ring
    _ ≤ a + b := by exact (add_le_add_iff_right b).2 ha


/- Let's do a variant using `add_le_add_iff_left a : a + b ≤ a + c ↔ b ≤ c` instead. -/

example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by
  sorry

/-
Important note: in the previous exercises, we used lemmas like `add_le_add_iff_left` as
elementary examples to manipulate equivalences. But invoking those lemmas by hand when
working on interesting mathematics would be awfully tedious. There are tactics
whose job is to do these things automatically, but this is not the topic of this file.


## Proving equivalences

In order to prove an equivalence one can use `rw` until the
goal is the tautology `P ↔ P`, just as one can do with equalities.

One can also separately prove the two implications using the `constructor` tactic.
Below is an example.
If you put your cursor after `constructor`, you will see two goals, one for each direction.
Lean will keep track of the goals for you, making sure you solve all of them.
The "focussing dot" `·` keeps the proof for each goal separate.
-/

example (a b : ℝ) : (a-b)*(a+b) = 0 ↔ a^2 = b^2 := by
  constructor
  · intro h
    calc
      a ^ 2 = b^2 + (a - b) * (a + b)  := by ring
          _ = b^2 + 0                  := by rw [h]
          _ = b^2                      := by ring
  · intro h
    calc
      (a-b)*(a+b) = a^2 - b^2  := by ring
                _ = b^2 - b^2  := by rw [h]
                _ = 0          := by ring


/- You can try it yourself in this exercise. -/

example (a b : ℝ) : a = b ↔ b - a = 0 := by
  sorry

/-
This is the end of this file where you learned how to handle implications and
equivalences. You learned about tactics:
* `intro`
* `apply`
* `have`
* `constructor`
-/

