import GlimpseOfLean.Library.Basic
import Mathlib.Data.Complex.Exponential
open Real

/-
# Computing

## The ring tactic

One of the earliest kind of proofs one encounters while learning mathematics is proving by
a calculation. It may not sound like a proof, but this is actually using lemmas expressing
properties of operations on numbers. Of course we usually don't want to invoke those explicitly
so mathlib has a tactic `ring` taking care of proving equalities that follow by applying
the properties of all commutative rings.
-/


example (a b c : ℝ) : (a * b) * c = b * (a * c) := by
  ring

/- It's your turn, replace the word sorry below by a proof. In this case the proof is just `ring`.
After you prove something, you will see a small "No goals" message, which is the indication that
your proof is finished.
-/

example (a b : ℝ) : (a+b)^2 = a^2 + 2*a*b + b^2 := by
  -- sorry
  ring
  -- sorry

/- In the first example above, take a closer look at where Lean displays parentheses.
The `ring` tactic certainly knows about associativity of multiplication, but sometimes
it is useful to understand that binary operation really are binary and an expression like
`a*b*c` is read as `(a*b)*c` by Lean and the fact that this is equal to `a*(b*c)` is a
lemma that is used by the `ring` tactic when needed.
-/


/-
## The rewriting tactic

Let us now see how to compute using assumptions relating the involved numbers.
This uses the fundamental property of equality: if two
mathematical objects A and B are equal then, in any statement involving A, one can replace A
by B. This operation is called rewriting, and the basic Lean tactic for this is `rw`.
Carefully step through the proof below and try to understand what is happening.
-/
example (a b c d e : ℝ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by
  rw [h]
  rw [h']
  ring

/-
Note the `rw` tactic changes the current goal. After the first line of the above proof,
the new goal is `b + c + e = d + c`. So you can read this first proof step as saying:
"I wanted to prove, `a + e = d + c` but, since assumption `h` tells me `a = b + c`,
it suffices to prove `b + c + e = d + c`."

The `rw` tactic needs to be told every rewrite step. Later on we will see more powerful tactics
that can automate the tedious steps for you.

One can actually do several rewritings in one command.
-/
example (a b c d e : ℝ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by
  rw [h, h']
  ring

/-
Note that putting your cursor between `h` and`h'` shows you the intermediate proof state.

Note also the subtle background color change in the tactic state that show you in green
what is new and in red what is about to change.

Now try it yourself. Note that ring can still do calculations,
but it doesn't use the assumptions `h` and `h'`
-/

example (a b c d : ℝ) (h : b = d + d) (h' : a = b + c) : a + b = c + 4 * d := by
  -- sorry
  rw [h', h]
  ring
  -- sorry

/- ## Rewriting with a lemma

In the previous examples, we rewrote the goal using a local assumption. But we can
also use lemmas. For instance let us prove a lemma about exponentiation.
Since `ring` only knows how to prove things from the axioms of rings,
it doesn't know how to work with exponentiation.
For the following lemma, we will rewrite twice with the lemma
`exp_add x y`, which is a proof that `exp(x+y) = exp(x) * exp(y)`.
-/
example (a b c : ℝ) : exp (a + b + c) = exp a * exp b * exp c := by
  rw [exp_add (a + b) c]
  rw [exp_add a b]

/-
Note also that after the second `rw` the goal becomes
`exp a * exp b * exp c = exp a * exp b * exp c` and Lean immediately declares the proof is done.

If we don't provide arguments to the lemmas, Lean will rewrite the first matching
subexpression. In our example this is good enough. Sometimes more control is needed.
-/
example (a b c : ℝ) : exp (a + b + c) = exp a * exp b * exp c := by
  rw [exp_add, exp_add]

/-
Let's do an exercise, where you also have to use
`exp_sub x y : exp(x-y) = exp(x) / exp(y)` and `exp_zero : exp 0 = 1`.

Recall that `a + b - c` means `(a + b) - c`.

You can either use `ring` or rewrite with `mul_one x : x * 1 = x` to simplify the denominator on the
right-hand side.
-/

example (a b c : ℝ) : exp (a + b - c) = (exp a * exp b) / (exp c * exp 0) := by
  -- sorry
  rw [exp_sub, exp_add, exp_zero, mul_one]
  -- sorry

/-
## Rewriting from right to left

Since equality is a symmetric relation, we can also replace the right-hand side of an
equality by the left-hand side using `←` as in the following example.
-/
example (a b c d e : ℝ) (h : a = b + c) (h' : a + e = d + c) : b + c + e = d + c := by
  rw [← h, h']

/-
Whenever you see in a Lean file a symbol that you don't see on your keyboard, such as ←,
you can put your mouse cursor above it and learn from a tooltip how to type it.
In the case of ←, you can type it by typing "\l ", so backslash-l-space.

Note this rewriting from right to left story is all about sides in the equality you want to
*use*, not about sides in what you want to *prove*. The `rw [← h]` in the previous example
replaced the right-hand side by the left-hand side, so it looked for `b + c` in the current
goal and replaced it with `a`.
-/

example (a b c d : ℝ) (h : a = b + b) (h' : b = c) (h'' : a = d) : b + c = d := by
  -- sorry
  rw [← h', ← h, ← h'']
  -- sorry

/- ## Rewriting in a local assumption

We can also perform rewriting in an assumption of the local context, using for instance
  `rw [exp_add x y] at h`
in order to replace `exp(x + y)` by `exp(x) * exp(y)` in assumption `h`.

The `exact` tactic allows you to give an explicit proof term to prove the current goal.
-/

example (a b c d : ℝ) (h : c = d*a + b) (h' : b = d) : c = d*a + d := by
  rw [h'] at h
  -- Our assumption `h` is now exactly what we have to prove
  exact h

/- ## Calculation layout using calc

What is written in the above example is very far away from what we would write on
paper. Let's now see how to get a more natural layout (and also return to using `ring`
instead of explicit lemma invocations).
After each `:=` below, the goal is to prove equality with the preceding line
(or the left-hand on the first line).
Carefully check you understand this by putting your cursor after each `by` and looking
at the tactic state.
-/

example (a b c d : ℝ) (h : c = b*a - d) (h' : d = a*b) : c = 0 := by
  calc
    c = b*a - d   := by rw [h]
    _ = b*a - a*b := by rw [h']
    _ = 0         := by ring

/-
Let's do some exercises using `calc`.
-/

example (a b c : ℝ) (h : a = b + c) : exp (2 * a) = (exp b) ^ 2 * (exp c) ^ 2 := by
  calc
    exp (2 * a) = exp (2 * (b + c))                 := by /- inline sorry -/rw [h]/- inline sorry -/
              _ = exp ((b + b) + (c + c))           := by /- inline sorry -/ring/- inline sorry -/
              _ = exp (b + b) * exp (c + c)         := by /- inline sorry -/rw [exp_add]/- inline sorry -/
              _ = (exp b * exp b) * (exp c * exp c) := by /- inline sorry -/rw [exp_add, exp_add]/- inline sorry -/
              _ = (exp b) ^ 2 * (exp c)^2           := by /- inline sorry -/ring/- inline sorry -/

/-
From a practical point of view, when writing such a proof, it is sometimes convenient to:
* pause the tactic state view update in VScode by clicking the Pause icon button
  in the top right corner of the Lean Infoview panel.
* write the full calculation, ending each line with ":= ?_"
* resume tactic state update by clicking the Play icon button and fill in proofs.

The underscores should be placed below the left-hand-side of the first line below the `calc`.
Aligning the equal signs and `:=` signs is not necessary but looks tidy.
-/

example (a b c d : ℝ) (h : c = d*a + b) (h' : b = a*d) : c = 2*a*d := by
  -- sorry
  calc
    c = d*a + b   := by rw [h]
    _ = d*a + a*d := by rw [h']
    _ = 2*a*d     := by ring
  -- sorry

/-
Congratulations, this is the end of your first exercise file! You've seen what typing
a Lean proof looks like and have learned about the following tactics:
* `ring`
* `rw`
* `exact`
* `calc`
-/
