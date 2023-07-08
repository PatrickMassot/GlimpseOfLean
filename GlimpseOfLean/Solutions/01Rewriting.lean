import Mathlib.Data.Real.Basic

/-
# Computing

## The ring tactic

One of the earliest kind of proofs one encounters while learning mathematics is proving by
a calculation. It may not sound like a proof, but this is actually using lemmas expressing
properties of operations on numbers. Of course we usually don't want to invoke those explicitly
so mathlib has a tactic `ring` taking care of proving equalities that follow by applying
the properties of all commutative rings.
-/


example (a b c : ℝ) : a * b * c = b * a * c := by
  ring

/- It's your turn, replace the word sorry below by a proof. -/

example (a b c : ℝ) : (c * b) * a = b * (a * c) := by
  -- sorry
  ring
  -- sorry

/- In the above two examples, take a closer look at where Lean displays parentheses.
The `ring` tactic certainly knows about associativity of multiplication, but sometimes
it is useful to understand that binary operation really are binary and an expression like
`a*b*c` is read as `(a*b)*c` by Lean and the fact that is equal `a*(b*c)` is a lemma
that is used by the `ring` tactic when needed. Doing the next example by hand from the axioms
of commutative rings would actually be quite tedious.
-/

example (a b : ℝ) : (a + b)^2 = a^2 + 2*a*b + b^2 := by
  -- sorry
  ring
  -- sorry

/-
## The rewriting tactic

Let us now see how to compute using assumptions relating the involved numbers.
This uses the fundamental property of equality: if two
mathematical objects A and B are equal then, in any statement involving A, one can replace A
by B. This operation is called rewriting, and the Lean tactic for this is `rw`.
Carefully step through the proof below and try to understand what is happening.
-/
example (a b c : ℝ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by
  rw [h]
  rw [h']
  ring

/-
Note the `rw` tactic changes the current goal. After the first line of the above proof,
the new goal is `b + c + e = d + c`. So you can read this first proof step as saying:
"I wanted to prove, `a + e = d + c` but, since assumption `h` tells me `a = b + c`,
it suffices to prove `b + c + e = d + c`."

One can actually do several rewritings in one command.
-/
example (a b c : ℝ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by
  rw [h, h']
  ring

/-
Note that putting your cursor between `h` and`h'` shows you the intermediate proof state.

Note also the subtle background color change in the tactic state that show you in green
what is new and in red what is about to change.
-/

/-
## Rewriting from right to left

Since equality is a symmetric relation, we can also replace the right-hand side of an
equality by the left-hand side using `←` as in the following example.
-/
example (a b c : ℝ) (h : a = b + c) (h' : a + e = d + c) : b + c + e = d + c := by
  rw [← h]
  rw [h']

/-
Whenever you see in a Lean file a symbol that you don't see on your keyboard, such as ←,
you can put your mouse cursor above it and learn from a tooltip how to type it.

Note this rewriting from right to left story is all about sides in the equality you want to
*use*, not about sides in what you want to *prove*. The `rw [← h]` goes from right to left in
`h` so it will look for `b + c` in the current goal and replace it with `a`. In our example
`b + c` happens to appear in the left-hand side of the goal but in general the goal does
not even need to be an equality. Note also that after the second `rw` the goal becomes
`d + c = d + c` and Lean immediately declares the proof is done.
-/

example (a b c : ℝ) (h : a = b + c) : (b+c)^2 - c^2 = (a+c)*(a-c) := by
  -- sorry
  rw [← h]
  ring
  -- sorry

/- ## Rewriting usual a lemma

In the previous examples, we rewrote the goal using a local assumption. But we can
also use lemmas. For instance let us prove that `a*b - b*a = 0` the hard way, without
the `ring` tactic but using lemmas `mul_comm` and `sub_self`.
In particular `mul_comm a b` is a proof of `a*b = b*a` and
`sub_self (b*a)` is a proof of `b*a - b*a = 0`.
-/

example (a b : ℝ) : a*b - b*a = 0 := by
  rw [mul_comm a b, sub_self (b*a)]

/-
If we don't provide arguments to the lemmas, Lean will rewrite the first matching
subexpression. In our example this is good enough. Sometimes more control is needed.
-/

example (a b : ℝ) : a*b - b*a = 0 := by
  rw [mul_comm, sub_self]

/-
Let's do an exercise using lemmas `mul_comm`, that we already saw, and
`mul_assoc x y z : (x * y) * z = x * (y * z)`.
-/

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  -- sorry
  rw [← mul_assoc]
  -- "rw mul_comm," doesn't do what we want.
  rw [mul_comm a b]
  rw [mul_assoc]
  -- sorry

/-
Remember this is only for training, Lean knows how to do this alone.
-/

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  ring

/- ## Rewriting in a local assumption

We can also perform rewriting in an assumption of the local context, using for instance
  `rw [mul_comm a b] at hyp`
in order to replace `a*b` by `b*a` in assumption `hyp`.

In the example below, we also use the `exact` tactic, which allows to provide a
direct proof. In this example, the argument is the name of an assumption,
but it could also be a lemma applied to some arguments.
-/

example (a b c d : ℝ) (hyp : c = d*a - b) (hyp' : b = a*d) : c = 0 := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [sub_self] at hyp
  -- Our assumption `hyp` is now exactly what we have to prove
  exact hyp

/- ## Calculation layout using calc

What is written in the above example is very far away from what we would write on
paper. Let's now see how to get a more natural layout (and also return to using `ring`
instead of explicit lemma invocations).
After each `:=` below, the goal is to prove equality with the preceding line
(or the left-hand on the first line).
Carefuly check you understand this by putting your cursor after each `by` and looking
at the tactic state.
-/

example (a b c d : ℝ) (hyp : c = b*a - d) (hyp' : d = a*b) : c = 0 := by
  calc c = b*a - d   := by rw [hyp]
  _      = b*a - a*b := by rw [hyp']
  _      = 0         := by ring


/-
From a practical point of view, when writing such a proof, it is sometimes convenient to:
* pause the tactic state view update in VScode by clicking the Pause icon button
  in the top right corner of the Lean Infoview panel.
* write the full calculation, ending each line with ":= ?_"
* resume tactic state update by clicking the Play icon button and fill in proofs.

Also note that the alignment of the underscores is somewhat flexible but not completely
random. Putting all of them below the c of `calc` is definitely safe. Aligning the equal
signs and `:=` signs is useless but looks tidy.

Let's do another example using this method.
-/

example (a b c d : ℝ) (hyp : c = d*a + b) (hyp' : b = a*d) : c = 2*a*d := by
  -- sorry
  calc c = d*a + b    := by rw [hyp]
  _      = d*a + a*d  := by rw [hyp']
  _      = 2*a*d      := by ring
  -- sorry

/-
Congratulations, this is the end of your first exercise file! You've seen what typing
a Lean proof looks like and have learned about the following tactics:
* `ring`
* `rw`
* `exact`
* `calc`
-/