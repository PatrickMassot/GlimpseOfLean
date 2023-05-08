import Mathlib.Data.Real.Basic

/-
One of the earliest kind of proofs one encounters while learning mathematics is proving by
a calculation. It may not sound like a proof, but this is actually using lemmas expressing
properties of operations on numbers. It also uses the fundamental property of equality: if two
mathematical objects A and B are equal then, in any statement involving A, one can replace A
by B. This operation is called rewriting, and the Lean "tactic" for this is `rw`.

In the following exercises, we will use the following two lemmas:
  `mul_assoc a b c : a * b * c = a * (b * c)`
  `mul_comm a b : a*b = b*a`

Hence the command
  `rw [mul_assoc a b c]`
will replace `a*b*c` by `a*(b*c)` in the current goal.

In order to replace backward, we use
  `rw [← mul_assoc a b c]`
replacing `a*(b*c)` by `a*b*c` in the current goal.

Of course we don't want to constantly invoke those lemmas, and we will eventually introduce
more powerful solutions.
-/

-- Uncomment the following line if you want to see parentheses around subexpressions.
-- set_option pp.parens true



example (a b c : ℝ) : a * b * c = b * a * c := by
  ring

example (a b c : ℝ) : (c * b) * a = b * (a * c) := by
  -- sorry
  ring
  -- sorry


example (a b : ℝ) : (a + b)^2 = a^2 + 2*a*b + b^2 := by
  -- sorry
  ring
  -- sorry


example (a b c : ℝ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by
  -- sorry
  rw [h, h']
  ring
  -- sorry

/-
TODO:
* rewrite backward
* rewrite using a lemma
* rewrite in an assumption
* calc alternating rw and ring
-/

/-
We can also perform rewriting in an assumption of the local context, using for instance
  `rw [mul_comm a b] at hyp`
in order to replace `a*b` by `b*a` in assumption `hyp`.

The next example will use a third lemma:
  `two_mul a : 2*a = a + a`

Also we use the `exact` tactic, which allows to provide a direct proof term.
-/

example (a b c d : ℝ) (hyp : c = d*a + b) (hyp' : b = a*d) : c = 2*a*d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a*d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp -- Our assumption hyp is now exactly what we have to prove

/-
What is written in the above example is very far away from what we would write on
paper. Let's now see how to get a more natural layout.
Inside each pair of curly braces below, the goal is to prove equality with the preceding line.
-/

example (a b c d : ℝ) (hyp : c = d*a + b) (hyp' : b = a*d) : c = 2*a*d := by
  calc c = d*a + b    := by rw [hyp]
       _ = d*a + a*d  := by rw [hyp']
       _ = a*d + a*d  := by rw [mul_comm d a]
       _ = 2*(a*d)    := by rw [two_mul]
       _ = 2*a*d      := by rw [mul_assoc]


/-
Let's note there is no comma at the end of each line of calculation. `calc` is really one
command, and the comma comes only after it's fully done.

From a practical point of view, when writing such a proof, it is convenient to:
* pause the tactic state view update in VScode by clicking the Pause icon button
  in the top right corner of the Lean Goal buffer
* write the full calculation, ending each line with ": by {}"
* resume tactic state update by clicking the Play icon button and fill in proofs between
  curly braces.

Let's do another example using this method and the lemma:
  `sub_self x : x - x = 0`
-/

example (a b c d : ℝ) (hyp : c = b*a - d) (hyp' : d = a*b) : c = 0 := by
  -- sorry
  calc c = b*a - d := by { rw [hyp] }
   _     = b*a - a*b := by { rw [hyp'] }
   _     = a*b - a*b := by { rw [mul_comm a b] }
   _     = 0 := by rw [sub_self (a*b)]
  -- sorry


/-
The preceding proofs have exhausted our supply of "mul_comm" patience. Now it's time
to get the computer to work harder. The `ring` tactic will prove any goal that follows by
applying only the axioms of commutative (semi-)rings, in particular commutativity and
associativity of addition and multiplication, as well as distributivity.

We also note that curly braces are not necessary when we write a single tactic proof, so
let's get rid of them.
-/

example (a b c d : ℝ) (hyp : c = d*a + b) (hyp' : b = a*d) : c = 2*a*d := by
  calc c = d*a + b   := by rw [hyp]
       _ = d*a + a*d := by rw [hyp']
       _ = 2*a*d     := by ring


/-
Of course we can use `ring` outside of `calc`. Let's do the next one in one line.
-/

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  -- sorry
  ring
  -- sorry

/-
This is too much fun. Let's do it again.
-/

example (a b : ℝ) : (a + b) + a = 2*a + b := by
  -- sorry
  ring
  -- sorry
