import GlimpseOfLean.Library.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas

open Function

namespace Forall
/- # Universal quantifiers

In this file, we'll learn about the `∀` quantifier.

Let `P` be a predicate on a type `X`. This means for every mathematical
object `x` with type `X`, we get a mathematical statement `P x`.
In Lean, `P x` has type `Prop`.

Lean sees a proof `h` of `∀ x, P x` as a function sending any `x : X` to
a proof `h x` of `P x`.
This already explains the main way to use an assumption or lemma which
starts with a `∀`.

In order to prove `∀ x, P x`, we use `intro x` to fix an arbitrary object
with type `X`, and call it `x` (`intro` stands for "introduce").

Note also we don't need to give the type of `x` in the expression `∀ x, P x`
as long as the type of `P` is clear to Lean, which can then infer the type of `x`.

Let's define a predicate to play with `∀`.
-/

def even_fun (f : ℝ → ℝ) := ∀ x, f (-x) = f x

/-
In the next proof, we also take the opportunity to introduce the
`unfold` tactic, which simply unfolds definitions. Here this is purely
for didactic reason, Lean doesn't need those `unfold` invocations.
We will also use the `rfl` tactic, which proves equalities that are true
by definition (in a very strong sense), it stands for "reflexivity".
-/

example (f g : ℝ → ℝ) (hf : even_fun f) (hg : even_fun g) : even_fun (f + g) := by
  -- Our assumption that f is even means ∀ x, f (-x) = f x
  unfold even_fun at hf
  -- and the same for g
  unfold even_fun at hg
  -- We need to prove ∀ x, (f+g)(-x) = (f+g)(x)
  unfold even_fun
  -- Let x be any real number
  intro x
  -- and let's compute
  calc
    (f + g) (-x) = f (-x) + g (-x)  := by rfl
               _ = f x + g (-x)     := by rw [hf x]
               _ = f x + g x        := by rw [hg x]
               _ = (f + g) x        := by rfl


/-
Tactics like `apply`, `exact`, `rfl` and `calc` will automatically unfold definitions.
You can test this by deleting the `unfold` lines in the above example.

Tactics like `rw` and `ring` will generally not unfold definitions that appear in the goal.
This is why the first computation line is necessary, although its proof is simply `rfl`.
Before that line, `rw [hf x]` won't find anything like `f (-x)` hence will give up.
The last line is not necessary however, since it only proves
something that is true by definition, and is not followed by a `rw`.

Also, Lean doesn't need to be told that `hf` should be specialized to
`x` before rewriting, exactly as in the first file.

Recall also that `rw` can take a list of expressions to use for
rewriting. For instance `rw [h₁, h₂, h₃]` is equivalent to three
lines `rw [h₁]`, `rw [h₂]` and `rw [h₃]`. Note that you can inspect the tactic
state between those rewrites when reading a proof using this syntax. You
simply need to move the cursor inside the list.

Hence we can compress the above proof to:
-/

example (f g : ℝ → ℝ) : even_fun f → even_fun g → even_fun (f + g) := by
  intro hf hg x
  calc
    (f + g) (-x) = f (-x) + g (-x)  := by rfl
               _ = f x + g x        := by rw [hf, hg]

/-
Now let's practice. Recall that if you need to learn how to type a unicode
symbol you can put your mouse cursor above the symbol and wait for one second.
-/

example (f g : ℝ → ℝ) (hf : even_fun f) : even_fun (g ∘ f) := by
  sorry

/-
Let's have more quantifiers, and play with forward and backward reasoning.

In the next definitions, note how `∀ x₁, ∀ x₂, ...` is abbreviated to `∀ x₁ x₂, ...`.
-/

def non_decreasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≤ f x₂

def non_increasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≥ f x₂

/- Let's be very explicit and use forward reasoning first. -/
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by
  -- Let x₁ and x₂ be real numbers such that x₁ ≤ x₂
  intro x₁ x₂ h
  -- Since f is non-decreasing, f x₁ ≤ f x₂.
  have step₁ : f x₁ ≤ f x₂ := by exact hf x₁ x₂ h
  -- Since g is non-decreasing, we then get g (f x₁) ≤ g (f x₂).
  exact hg (f x₁) (f x₂) step₁

/-
In the above proof, note how inconvenient it is to specify `x₁` and `x₂` in `hf x₁ x₂ h` since
they could be inferred from the type of `hf`.
We could have written `hf _ _ h` and Lean would have filled the holes denoted by `_`.
The same remark applies to the last line.

One possible variation on the above proof is to
use the `specialize` tactic to replace `hf` by its specialization to the relevant value.
 -/

example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by
  intro x₁ x₂ h
  specialize hf x₁ x₂ h
  exact hg (f x₁) (f x₂) hf

/-
This `specialize` tactic is mostly useful for exploration, or in preparation for rewriting
in the assumption. One can very often replace its use by using more complicated expressions
directly involving the original assumption, as in the next variation:
-/
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by
  intro x₁ x₂ h
  exact hg (f x₁) (f x₂) (hf x₁ x₂ h)

/-
Let's see how backward reasoning would look like here.
As usual with this style, we use `apply` and enjoy Lean specializing assumptions for us
using so-called unification.
-/

example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by
  -- Let x₁ and x₂ be real numbers such that x₁ ≤ x₂
  intro x₁ x₂ h
  -- We need to prove (g ∘ f) x₁ ≤ (g ∘ f) x₂.
  -- Since g is non-decreasing, it suffices to prove f x₁ ≤ f x₂
  apply hg
  -- which follows from our assumption on f
  apply hf
  -- and on x₁ and x₂
  exact h

example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_increasing g) :
    non_increasing (g ∘ f) := by
  sorry

/- # Finding lemmas

Lean's mathematical library contains many useful facts, and remembering all of
them by name is impossible.
The following exercises teach you two techniques to avoid needing to remember names.
* `simp` will simplify complicated expressions.
* `apply?` will find lemmas from the library.
-/

/- Use `simp` as a first step to prove the following. Note that `X : Set ℝ`
means that `X` is a set containing (only) real numbers. -/
example (x : ℝ) (X Y : Set ℝ) (hx : x ∈ X) : x ∈ (X ∩ Y) ∪ (X \ Y) := by
  sorry

/- Use `apply?` to find the lemma that every continuous function with compact support
has a global minimum. You can click on the suggestion that appears to replace
`apply?` with the tactic it suggested.
-/

example (f : ℝ → ℝ) (hf : Continuous f) (h2f : HasCompactSupport f) : ∃ x, ∀ y, f x ≤ f y := by
  sorry

/-
Note that `apply?` does not only suggest full proofs. It can suggest lemmas that
apply but require to check side conditions. Accepting such a suggestion
will output incomplete proofs using the `refine` tactic.

Note that each suggestion comes with a list of side conditions that would need
to be check. So you need to decide which suggestion to accept depending on what
the side conditions look like. For instance, if the goal is to prove continuity of
a function, one lemma always applies: the lemma saying that any function out of
a discrete topological space is continuous. But it leaves as a side condition
discreteness of the source space. So you should be careful when deciding to
accept this suggestion which can very quickly lead to a dead end.

This is the end of this file where you learned how to handle universal quantifiers.
You learned about tactics:
* `unfold`
* `specialize`
* `simp`
* `apply?`

You now have a choice what to do next. There is one more basic file `04Exists`
about the existential quantifier and conjunctions. You can do that now,
or dive directly in one of the specialized files.
In the latter case, you should come back to `04Exists` if you get stuck on anything with `∃`/`∧`
(where `∧` is the symbol for conjunctions, aka the logical “and” operator).

You can start with specialized files in the `Topics` folder. You have choice between
* `SequenceLimit` (easier, math) if you want to do some elementary calculus.
  For this file it is recommended to do `04Exists` first.
* `Probability` (easier, math) if you want to work with probability measures,
  independent sets, and conditional probability, including Bayes' Theorem.
* `RingTheory` (medium, math) if you want to do a bit a commutative algebra. It starts
  very gently with basics about commutative rings, then introduces ideals and proves
  Nœther’s first isomorphism theorem, and finishes with the Chinese remainder theorem
  in general commutative rings.
* `GaloisAdjunctions` (harder, math) if you want some more abstraction
  and learn how to prove things about adjunctions between complete lattices.
  It ends with a constructor of the product topology and its universal property
  manipulating as few open sets as possible.
* `ClassicalPropositionalLogic` (easier, logic) if you want to learn
  how to do classical propositional logic in Lean.
* `IntuitionisticPropositionalLogic` (harder, logic) if you want a bigger challenge
  and do intuitionistic propositional logic.

Note the two logic files are really for people interested in logic as a goal, not logic
as a tool.
-/

