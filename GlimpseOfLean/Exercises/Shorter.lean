import GlimpseOfLean.Library.Short

/- # A shorter Glimpse of Lean

This file is the short track of the Glimpse of Lean project. It is meant for people
who want to spend two hours discovering Lean. The hope is that two hours are
enough to reach at least the first exercises about limits of sequences of real numbers.
If you go faster or have a bit more time, you can try to do all those exercises.

Of course the proofs are not always the most idiomatic ones since we aim to keep
the amount of things to explain very low, while still giving a glimpse of how Lean
sees mathematical proofs.

Every command that is typed to make progress in the proof is called a “tactic”.
We will learn about a dozen of them. For each tactic, we will see a couple of
examples and then you will have exercises to do. The goal of each exercise is
to replace the word `sorry` by a sequence of tactics that bring Lean to report
there are no remaining goal, without reporting any error along the way.
-/

/- ## Computing

We start with basic computations using real numbers. We could play the micro-management
game invoking properties like commutatitivity and associativity of addition.
But we can also ask Lean to take care of any proof that only uses those properties
using the `ring` tactic.
By “only those properties” we mean in particular it won’t use any assumption
specific to the proof at hand.

The word `ring` refers to the abstract mathematical definition that encapsulates the
basic properties of addition, subtraction and multiplication. Knowing about this
abstract algebra is not required here.
-/

example (a b : ℝ) : (a+b)^2 = a^2 + 2*a*b + b^2 := by
  ring

/-
Now it’s your turn: replace the word sorry with the relevant tactic to
finish the exercise.
-/

example (a b : ℝ) : (a+b)*(a-b) = a^2 - b^2 := by
  sorry

/-
Our next tactic is the `congr` tactic (`congr` stands for “congruence”).
It tries to prove equalities by comparing both sides and creating new goals each time it
sees some mismatch.
-/

example (a b : ℝ) (f : ℝ → ℝ) : f ((a+b)^2) = f (a^2 + 2*a*b + b^2) := by
  congr
  -- `congr` recognized the pattern `f _ = f _` and created a new goal
  -- about the mismatching part, namely the arguments supplied to `f`.
  ring

/-
Try it on the next example.
-/

example (a b : ℝ) (f : ℝ → ℝ) : f ((a+b)^2 - 2*a*b) = f (a^2 + b^2) := by
  sorry

/-
When there are several mismatches, `congr` creates several goals.
Sometimes it gets over-enthusastic and matches “too much”. For instance, if the goal
is `f (a+b) = f (b+a)` then `congr` will recognize the common pattern
`f (_ + _) = f (_ + _)` and create two goals: `a = b` and `b = a`.
This can be controlled in various ways. The most basic one is enough for us: we can limit
the number of function application layers by putting a number after `congr`.
In the example the two functions that are applied are `f` and addition, and we want to
go only through the application of `f`.
-/

example (a b : ℝ) (f : ℝ → ℝ) : f (a + b) = f (b + a) := by
  congr 1 -- try removing that 1 or increasing it to see the issue.
  ring

/-
Actually `congr` does more than finding mismatches, it also try to resolve them
using assumptions. In the next example, `congr` creates the goal `a + b = c` by
matching, and then immediately proves it by noticing and using assumption `h`.
-/

example (a b c : ℝ) (h : a + b = c) (f : ℝ → ℝ) : f (a + b) = f c := by
  congr

/-
The tactics `ring` and `congr` are the basic tools we will use to compute.
But sometimes we need to chain several computation steps.
This is the job of the `calc` tactic.

In the following example, it helps to carefully consider the tactic state
displayed after each `by` after the `calc` line.
-/

example (a b c d : ℝ) (h : c = b*a - d) (h' : d = a*b) : c = 0 := by
  calc
    c = b*a - d   := by congr
    _ = b*a - a*b := by congr
    _ = 0         := by ring

/-
Note that each `_` stands for the right-hand side of the previous line.
So we are really proving a sequence of equalities, and then the `calc` tactic
takes care of applying transitivity of equality (or equalities and inequalities
when proving inequalities). Each proof in this sequence is introduced by `:= by`.

The indentation rules for `calc` are a bit subtle, especially when there
are other tactics after `calc`. Be careful to always align the `_`.
Aligning the equality signs and the `:=` signs looks nice but is not mandatory.

Laying out those calculation steps and copy-pasting the common pieces can be a
bit tedious on larger examples, but we get help from the calc widget, as can be
seen on the video at

https://www.imo.universite-paris-saclay.fr/~patrick.massot/calc_widget.webm

As you can see there, the `calc?` tactic propose to create a one-line computation,
and then putting the cursor after `:= by` allows to select subterms to replace in
a new calculation step.

Note that subterm selection is done using Shift-click.
There is no “click and move the cursor and then stop clicking”.
This is different from regular selection of text in your editor or browser.

Note that in order to do this computation with the tools presented here, you need
to carefully plan your path to make sure `a` and `b+c` appear somewhere
so that `congr` can use the assumptions. If you find this puzzle frustrating then
don’t hesitate to skip this exercise.

Note also that `lean` is perfectly capable of solving the whole exercise in one
command —namely `grind`— using a Gröbner basis algorithm. But here the point is to
pratice doing computations by hand.
-/

example (a b c : ℝ) (h : a = -b) (h' : b + c = 0) : b*(a - c) = 0 := by
  sorry

/-
We can also handle inequalities using `gcongr` (which stands for “generalized congruence”)
instead of `congr`.
-/

example (a b : ℝ) (h : a ≤ 2*b) : a + b ≤ 3*b := by
  calc
    a + b ≤ 2*b + b := by gcongr
    _     = 3*b     := by ring

example (a b : ℝ) (h : b ≤ a) : a + b ≤ 2*a := by
  sorry

/-
The last tactic you will use in computation is the simplifier `simp`. It will
repeatedly apply a number of lemmas that are marked as simplification lemmas.
For instance the proof below simplifies `x - x` to `0` and then `|0|` to `0`.
-/

example (x : ℝ) : |x - x| = 0 := by
  simp


/- ## Universal quantifiers and implications

Now let’s learn about the `∀` quantifier.

Let `P` be a predicate on a type `X`. This means for every mathematical
object `x` with type `X`, we get a mathematical statement `P x`.

Lean sees a proof `h` of `∀ x, P x` as a function sending any `x : X` to
a proof `h x` of `P x`.
This already explains the main way to use an assumption or lemma which
starts with a `∀`: we can simply feed it an element of the relevant `X`.

Note we don't need to spell out `X` in the expression `∀ x, P x`
as long as the type of `P` is clear to Lean, which can then infer the type of `x`.

Let's define a predicate to play with `∀`. In that example we have a function
`f : ℝ → ℝ` at hand, and `X = ℝ` (this value of `X` is inferred from the fact
that we feed `x` to `f` which goes from `ℝ` to `ℝ`).
-/

def even_fun (f : ℝ → ℝ) := ∀ x, f (-x) = f x

/-
In the above definition, note how there is no parentheses in `f x`.
This is how Lean denotes function application. In `f (-x)` there are parentheses
to prevent Lean from seeing a subtraction of `f` and `x` (which would make no sense).
Also be careful the space between `f` and `(-x)` is mandatory.

The `apply` tactic can be used to specialize universally quantified statements.
-/

example (f : ℝ → ℝ) (hf : even_fun f) : f (-3) = f 3 := by
  apply hf 3

/-
Fortunately, Lean is willing to work for us, so we can leave out the `3` and
let the `apply` tactic compare the goal with the assumption
and decide to specialize it to `x = 3`.
-/

example (f : ℝ → ℝ) (hf : even_fun f) : f (-3) = f 3 := by
  apply hf

/-
In the following exercise, you get to choose whether you want help from Lean
or do all the work.
-/
example (f : ℝ → ℝ) (hf : even_fun f) : f (-5) = f 5 := by
  sorry

/-
This was about using a `∀`. Let us now see how to prove a `∀`.

In order to prove `∀ x, P x`, we use `intro x₀` to fix an arbitrary object
with type `X`, and call it `x₀` (`intro` stands for “introduce”).
Note we don’t have to use the letter `x₀`, any name will work.

We will prove that the real cosine function is even. After introducing some `x₀`,
the simplifier tactic can finish the proof. Remember to carefully inspect the goal
at the beginning of each line.
-/

open Real in -- this line insists that we mean real cos, not the complex numbers one.
example : even_fun cos := by
  intro x₀
  simp

/-
In order to get slightly more interesting examples, we will both use and prove
some universally quantified statements.

In the next proof, we also take the opportunity to introduce the
`unfold` tactic, which simply unfolds definitions. Here this is purely
for didactic reason, Lean doesn't need those `unfold` invocations.
-/

example (f g : ℝ → ℝ) (hf : even_fun f) (hg : even_fun g) : even_fun (f + g) := by
  -- Our assumption on that f is even means ∀ x, f (-x) = f x
  unfold even_fun at hf -- note how `hf` changes after this line
  -- and the same for g
  unfold even_fun at hg
  -- We need to prove ∀ x, (f+g)(-x) = (f+g)(x)
  unfold even_fun
  -- Let x₀ be any real number
  intro x₀
  -- and let's compute
  calc
    (f + g) (-x₀) = f (-x₀) + g (-x₀)  := by simp
    _             = f x₀ + g (-x₀)     := by congr 1; apply hf
  -- put your cursor between `;` and `apply` in the previous line to see the intermediate goal
    _             = f x₀ + g x₀        := by congr 1; apply hg
    _             = (f + g) x₀         := by simp


/-
Tactics like `congr` and `ring` will not unfold definitions that appear in the goal.
This is why the first computation line is necessary, although it only unfolds a definition.
The last line is not necessary however, since it only proves
something that is true by definition, and is not followed by any other tactic.

Also note that `congr` can generate several goals so we don’t have to call it twice.

Hence we can compress the above proof to:
-/

example (f g : ℝ → ℝ)  (hf : even_fun f) (hg : even_fun g) : even_fun (f + g) := by
  intro x₀
  calc
    (f + g) (-x₀) = f (-x₀) + g (-x₀)  := by simp
    _             = f x₀ + g x₀        := by congr 1; apply hf; apply hg

/-
If you would rather uncompress the proof, you can use the `specialize` tactic to
specialize a universally quantified assumption before using it.
-/

example (f g : ℝ → ℝ) (hf : even_fun f) (hg : even_fun g) : even_fun (f + g) := by
  -- Let x₀ be any real number
  intro x₀
  specialize hf x₀ -- hf is now only about the x₀ we just introduced
  specialize hg x₀ -- hg is now only about the x₀ we just introduced
  -- and let's compute
  -- (note how `congr` now finds assumptions finishing those steps)
  calc
    (f + g) (-x₀) = f (-x₀) + g (-x₀)  := by simp
    _             = f x₀ + g (-x₀)     := by congr
    _             = f x₀ + g x₀        := by congr
    _             = (f + g) x₀         := by simp

/-
All exercises in this file can be done without introducting any intermediate statements.
But experience shows this can be frustrating to some people. If you feel the need
to state something that is not the current goal, you can use
```
have my_statement_name : statement := by
   indented proof
```
as in the following example.
-/

example (f g : ℝ → ℝ) (hf : even_fun f) (hg : even_fun g) : even_fun (f + g) := by
  -- Let x₀ be any real number
  intro x₀
  -- We now record some useful facts.
  have hfx₀ : f (-x₀) = f x₀ := by
    apply hf
  have hgx₀ : g (-x₀) = g x₀ := by
    apply hg
  -- and let's compute
  -- (note how `congr` now finds assumptions finishing those steps)
  calc
    (f + g) (-x₀) = f (-x₀) + g (-x₀)  := by simp
    _             = f x₀ + g (-x₀)     := by congr
    _             = f x₀ + g x₀        := by congr
    _             = (f + g) x₀         := by simp


/-
Now let's practice. If you need to learn how to type a unicode symbol, you can
put your mouse cursor above the symbol and wait for one second.
Recall you can set a depth limit in `congr` by giving it a number as in `congr 1`.

Note also that you can call your arbitrary real number `x` instead of `x₀` if
you want to save some typing. We called it `x₀` only to emphasize it doesn’t
need to be the same notation as in the statement.
-/

example (f g : ℝ → ℝ) (hf : even_fun f) : even_fun (g ∘ f) := by
  sorry

/-
Let's now combine the universal quantifier with implication.

In the next definitions, note how `∀ x₁, ∀ x₂, ...` is abbreviated to `∀ x₁ x₂, ...`.
-/

def non_decreasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≤ f x₂

def non_increasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≥ f x₂

/-
Note how Lean uses a single arrow `→` to denote implication. This is the same arrow
as in `f : ℝ → ℝ`. Indeed Lean sees a proof of the implication `P → Q` as a
function from proofs of `P` to proofs of `Q`.

So an assumption `hf : non_decreasing f` is a function that takes as input two numbers
and a inequality between them and outputs an inequality between their images under `f`.
-/

example (f : ℝ → ℝ) (hf : non_decreasing f) (x₁ x₂ : ℝ) (hx : x₁ ≤ x₂) : f x₁ ≤ f x₂ := by
  apply hf x₁ x₂ hx

/-
We can ask Lean to work more for us, as in the following example:
-/

example (f : ℝ → ℝ) (hf : non_decreasing f) (x₁ x₂ : ℝ) (hx : x₁ ≤ x₂) : f x₁ ≤ f x₂ := by
  apply hf -- Lean compares the goal with the assumption `hf`. It recognizes that `hf`
           -- needs to be specialized to the numbers `x₁` and `x₂` that are given, to get
           -- the implication `x₁ ≤ x₂ → f x₁ ≤ f x₂` and then asks for a proof of the
           -- premise `x₁ ≤ x₂`
  apply hx -- Our assumption hx is such a proof

/-
Note that the tactic `apply` does not mean anything vague like “make something
of that expression somehow”. It asks for an input that is either a full proof
as in the first example, or a proof of statement involving universal
quantifiers and implications in front of some statement that can be specialized
to the current goal (as in the previous example).

In this very simple example, we did not gain much. Now compare the following
two proofs of the same statement.
-/

example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by
  intro x₁ x₂ hx -- Note how `intro` is also introducing the assumption `hx : x₁ ≤ x₂`
  apply hg (f x₁) (f x₂) (hf x₁ x₂ hx)

example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by
  intro x₁ x₂ hx
  apply hg
  apply hf
  apply hx

/-
Take some time to understand how, in the second proof, Lean saves us the
trouble of finding the relevant pairs of numbers and also nicely cuts the proof
into pieces. You can choose your way in the following variation.
-/

example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_increasing g) :
    non_increasing (g ∘ f) := by
  sorry

/-
At this stage you should feel that such a proof actually doesn’t require any
thinking at all. And indeed Lean can easily handle the full proof in one tactic
(but we won’t need this here).

We can also use the `specialize` tactic to feed arguments to an assumption
before using it, as we saw with the example of even functions.
-/

example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g + f) := by
  intro x₁ x₂ h
  specialize hf x₁ x₂ h
  specialize hg x₁ x₂ h
  calc
    (g + f) x₁ = g x₁ + f x₁ := by simp
    _          ≤ g x₂ + f x₂ := by gcongr
    _          = (g + f) x₂  := by simp


/- # Finding lemmas

Lean’s mathematical library contains many useful facts, and remembering all of
them by name is infeasible. We already saw the simplifier tactic `simp` which
applies many lemmas without using their names.

Use `simp` to prove the following. Note that `X : Set ℝ` means that `X` is a
set containing (only) real numbers. -/

example (x : ℝ) (X Y : Set ℝ) (hx : x ∈ X) : x ∈ (X ∩ Y) ∪ (X \ Y) := by
  sorry

/-
The `apply?` tactic will find lemmas from the library and tell you their names.
It creates a suggestion below the goal display. You can click on this suggestion
to edit your code.
Use `apply?` to find the lemma that every continuous function with compact support
has a global minimum. -/

example (f : ℝ → ℝ) (hf : Continuous f) (h2f : HasCompactSupport f) : ∃ x, ∀ y, f x ≤ f y := by
  sorry

/- ## Existential quantifiers

In order to prove `∃ x, P x`, we give some `x₀` that works with `use x₀` and
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

The examples will use divisibility in `ℤ` (beware the `∣` symbol which is
not ASCII but a unicode symbol). The angle brackets appearing after the
word `with` are also unicode symbols.
If your keyboard is not configured to directly type those symbols, you can
put your mouse cursor above the symbol and wait for one second to see how
to type them in this editor.

-/

example (a b c : ℤ) (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c := by
  rcases h₁ with ⟨k, hk⟩ -- we fix some `k` such that `b = a * k`
  rcases h₂ with ⟨l, hl⟩ -- we fix some `l` such that `c = b * l`
  -- Since `a ∣ c` means `∃ k, c = a*k`, we need the `use` tactic.
  use k*l
  calc
    c = b*l     := by congr
    _ = (a*k)*l := by congr
    _ = a*(k*l) := by ring

example (a b c : ℤ) (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b + c := by
  sorry

/-
## Conjunctions

We now explain how to handle one more logical gadget: conjunction.

Given two statements `P` and `Q`, the conjunction `P ∧ Q` is the statement that
`P` and `Q` are both true (`∧` is sometimes called the “logical and”).

In order to prove `P ∧ Q` we use the `constructor` tactic that splits the goal
into proving `P` and then proving `Q`.

In order to use a proof `h` of `P ∧ Q`, we use `h.1` to get a proof of `P`
and `h.2` to get a proof of `Q`. We can also use `rcases h with ⟨hP, hQ⟩` to
get `hP : P` and `hQ : Q`.

Let us see both in action in a very basic logic proof: let us deduce `Q ∧ P`
from `P ∧ Q`.
-/

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  constructor
  apply h.2
  apply h.1

/-
## Limits

We learned enough tactics to manipulate a definition involving both kinds of quantifiers:
limits of sequences of real numbers.

-/

/-- A sequence `u` converges to a limit `l` if the following holds. -/
def seq_limit (u : ℕ → ℝ) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

/-
Let’s see an example manipulating this definition and using a lot of the tactics
we’ve seen above: if `u` is constant with value `l` then `u` tends to `l`.

Remember `apply?` can find lemmas whose name you don’t want to remember, such as
the lemma saying that positive implies non-negative. -/
example (h : ∀ n, u n = l) : seq_limit u l := by
  intro ε ε_pos
  use 0
  intro n hn
  calc |u n - l| = |l - l| := by congr; apply h
    _            = 0       := by simp
    _            ≤ ε       := by apply?

/- When dealing with absolute values, we'll use the lemma:

`abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y`

When dealing with max, we’ll use

`ge_max_iff (p q r) : r ≥ max p q ↔ r ≥ p ∧ r ≥ q`

The way we will use those lemmas is with the rewriting command
`rw`. Let's see an example.
In that example, we kept `apply?` instead of accepting its suggestions in order to emphasize
there is no need to remember those lemma names.
Note also how we can use `by` anywhere to start proving something using tactics. In the example
below, we use it to prove `ε/2 > 0` from our assumption `ε > 0`.
-/

-- If `u` tends to `l` and `v` tends `l'` then `u+v` tends to `l+l'`
example (hu : seq_limit u l) (hv : seq_limit v l') :
    seq_limit (u + v) (l + l') := by
  intro ε ε_pos
  rcases hu (ε/2) (by apply?) with ⟨N₁, hN₁⟩
  rcases hv (ε/2) (by apply?) with ⟨N₂, hN₂⟩
  use max N₁ N₂
  intro n hn
  rw [ge_max_iff] at hn -- Note how hn changes from `n ≥ max N₁ N₂` to `n ≥ N₁ ∧ n ≥ N₂`
  specialize hN₁ n hn.1
  specialize hN₂ n hn.2
  calc
    |(u + v) n - (l + l')| = |u n + v n - (l + l')|   := by simp
    _ = |(u n - l) + (v n - l')|                      := by congr; ring
    _ ≤ |u n - l| + |v n - l'|                        := by apply?
    _ ≤ ε/2 + ε/2                                     := by gcongr
    _ = ε                                             := by simp


/- Let's do something similar: the squeezing theorem using both `ge_max_iff` and `abs_le`.
You will probably want to rewrite using `abs_le` in several assumptions as well as in the
goal. You can use `rw [abs_le] at *` for this. -/
example (hu : seq_limit u l) (hw : seq_limit w l) (h : ∀ n, u n ≤ v n) (h' : ∀ n, v n ≤ w n) :
    seq_limit v l := by
  sorry


/- In the next exercise, we'll use

`eq_of_abs_sub_le_all (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y`

as the first step.
-/

-- A sequence admits at most one limit. You will be able to use that lemma in the following
-- exercises.
lemma uniq_limit (hl : seq_limit u l) (hl' : seq_limit u l') : l = l' := by
  apply eq_of_abs_sub_le_all
  sorry

/-

## Subsequences

We will now play with subsequences.

The new definition we will use is that `φ : ℕ → ℕ` is an extraction
if it is (strictly) increasing.
-/

def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m

/-
In the following, `φ` will always denote a function from `ℕ` to `ℕ`.

The next lemma is proved by an easy induction, but we haven't seen induction
in this tutorial. If you did the natural number game then you can delete
the proof below and try to reconstruct it. Otherwise you can simply take a quick look
at how proofs by induction look like (but we won’t need any other one here).
-/
/-- An extraction is greater than id -/
lemma id_le_extraction' : extraction φ → ∀ n, n ≤ φ n := by
  intro hyp n
  induction n with
  | zero =>  apply?
  | succ n ih => exact Nat.succ_le_of_lt (by
      calc n ≤ φ n := ih
        _    < φ (n + 1) := by apply hyp; apply?)

/-
In the exercise, we use `∃ n ≥ N, ...` which is the abbreviation of
`∃ n, n ≥ N ∧ ...`.

Don’t forget to move the cursor around to see what each `apply?` is proving.
-/

/-- Extractions take arbitrarily large values for arbitrarily large
inputs. -/
lemma extraction_ge : extraction φ → ∀ N N', ∃ n ≥ N', φ n ≥ N := by
  sorry

/-- A real number `a` is a cluster point of a sequence `u`
if `u` has a subsequence converging to `a`. -/
def cluster_point (u : ℕ → ℝ) (a : ℝ) := ∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a

/-- If `a` is a cluster point of `u` then there are values of
`u` arbitrarily close to `a` for arbitrarily large input. -/
lemma near_cluster :
  cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε := by
  sorry


/-- If `u` tends to `l` then its subsequences tend to `l`. -/
lemma subseq_tendsto_of_tendsto' (h : seq_limit u l) (hφ : extraction φ) :
  seq_limit (u ∘ φ) l := by
  sorry

/-- If `u` tends to `l` all its cluster points are equal to `l`. -/
lemma cluster_limit (hl : seq_limit u l) (ha : cluster_point u a) : a = l := by
  sorry

/-- `u` is a Cauchy sequence if its values get arbitrarily close for large
enough inputs. -/
def CauchySequence (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

example : (∃ l, seq_limit u l) → CauchySequence u := by
  sorry


