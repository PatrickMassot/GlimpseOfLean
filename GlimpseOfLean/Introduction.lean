import GlimpseOfLean.Library.Basic

namespace Introduction

/-
# Introduction to this tutorial

If you have a small screen, you can press
`alt-Z` (or `option-Z`) to enable word wrap.

Welcome to this tutorial designed to give you a glimpse of Lean in a couple of hours.

First let us see what a Lean proof looks like, without trying to understand any syntactical
detail yet. You won't have to type anything in this file.

If everything works, you currently see a panel to the right of this text with title
"Lean Infoview", with a message like "No info found."
This panel will start displaying interesting things inside the proof.

First let us review two calculus definitions.
-/

/-- A sequence `u` of real numbers converges to `l` if `∀ ε > 0, ∃ N, ∀ n ≥ N, |u_n - l| ≤ ε`.
This condition will be spelled `seq_limit u l`. -/
def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

/- In the above definition, note that the `n`-th term of the sequence `u` is denoted
simply by `u n`.

Similarly, in the next definition, `f x` is what we would write `f(x)` on paper.
Also note that implication is denoted by a single arrow (we'll explain why later). -/

/-- A function`f : ℝ → ℝ` is continuous at `x₀` if
`∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ ⇒ |f(x) - f(x₀)| ≤ ε`.
This condition will be spelled `continuous_at f x₀`.-/
def continuous_at (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

/-- Now we claim that if `f` is continuous at `x₀` then it is sequentially continuous
at `x₀`: for any sequence `u` converging to `x₀`, the sequence `f ∘ u` converges
to `f x₀`.  -/
example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ) (hu : seq_limit u x₀) (hf : continuous_at f x₀) :
  seq_limit (f ∘ u) (f x₀) := by { -- This `by` keyword marks the beginning of the proof
  -- Put your text cursor here and watch the Lean InfoView panel to the right.
  -- Then move your cursor from line to line in the proof while monitoring the Infoview.

  -- Our goal is to prove that, for any positive `ε`, there exists a natural
  -- number `N` such that, for any natural number `n` at least `N`,
  --  `|f(u_n) - f(x₀)|` is at most `ε`.
  unfold seq_limit
  -- Fix a positive number `ε`.
  intros ε hε
  -- By assumption on `f` applied to this positive `ε`, we get a positive `δ`
  -- such that, for all real number `x`, if `|x - x₀| ≤ δ` then `|f(x) - f(x₀)| ≤ ε` (1).
  obtain ⟨δ, δ_pos, Hf⟩ : ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε := hf ε hε
  -- The assumption on `u` applied to this `δ` gives a natural number `N` such that
  -- for every natural number `n`, if `n ≥ N` then `|u_n - x₀| ≤ δ`   (2).
  obtain ⟨N, Hu⟩ : ∃ N, ∀ n ≥ N, |u n - x₀| ≤ δ := hu δ δ_pos
  -- Let's prove `N` is suitable.
  use N
  -- Fix `n` which is at least `N`. Let's prove `|f(u_n) - f(x₀)| ≤ ε`.
  intros n hn
  -- Thanks to (1) applied to `u_n`, it suffices to prove that `|u_n - x₀| ≤ δ`.
  apply Hf
  -- This follows from property (2) and our assumption on `n`.
  exact Hu n hn
  -- This finishes the proof!
  }

/-
Now that this proof is over, you can use the file explorer to the
left of this panel to open the file `Exercises > 01Rewriting.lean`.
-/