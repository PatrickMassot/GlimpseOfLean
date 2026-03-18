/- We need some simple Lean background definitions to get the ball rolling.
Namely, we will need some basic ring definitions (like the definition of an Ideal.)-/
import GlimpseOfLean.Library.Basic
import GlimpseOfLean.Library.Ring


/-- The definition of the limit of a real valued sequence u(n).-/
def seq_limit (u : ℕ → ℝ) (l : ℝ)
-- Notice the slight change! In LEAN we view u(n) as a function,
-- from indices to values in ℝ.
  := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε
  -- Otherwise this is the standard definition.


/- Example 1 - Some intro analysis-/
/- If u is constant with value l then u tends to l.-/
example (h : ∀ n, u n = l) : seq_limit u l := by
  sorry

/- Example 2 - The intersection of ideals is an ideal. -/

variable {R : Type*} [CommRing R]

/-- The intersection of ideals is an ideal. -/
def Ideal.inter' (I J : Ideal R) : Ideal R where
  -- Go command click on Ideal to see what it means to be
  -- an ideal of a ring R in Lean!
  carrier := I ∩ J
  add_mem' := by
    sorry
  zero_mem' := by
    sorry
  smul_mem' := by
    sorry
