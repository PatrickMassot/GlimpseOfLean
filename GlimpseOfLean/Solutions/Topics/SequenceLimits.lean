import GlimpseOfLean.Library.Basic

namespace Topics

/-
In this file we manipulate the elementary definition of limits of
sequences of real numbers.
mathlib has a much more general definition of limits, but here
we want to practice using the logical operators and relations
covered in the previous files.

There are many exercises in this file, so do not hesitate to take a
look at the solutions folder if you are stuck, there will be other
exercises.
-/

/-
Before we start on, let us make sure Lean doesn't need so much help to
prove equalities or inequalities that linearly follow from known
equalities and inequalities. This is the job of the linear arithmetic
tactic: `linarith`.
-/

example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by linarith

/-
Let's prove some exercises using `linarith`.
-/

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by
  -- sorry
  linarith
  -- sorry

example (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d := by
  -- sorry
  linarith
  -- sorry

/-
A sequence `u` is a function from `ℕ` to `ℝ`, hence Lean says
`u : ℕ → ℝ`
The definition we'll be using is:
-/

/-- Definition of “u tends to l” -/
def seq_limit (u : ℕ → ℝ) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

/-
Note the use of `∀ ε > 0, _` which is an abbreviation of
`∀ ε, ε > 0 → _ `

In particular, a statement like `h : ∀ ε > 0, _`
can be specialized to a given `ε₀` by
  `specialize h ε₀ hε₀`
where `hε₀` is a proof of `ε₀ > 0`.

Also note that, wherever Lean expects some proof term, we can
start a tactic mode proof using the keyword `by`.
For instance, if the local context contains:

δ : ℝ
δ_pos : δ > 0
h : ∀ ε > 0, _

then we can specialize h to the real number δ/2 using:
  `specialize h (δ/2) (by linarith)`
where `by linarith` will provide the proof of `δ/2 > 0` expected by Lean.
-/

/- If u is constant with value l then u tends to l.
Hint: `simp` can rewrite `|l - l|` to `0` -/
example (h : ∀ n, u n = l) : seq_limit u l := by
  -- sorry
  intros ε ε_pos
  use 0
  intros n _
  rw [h]
  simp
  linarith
  -- sorry


/-
A small user interface remark: you may have noticed in the previous example that
your editor shows a somewhat ghostly `{u l}` after the `example` word.
This text is not actually present in the Lean file, and cannot be edited.
It is displayed as a hint that Lean inferred we wanted to work with some `u` and `l`.
The fact that `u` should be a sequence and `l` a real numbered was inferred because
the announced conclusion was `seq_limit u l`.

The short version of the above paragraph is you can mostly ignore those ghostly
indications and trust your common sense that `u` is a sequence and `l` a limit.
-/

/-
When dealing with absolute values, we'll use lemmas:

`abs_sub_comm (x y : ℝ) : |x - y| = |y - x|`

`abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y`

We will also use variants of the triangle inequality

`abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|`
or
`abs_sub_le  (a c b : ℝ) : |a - b| ≤ |a - c| + |c - b|`
or the primed version:
`abs_sub_le' (a c b : ℝ) : |a - b| ≤ |a - c| + |b - c|`
-/

-- Assume `l > 0`. Then `u` ts to `l` implies `u n ≥ l/2` for large enough `n`
example (h : seq_limit u l) (hl : l > 0) :
    ∃ N, ∀ n ≥ N, u n ≥ l/2 := by
  -- sorry
  rcases h (l/2) (by linarith) with ⟨N, hN⟩
  use N
  intros n hn
  specialize hN n hn
  rw [abs_le] at hN
  linarith
  -- sorry


/-
When dealing with max, you can use

`ge_max_iff (p q r) : r ≥ max p q ↔ r ≥ p ∧ r ≥ q`

`le_max_left p q : p ≤ max p q`

`le_max_right p q : q ≤ max p q`

Let's see an example.
-/

-- If `u` tends to `l` and `v` tends `l'` then `u+v` tends to `l+l'`
example (hu : seq_limit u l) (hv : seq_limit v l') :
    seq_limit (u + v) (l + l') := by
  intros ε ε_pos
  rcases hu (ε/2) (by linarith) with ⟨N₁, hN₁⟩
  rcases hv (ε/2) (by linarith) with ⟨N₂, hN₂⟩
  use max N₁ N₂
  intros n hn
  have : n ≥ N₁ := by exact le_of_max_le_left hn
  rw [ge_max_iff] at hn
  rcases hn with ⟨_hn₁, hn₂⟩
  have fact₁ : |u n - l| ≤ ε/2 := hN₁ n (by linarith)
  have fact₂ : |v n - l'| ≤ ε/2 := hN₂ n (by linarith)
  -- omit
  /-
  -- alternative proof without using `calc`
  simp
  have : |u n + v n - (l + l')| = |(u n - l) + (v n - l')|
  · ring
  rw [this]
  trans |u n - l| + |v n - l'|
  apply abs_add
  linarith [fact₁, fact₂]
  -/
  -- omit
  calc
    |(u + v) n - (l + l')| = |u n + v n - (l + l')|   := rfl
    _ = |(u n - l) + (v n - l')|                      := by ring
    _ ≤ |u n - l| + |v n - l'|                        := by apply abs_add
    _ ≤ ε                                             := by linarith


/- Let's do something similar: the squeezing theorem.
In that example it can help to use the `specialize` tactic (introduced in the file
`03Forall.lean`) so that the `linarith` tactic can pick up the relevant files
from the assumptions.
-/
example (hu : seq_limit u l) (hw : seq_limit w l) (h : ∀ n, u n ≤ v n) (h' : ∀ n, v n ≤ w n) :
    seq_limit v l := by
  -- sorry
  intros ε ε_pos
  rcases hu ε ε_pos with ⟨N, hN⟩
  rcases hw ε ε_pos with ⟨N', hN'⟩
  use max N N'
  intros n hn
  rw [ge_max_iff] at hn
  specialize hN n (by linarith)
  specialize hN' n (by linarith)
  specialize h n
  specialize h' n
  rw [abs_le] at *
  constructor
  -- Here `linarith` can finish, but on paper we would write
  calc
    -ε ≤ u n - l := by linarith
     _ ≤ v n - l := by linarith
  calc
    v n - l ≤ w n - l := by linarith
          _ ≤ ε := by linarith
  -- sorry



/- In the next exercise, we'll use

`eq_of_abs_sub_le_all (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y`

Recall we listed three variations on the triangle inequality at the beginning of this file.
-/

-- A sequence admits at most one limit. You will be able to use that lemma in the following
-- exercises.
lemma unique_limit : seq_limit u l → seq_limit u l' → l = l' := by
  -- sorry
  intros hl hl'
  apply eq_of_abs_sub_le_all
  intros ε ε_pos
  rcases hl (ε/2) (by linarith) with ⟨N, hN⟩
  rcases hl' (ε/2) (by linarith) with ⟨N', hN'⟩
  specialize hN _ (le_max_left N N')
  specialize hN' _ (le_max_right N N')
  calc
    |l - l'| ≤ |l - u (max N N')| + |u (max N N') - l'| := by apply abs_sub_le
           _ = |u (max N N') - l| + |u (max N N') - l'| := by rw [abs_sub_comm]
           _ ≤ ε := by linarith
  -- sorry



/-
Let's now practice deciphering definitions before proving.
-/

def non_decreasing (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

def is_seq_sup (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

example (M : ℝ) (h : is_seq_sup M u) (h' : non_decreasing u) : seq_limit u M := by
  -- sorry
  intros ε ε_pos
  rcases h with ⟨inf_M, sup_M_ep⟩
  rcases sup_M_ep ε ε_pos with ⟨n₀, hn₀⟩
  use n₀
  intros n hn
  rw [abs_le]
  specialize inf_M n
  specialize h' n₀ n hn
  constructor
  · linarith
  · linarith
  -- sorry

/-
We will now play with subsequences.

The new definition we will use is that `φ : ℕ → ℕ` is an extraction
if it is (strictly) increasing.
-/

def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m

/-
In the following, `φ` will always denote a function from `ℕ` to `ℕ`.

The next lemma is proved by an easy induction, but we haven't seen induction
in this tutorial. If you did the natural number game then you can delete
the proof below and try to reconstruct it.
-/
/-- An extraction is greater than id -/
lemma id_le_extraction' : extraction φ → ∀ n, n ≤ φ n := by
  intros hyp n
  induction n with
  | zero =>  exact Nat.zero_le _
  | succ n ih => exact Nat.succ_le_of_lt (by linarith [hyp n (n+1) (by linarith)])


/-
In the exercise, we use `∃ n ≥ N, ...` which is the abbreviation of
`∃ n, n ≥ N ∧ ...`.
-/

/-- Extractions take arbitrarily large values for arbitrarily large
inputs. -/
lemma extraction_ge : extraction φ → ∀ N N', ∃ n ≥ N', φ n ≥ N := by
  -- sorry
  intro h N N'
  use max N N'
  constructor
  apply le_max_right
  calc
    N ≤ max N N' := by apply le_max_left
    _ ≤ φ (max N N') := by apply id_le_extraction' h
  -- sorry

/- A real number `a` is a cluster point of a sequence `u`
if `u` has a subsequence converging to `a`.
-/

def cluster_point (u : ℕ → ℝ) (a : ℝ) := ∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a

/-- If `a` is a cluster point of `u` then there are values of
`u` arbitrarily close to `a` for arbitrarily large input. -/
lemma near_cluster :
  cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε := by
  -- sorry
  intro hyp ε ε_pos N
  rcases hyp with ⟨φ, φ_extr, hφ⟩
  rcases hφ ε ε_pos with ⟨N', hN'⟩
  rcases extraction_ge φ_extr N N' with ⟨q, hq, hq'⟩
  exact ⟨φ q, hq', hN' _ hq⟩
  -- sorry


/-- If `u` tends to `l` then its subsequences tend to `l`. -/
lemma subseq_tendsto_of_tendsto' (h : seq_limit u l) (hφ : extraction φ) :
seq_limit (u ∘ φ) l := by
  -- sorry
  intro ε ε_pos
  rcases h ε ε_pos with ⟨N, hN⟩
  use N
  intro n hn
  apply hN
  calc
    N ≤ n := hn
    _ ≤ φ n := id_le_extraction' hφ n
  -- sorry

/-- If `u` tends to `l` all its cluster points are equal to `l`. -/
lemma cluster_limit (hl : seq_limit u l) (ha : cluster_point u a) : a = l := by
  -- sorry
  rcases ha with ⟨φ, φ_extr, lim_u_φ⟩
  have lim_u_φ' : seq_limit (u ∘ φ) l := subseq_tendsto_of_tendsto' hl φ_extr
  exact unique_limit lim_u_φ lim_u_φ'
  -- sorry

/-- Cauchy_sequence sequence -/
def CauchySequence (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

example : (∃ l, seq_limit u l) → CauchySequence u := by
  -- sorry
  intro hyp
  rcases hyp with ⟨l, hl⟩
  intro ε ε_pos
  rcases hl (ε / 2) (by positivity) with ⟨N, hN⟩
  use N
  intro p q hp hq
  calc
    |u p - u q| = |u p - l + (l - u q)| := by ring_nf
    _ ≤ |u p - l| + |l - u q| := by apply abs_add
    _ = |u p - l| + |u q - l| := by rw [abs_sub_comm (u q) l]
    _ ≤ ε := by linarith [hN p hp, hN q hq]
  -- sorry

/-
In the next exercise, you can reuse
 near_cluster : cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε
-/

example (hu : CauchySequence u) (hl : cluster_point u l) : seq_limit u l := by
  -- sorry
  intro ε ε_pos
  rcases hu (ε / 2) (by positivity) with ⟨N, hN⟩
  use N
  have clef : ∃ N' ≥ N, |u N' - l| ≤ ε / 2 := by
    apply near_cluster hl (ε / 2) (by positivity)
  rcases clef with ⟨N', h⟩
  rcases h with ⟨hNN', hN'⟩
  intro n hn
  calc
    |u n - l| = |u n - u N' + (u N' - l)| := by ring_nf
    _ ≤ |u n - u N'| + |u N' - l| := by apply abs_add
    _ ≤ ε := by linarith [hN n N' hn hNN', hN']
  -- sorry
