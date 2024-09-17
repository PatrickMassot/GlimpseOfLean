import Mathlib.Probability.Notation
import GlimpseOfLean.Library.Probability
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option linter.unusedTactic false
noncomputable section
open scoped ENNReal
/-

# Probability measures, independent sets

We introduce a probability space and events (measurable sets) on that space. We then define
independence of events and conditional probability, and prove results relating those two notions.

Mathlib has a (different) definition for independence of sets and also has a conditional measure
given a set. Here we practice instead on simple new definitions to apply the tactics introduced in
the previous files.
-/

/- We open namespaces. The effect is that after that command, we can call lemmas in those namespaces
without their namespace prefix: for example, we can write `inter_comm` instead of `Set.inter_comm`.
Hover over `open` if you want to learn more. -/
open MeasureTheory ProbabilityTheory Set

/- We define a measure space `Ω`: the `MeasureSpace Ω` variable states that `Ω` is a measurable
space on which there is a canonical measure `volume`, with notation `ℙ`.
We then state that `ℙ` is a probability measure. That is, `ℙ univ = 1`, where `univ : Set Ω` is the
universal set in `Ω` (the set that contains all `x : Ω`). -/
variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

-- `A, B` will denote sets in `Ω`.
variable {A B : Set Ω}

/- One can take the measure of a set `A`: `ℙ A : ℝ≥0∞`.
`ℝ≥0∞`, or `ENNReal`, is the type of extended non-negative real numbers, which contain `∞`.
Measures can in general take infinite values, but since our `ℙ` is a probabilty measure,
it actually takes only values up to 1.
`simp` knows that a probability measure is finite and will use the lemmas `measure_ne_top`
or `measure_lt_top` to prove that `ℙ A ≠ ∞` or `ℙ A < ∞`.

Hint: use `#check measure_ne_top` to see what that lemma does.

The operations on `ENNReal` are not as nicely behaved as on `ℝ`: `ENNReal` is not a ring and
subtraction truncates to zero for example. If you find that lemma `lemma_name` used to transform
an equation does not apply to `ENNReal`, try to find a lemma named something like
`ENNReal.lemma_name_of_something` and use that instead. -/

/-- Two sets `A, B` are independent for the ambiant probability measure `ℙ` if
`ℙ (A ∩ B) = ℙ A * ℙ B`. -/
def IndepSet (A B : Set Ω) : Prop := ℙ (A ∩ B) = ℙ A * ℙ B

/-- If `A` is independent of `B`, then `B` is independent of `A`. -/
lemma indepSet_symm : IndepSet A B → IndepSet B A := by
  intro h
  unfold IndepSet
  unfold IndepSet at h
  rw [inter_comm, mul_comm]
  exact h

/- Many lemmas in measure theory require sets to be measurable (`MeasurableSet A`).
If you are presented with a goal like `⊢ MeasurableSet (A ∩ B)`, try the `measurability` tactic.
That tactic produces measurability proofs. -/

-- Hints: `compl_eq_univ_diff`, `measure_diff`, `inter_univ`, `measure_compl`, `ENNReal.mul_sub`
lemma indepSet_compl_right (hA : MeasurableSet A) (hB : MeasurableSet B) :
    IndepSet A B → IndepSet A Bᶜ := by
  intro h
  unfold IndepSet
  unfold IndepSet at h
  rw [measure_compl hB (measure_ne_top _ _)]
  rw [measure_univ]
  rw [compl_eq_univ_diff]
  rw [inter_diff_distrib_left]
  rw [inter_univ]
  rw [measure_diff]
  · rw [ENNReal.mul_sub]
    rw [mul_one]
    rw [h]
    simp
  · simp
  · measurability
  · simp

-- Use what you have proved so far
lemma indepSet_compl_left (hA : MeasurableSet A) (hB : MeasurableSet B) (h : IndepSet A B) :
    IndepSet Aᶜ B := by
  apply indepSet_symm
  apply indepSet_compl_right hB hA
  apply indepSet_symm
  exact h

-- Hint: `ENNReal.mul_self_eq_self_iff`
lemma indep_self (h : IndepSet A A) : ℙ A = 0 ∨ ℙ A = 1 := by
  unfold IndepSet at h
  rw [inter_self] at h
  symm at h -- TODO maybe it's not been introduced
  rw [ENNReal.mul_self_eq_self_iff] at h
  simp at h
  exact h

/-

### Conditional probability

-/

/-- The probability of set `A` conditioned on `B`. -/
def condProb (A B : Set Ω) : ENNReal := ℙ (A ∩ B) / ℙ B

/- We define a notation for `condProb A B` that makes it look more like paper math. -/
notation3 "ℙ("A"|"B")" => condProb A B

/- Now that we have defined `condProb`, we want to use it, but Lean knows nothing about it.
We could start every proof with `rw [condProb]`, but it is more convenient to write lemmas about the
properties of `condProb` first and then use those. -/

-- Hint : `measure_inter_null_of_null_left`
@[simp] -- this makes the lemma usable by `simp`
lemma condProb_zero_left (A B : Set Ω) (hA : ℙ A = 0) : ℙ(A|B) = 0 := by
  unfold condProb
  simp [measure_inter_null_of_null_left _ hA]

@[simp]
lemma condProb_zero_right (A B : Set Ω) (hB : ℙ B = 0) : ℙ(A|B) = 0 := by
  unfold condProb
  simp [measure_inter_null_of_null_right _ hB]

/- What other basic lemmas could be useful? Are there other "special" sets for which `condProb`
takes known values? -/

-- Your lemma(s) here

/- The next statement is a `theorem` and not a `lemma`, because we think it is important.
There is no functional difference between those two keywords. -/

/-- **Bayes Theorem** -/
theorem bayesTheorem (A B : Set Ω) : ℙ(A|B) = ℙ A * ℙ(B|A) / ℙ B := by
  by_cases h : ℙ A = 0
  · simp [h]
  unfold condProb
  rw [ENNReal.mul_div_cancel' h]
  · rw [inter_comm]
  · simp

-- Did you really need all those hypotheses?

lemma condProb_of_indepSet (h : IndepSet A B) (hB : ℙ B ≠ 0) : ℙ(A|B) = ℙ A := by
  unfold condProb
  rw [h, mul_div_assoc, ENNReal.div_self, mul_one]
  · exact hB
  · simp
