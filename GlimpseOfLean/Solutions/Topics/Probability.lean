import Mathlib.Probability.Notation
import GlimpseOfLean.Library.Probability
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
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
Measures can in general take infinite values, but since our `ℙ` is a probability measure,
it actually takes only values up to 1.
`simp` knows that a probability measure is finite and will use the lemmas `measure_ne_top`
or `measure_lt_top` to prove that `ℙ A ≠ ∞` or `ℙ A < ∞`.

Hint: use `#check measure_ne_top` to see what that lemma does.

The operations on `ENNReal` are not as nicely behaved as on `ℝ`: `ENNReal` is not a ring and
subtraction truncates to zero for example. If you find that lemma `lemma_name` used to transform
an equation does not apply to `ENNReal`, try to find a lemma named something like
`ENNReal.lemma_name_of_something` and use that instead. -/

/-- Two sets `A, B` are independent for the ambient probability measure `ℙ` if
`ℙ (A ∩ B) = ℙ A * ℙ B`. -/
def IndepSet (A B : Set Ω) : Prop := ℙ (A ∩ B) = ℙ A * ℙ B

/-- If `A` is independent of `B`, then `B` is independent of `A`. -/
lemma IndepSet.symm : IndepSet A B → IndepSet B A := by
  -- sorry
  intro h
  unfold IndepSet
  unfold IndepSet at h
  rw [inter_comm, mul_comm]
  exact h
  -- sorry

/- Many lemmas in measure theory require sets to be measurable (`MeasurableSet A`),
or to be equal to a measurable set up to a set of zero measure (`NullMeasurableSet A ℙ`).
If you are presented with a goal like `⊢ MeasurableSet (A ∩ B)` or `⊢ NullMeasurableSet (A ∩ B) ℙ`,
try the `measurability` tactic. That tactic produces measurability proofs. -/

-- Hints: `compl_eq_univ_diff`, `measure_diff`, `inter_univ`, `measure_compl`, `ENNReal.mul_sub`
lemma IndepSet.compl_right (hA : MeasurableSet A) (hB : MeasurableSet B) :
    IndepSet A B → IndepSet A Bᶜ := by
  -- sorry
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
  -- sorry

/- Apply `IndepSet.compl_right` to prove this generalization. It is good practice to add the iff
version of some frequently used lemmas, this allows us to use them inside `rw` tactics. -/
lemma IndepSet.compl_right_iff (hA : MeasurableSet A) (hB : MeasurableSet B) :
    IndepSet A Bᶜ ↔ IndepSet A B := by
  -- sorry
  constructor
  · intro h
    rw [← compl_compl B]
    apply IndepSet.compl_right hA hB.compl
    exact h
  · intro h
    exact compl_right hA hB h
  -- sorry

-- Use what you have proved so far
lemma IndepSet.compl_left (hA : MeasurableSet A) (hB : MeasurableSet B) (h : IndepSet A B) :
    IndepSet Aᶜ B := by
  -- sorry
  apply IndepSet.symm
  apply IndepSet.compl_right hB hA
  apply IndepSet.symm
  exact h
  -- sorry

/- Can you write and prove a lemma `IndepSet.compl_left_iff`, following the examples above?-/

-- Your lemma here

-- Hint: `ENNReal.mul_self_eq_self_iff`
lemma indep_self (h : IndepSet A A) : ℙ A = 0 ∨ ℙ A = 1 := by
  -- sorry
  unfold IndepSet at h
  rw [inter_self] at h
  symm at h -- TODO maybe it's not been introduced
  rw [ENNReal.mul_self_eq_self_iff] at h
  simp at h
  exact h
  -- sorry

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
  -- sorry
  unfold condProb
  simp [measure_inter_null_of_null_left _ hA]
  -- sorry

@[simp]
lemma condProb_zero_right (A B : Set Ω) (hB : ℙ B = 0) : ℙ(A|B) = 0 := by
  -- sorry
  unfold condProb
  simp [measure_inter_null_of_null_right _ hB]
  -- sorry

/- What other basic lemmas could be useful? Are there other "special" sets for which `condProb`
takes known values? -/

-- Your lemma(s) here

/- The next statement is a `theorem` and not a `lemma`, because we think it is important.
There is no functional difference between those two keywords. -/

/-- **Bayes Theorem** -/
theorem bayesTheorem (hB : ℙ B ≠ 0) : ℙ(A|B) = ℙ A * ℙ(B|A) / ℙ B := by
  by_cases h : ℙ A = 0 -- this tactic perfoms a case disjunction.
  -- Observe the goals that are created, and specifically the `h` assumption in both goals
  · /- inline sorry -/simp [h] /- inline sorry -/
  -- sorry
  unfold condProb
  rw [ENNReal.mul_div_cancel h]
  · rw [inter_comm]
  · simp
  -- sorry

/- Did you really need all those hypotheses?
In Lean, division by zero follows the convention that `a/0 = 0` for all a. This means we can prove
Bayes' Theorem without requiring `ℙ A ≠ 0` and `ℙ B ≠ 0`. However, this is a quirk of the
formalization rather than the standard mathematical statement.
If you want to know more about how division works in Lean, try to hover over `/` with your mouse. -/

theorem bayesTheorem' (A B : Set Ω) : ℙ(A|B) = ℙ A * ℙ(B|A) / ℙ B := by
  -- sorry
  by_cases h : ℙ A = 0
  · simp [h]
  unfold condProb
  rw [ENNReal.mul_div_cancel h]
  · rw [inter_comm]
  · simp
  -- sorry

lemma condProb_of_indepSet (h : IndepSet B A) (hB : ℙ B ≠ 0) : ℙ(A|B) = ℙ A := by
  -- sorry
  unfold condProb
  rw [h.symm, mul_div_assoc, ENNReal.div_self, mul_one]
  · exact hB
  · simp
  -- sorry
