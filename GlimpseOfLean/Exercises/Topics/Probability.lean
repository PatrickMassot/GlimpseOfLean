-- import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Notation
import GlimpseOfLean.Library.Probability
set_option linter.unusedSectionVars false
noncomputable section
-- def measurable sets:NO import it, explain in docstring what it is
-- def independence of sets -- define it
--indep A B -> indep B A
--indep A B -> indep A B^c
-- indep A A -> μ A = 0, 1, +∞
-- def conditional probability for a  general set

-- introduce measure_ne_top

-- Bayes theorem

-- explain that `open Set` allows us to write inter_comm instead of Set.inter_comm

-- #check inter_comm --
-- #check Set.inter_comm

-- explain the measurability tactic

--measure take values in ENNReal, which has some strange features, explain ⊤, it's not a ring, there is ENNReal.mul_sub that asks for particular assumptions, sometimes we need measure_ne_top, but simp should solve it

-- remove the linter that complains for unused hypotheses

open MeasureTheory ProbabilityTheory Set

attribute [simp] measure_ne_top measure_lt_top

variable {Ω : Type} {A B C : Set Ω} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

def IndepSet (A B : Set Ω) : Prop :=
  ℙ (A ∩ B) = ℙ A * ℙ B

lemma indepSet_symm : IndepSet A B → IndepSet B A := by
  sorry


-- hints: `compl_eq_univ_diff`, `measure_diff`, `inter_univ`, `measure_compl`, `ENNReal.mul_sub`
lemma indepSet_compl_right (hA : MeasurableSet A) (hB : MeasurableSet B) :
    IndepSet A B → IndepSet A Bᶜ := by
  sorry

-- use what you have proved so far
lemma indepSet_compl_left (hA : MeasurableSet A) (hB : MeasurableSet B) :
    IndepSet A B → IndepSet Aᶜ B := by
  sorry

lemma indep_self : IndepSet A A → ℙ A = 0 ∨ ℙ A = 1 := by
  sorry

def condProb (A B : Set Ω) : ENNReal :=
  ℙ (A ∩ B) / ℙ B

--remark, we could just start every proof with rw [condProb], but we want an API to make the object more usable
-- hints : `measure_inter_null_of_null_left`
@[simp] -- this makes the lemma usable by simp
lemma condProb_zero_left (hA : ℙ A = 0) : condProb A B = 0 := by
  sorry

@[simp]
lemma condProb_zero_right (hB : ℙ B = 0) : condProb A B = 0 := by
  sorry

theorem bayesTheorem (hA : MeasurableSet A) (hB : MeasurableSet B) (hB₀ : ℙ B ≠ 0) :
    condProb A B = ℙ A * condProb B A / ℙ B := by
  sorry

--do you really need all those hypotheses?
