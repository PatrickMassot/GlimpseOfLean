import GlimpseOfLean.Library.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

open PiNotation BigOperators Function

section chinese
open RingHom
namespace Ideal
variable [CommRing R] {ι : Type}

def chineseMap (I : ι → Ideal R) : (R ⧸ ⨅ i, I i) →+* Π i, R ⧸ I i :=
  Quotient.lift (⨅ i, I i) (Pi.ringHom fun i : ι ↦ Quotient.mk (I i))
    (by simp [← RingHom.mem_ker, ker_Pi_Quotient_mk])

lemma chineseMap_mk (I : ι → Ideal R) (x : R) :
  chineseMap I (Quotient.mk _ x) = fun i : ι ↦ Quotient.mk (I i) x :=
rfl

lemma chineseMap_mk' (I : ι → Ideal R) (x : R) (i : ι) :
  chineseMap I (Quotient.mk _ x) i = Quotient.mk (I i) x :=
rfl

lemma chineseMap_injective (I : ι → Ideal R) : Injective (chineseMap I) := by
  rw [chineseMap, injective_lift_iff, ker_Pi_Quotient_mk]

lemma coprime_iInf_of_coprime [DecidableEq ι] {I : Ideal R} {J : ι → Ideal R} {s : Finset ι} (hf : ∀ j ∈ s, I + J j = 1) :
    I + (⨅ j ∈ s, J j) = 1 := by
  revert hf
  induction s using Finset.induction with
  | empty =>
      simp
  | @insert i s _ hs =>
      intro h
      rw [Finset.iInf_insert, inf_comm, one_eq_top, eq_top_iff, ← one_eq_top]
      set K := ⨅ j ∈ s, J j
      calc
        1 = I + K            := (hs fun j hj ↦ h j (Finset.mem_insert_of_mem hj)).symm
        _ = I + K*(I + J i)  := by rw [h i (Finset.mem_insert_self i s), mul_one]
        _ = (1+K)*I + K*J i  := by ring
        _ ≤ I + K ⊓ J i      := add_le_add mul_le_left mul_le_inf

lemma chineseMap_surjective [DecidableEq ι] [Fintype ι] {I : ι → Ideal R} (hI : ∀ i j, i ≠ j → I i + I j = 1) :
    Function.Surjective (chineseMap I) := by
  intro g
  choose f hf using fun i ↦ Quotient.mk_surjective (g i)
  have key : ∀ i, ∃ e : R, Quotient.mk (I i) e = 1 ∧ ∀ j, j ≠ i → Quotient.mk (I j) e = 0 := by
    intro i
    have hI' : ∀ j ∈ ({i} : Finset ι)ᶜ, I i + I j = 1 := by
      intros j hj
      apply hI
      simpa [ne_comm] using hj

    rcases Ideal.add_eq_one_iff.mp (coprime_iInf_of_coprime hI') with ⟨u, hu, e, he, hue⟩
    refine ⟨e, ?_, ?_⟩
    · simp [eq_sub_of_add_eq' hue, map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hu]
    · intros j hj
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      simp at he
      tauto

  choose e he using key
  use Quotient.mk _ (∑ i, f i*e i)
  ext i
  rw [chineseMap_mk', map_sum, Finset.sum_univ_eq_single i]
  · simp [(he i).1, hf]
  · intros j hj
    simp [(he j).2 i hj.symm]

noncomputable def chineseIso [DecidableEq ι] [Fintype ι] (I : ι → Ideal R) (hI : ∀ i j, i ≠ j → I i + I j = 1) :
   (R ⧸ ⨅ i, I i) ≃+* Π i, R ⧸ I i :=
{ Equiv.ofBijective _ ⟨chineseMap_injective I, chineseMap_surjective hI⟩, chineseMap I with }

end Ideal
end chinese
