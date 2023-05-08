import GlimpseOfLean.Lib.TutoLib
import Mathlib.Order.GaloisConnection

open PiNotation
macro "ls" : tactic => `(tactic | library_search)

namespace Tuto

section InfSup
variable  [PartialOrder X]

def isInf (s : Set X) (x₀ : X) :=
  ∀ x, x ∈ lowerBounds s ↔ x ≤ x₀

lemma isInf.lowerBound {s : Set X} {x₀ : X} (h : isInf s x₀) : x₀ ∈ lowerBounds s := by
  exact (h _).mpr le_rfl

def isInf.eq {s : Set X} {x₀ x₁ : X} (hx₀ : isInf s x₀) (hx₁ : isInf s x₁) : x₀ = x₁ := by
  apply le_antisymm
  · exact (hx₁ _).1 ((hx₀ _).2 le_rfl)
  · exact (hx₀ _).1 ((hx₁ _).2 le_rfl)

def isSup (s : Set X) (x₀ : X) :=
  ∀ x, x ∈ upperBounds s ↔ x₀ ≤ x

lemma isSup.upperBound {s : Set X} {x₀ : X} (h : isSup s x₀) : x₀ ∈ upperBounds s :=
  isInf.lowerBound (X := OrderDual X) h

def isSup.eq {s : Set X} {x₀ x₁ : X} (hx₀ : isSup s x₀) (hx₁ : isSup s x₁) : x₀ = x₁ :=
  isInf.eq (X := OrderDual X) hx₀ hx₁

def isInfFun (I : Set X → X) :=
  ∀ s : Set X, isInf s (I s)

def isSupFun (S : Set X → X) :=
  ∀ s : Set X, isSup s (S s)


lemma isSup_of_isInf {I : Set X → X} (h : isInfFun I) : isSupFun (fun s ↦ I (upperBounds s)) := by
  intro s x
  constructor
  · intro hx
    exact (h _).lowerBound hx
  · intros hx y hy
    calc
      y ≤ I (upperBounds s) := (h _ y).mp (fun z hz ↦ hz hy)
      _ ≤ x                 := hx

lemma isInf_of_isSup {S : Set X → X} (h : isSupFun S) : isInfFun (fun s ↦ S (lowerBounds s)) :=
  isSup_of_isInf (X := OrderDual X) h


class CompleteLattice (X : Type) [PartialOrder X] where
  I : Set X → X
  I_isInf : isInfFun I
  S : Set X → X
  S_isSup : isSupFun S

instance (X : Type) [PartialOrder X] [CompleteLattice X] : CompleteLattice (OrderDual X) where
  I := CompleteLattice.S (X := X)
  I_isInf := CompleteLattice.S_isSup (X := X)
  S := CompleteLattice.I (X := X)
  S_isSup := CompleteLattice.I_isInf (X := X)

notation "Inf" => CompleteLattice.I
notation "Sup" => CompleteLattice.S

def CompleteLattice.mk_of_Inf {I : Set X → X} (h : isInfFun I) : CompleteLattice X where
 I := I
 I_isInf := h
 S := fun s ↦ I (upperBounds s)
 S_isSup := isSup_of_isInf h

def CompleteLattice.mk_of_Sup {S : Set X → X} (h : isSupFun S) : CompleteLattice X where
 I := fun s ↦ S (lowerBounds s)
 I_isInf := isInf_of_isSup h
 S := S
 S_isSup := h

variable [CompleteLattice X]

lemma lowerBound_Inf (s : Set X) : Inf s ∈ lowerBounds s :=
  (CompleteLattice.I_isInf _).lowerBound

lemma upperBound_Sup (s : Set X) : Sup s ∈ upperBounds s :=
  (CompleteLattice.S_isSup _).upperBound

lemma Inf_subset {s t : Set X} (h : s ⊆ t): Inf t ≤ Inf s := by
  apply (CompleteLattice.I_isInf s _).1
  apply lowerBounds_mono_set h
  exact lowerBound_Inf t

lemma Sup_subset {s t : Set X} (h : s ⊆ t): Sup s ≤ Sup t :=
  Inf_subset (X := OrderDual X) h

lemma Inf_pair {x x' : X} : x ≤ x' ↔ Inf {x, x'} = x := by
  constructor
  · intro h
    apply (CompleteLattice.I_isInf _).eq
    intro z
    constructor
    · intro hz
      apply hz
      simp
    · intro hz
      simp [hz, hz.trans h]
  · intro h
    rw [← h]
    apply lowerBound_Inf
    simp

lemma Sup_pair {x x' : X} : x ≤ x' ↔ Sup {x, x'} = x' := by
  rw [Set.pair_comm x x']
  exact Inf_pair (X := OrderDual X)

lemma Inf_self_le (x : X) : Inf {x' | x ≤ x'} = x := by
  apply (CompleteLattice.I_isInf _).eq
  intro x'
  constructor
  · intro h
    exact h le_rfl
  · intro h x'' hx''
    exact h.trans hx''

lemma Sup_le_self (x : X) : Sup {x' | x' ≤ x} = x :=
  Inf_self_le (X := OrderDual X) x

end InfSup

section Adjunction

variable [PartialOrder X] [CompleteLattice X] [PartialOrder Y] [CompleteLattice Y]

def adjunction [PartialOrder X] [PartialOrder Y] (l : X → Y) (r : Y → X) :=
  ∀ x y, l x ≤ y ↔ x ≤ r y

def mk_right (l : X → Y) : Y → X := fun y ↦ Sup {x | l x ≤ y}

lemma adjunction_of_Sup {l : X → Y} (h : ∀ s : Set X, l (Sup s) = Sup (l '' s)) :
    adjunction l (mk_right l) := by
  intro x y
  constructor
  · intro h'
    exact (CompleteLattice.S_isSup {x | l x ≤ y}).upperBound h'
  · intro h'
    have l_mono : Monotone l := by
      intro a b hab
      have := h {a, b}
      rw [Sup_pair.1 hab, Set.image_pair] at this
      exact Sup_pair.2 this.symm
    calc
      l x ≤ l (mk_right l y) := l_mono h'
      _   = Sup (l '' { x | l x ≤ y }) := h {x | l x ≤ y}
      _   ≤ Sup { y' | y' ≤ y } := Sup_subset (Set.image_preimage_subset l { y' | y' ≤ y })
      _   = y := Sup_le_self y

def mk_left (r : Y → X) : X → Y := fun x ↦ Inf {y | x ≤ r y}

lemma adjunction_of_Inf {r : Y → X} (h : ∀ s : Set Y, r (Inf s) = Inf (r '' s)) :
    adjunction (mk_left r) r :=
  fun x y ↦ (adjunction_of_Sup (X := OrderDual Y) (Y := OrderDual X) h y x).symm

end Adjunction

section Topology

@[ext]
structure Topology (X : Type) where
  isOpen : Set X → Prop
  isOpen_unionᵢ : ∀ {ι : Type}, ∀ {s : ι → Set X}, (∀ i, isOpen (s i)) → isOpen (⋃ i, s i)
  isOpen_interᵢ : ∀ {ι : Type}, ∀ {s : ι → Set X}, (∀ i, isOpen (s i)) → Finite ι → isOpen (⋂ i, s i)

instance : PartialOrder (Topology X) where
  le := fun T T' ↦ T'.isOpen ≤ T.isOpen
  le_refl := fun T V hV ↦ hV
  le_trans := fun T T' T'' h h' V hV ↦ h _ (h' V hV)
  le_antisymm := by
    intro T T' h h'
    ext V
    tauto

def SupTop (s : Set (Topology X)) : Topology X where
  isOpen := fun V ↦ ∀ T ∈ s, T.isOpen V
  isOpen_unionᵢ := by
    intros ι t ht a ha
    exact a.isOpen_unionᵢ fun i ↦ ht i a ha
  isOpen_interᵢ := by
    intros ι t ht hι a ha
    exact a.isOpen_interᵢ (fun i ↦ ht i a ha) hι

lemma isSup_SupTop : isSupFun (SupTop : Set (Topology X) → Topology X) := by
  intro t T
  constructor
  · intro hT V hV s hs
    exact hT hs V hV
  · intro hT T' hT' V hV
    exact hT V hV T' hT'

instance : CompleteLattice (Topology X) := CompleteLattice.mk_of_Sup isSup_SupTop

def push (f : X → Y) (T : Topology X) : Topology Y where
  isOpen := fun V ↦ T.isOpen (f ⁻¹' V)
  isOpen_unionᵢ := by
    intros ι s hs
    rw [Set.preimage_unionᵢ]
    exact T.isOpen_unionᵢ hs
  isOpen_interᵢ := by
    intros ι s hs hι
    rw [Set.preimage_interᵢ]
    exact T.isOpen_interᵢ hs hι

lemma push_push (f : X → Y) (g : Y →Z) (T : Topology X) :
    push g (push f T) = push (g ∘ f) T := by
  ext V
  rfl


def Continuous (T : Topology X) (T' : Topology Y) (f : X → Y) := push f T ≤ T'

def pull (f : X → Y) (T : Topology Y) : Topology X := mk_right (push f) T

def ProductTopology {ι : Type} {X : ι → Type} (T : Π i, Topology (X i)) : Topology (Π i, X i) :=
Inf (Set.range (fun i ↦ pull (fun x ↦ x i) (T i)))

lemma push_Sup (f : X → Y) {t : Set (Topology X)} : push f (Sup t) = Sup (push f '' t) := by
  ext V
  change _ ↔ ∀ T ∈ push f '' t, _
  rw [Set.ball_image_iff]
  rfl

lemma ContinuousProductTopIff {ι : Type} {X : ι → Type} (T : Π i, Topology (X i))
  {Z : Type} (TZ : Topology Z) {f : Z → Π i, X i}:
    Continuous TZ (ProductTopology T) f ↔ ∀ i,  Continuous TZ (T i) (fun z ↦ f z i) := by
  unfold Continuous ProductTopology
  rw [← CompleteLattice.I_isInf, lowerBounds_range]
  apply forall_congr'
  intro i
  unfold pull
  rw [← adjunction_of_Sup (fun s ↦ push_Sup _), push_push]
  rfl

end Topology
end Tuto
