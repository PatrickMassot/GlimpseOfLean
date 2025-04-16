import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Basic
attribute [-aesop] mul_mem add_mem
attribute [aesop unsafe apply (rule_sets := [SetLike])] mul_mem add_mem Ideal.mul_mem_left Ideal.mul_mem_right
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option linter.unusedTactic false
noncomputable section

namespace Tutorial

/-
# Ring theory and the first isomorphism theorem

This exercise gives a tour through the objects needed to do ring theory:
rings, ring homomorphisms and isomorphisms, ideals and quotients.
We finish by proving the first isomorphism theorem.
-/

open RingHom Function

/-
The `variables` line means: "Let `R`, `S`, `T` be arbitrary commutative rings."
First we declare three types `R`, `S`, `T`, and then we equip them with
an arbitrary commutative ring structure.
-/
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-
Now, given elements `x y z : R` we can apply the ring operators such as `+`, `-`, `*`, `0` and `1`
to the elements of the ring and get new elements.
The `ring` tactic can simplify the resulting expressions.

(Here, `2` is an abbreviation for `1 + 1`, `3` is `1 + 1 + 1`, ...)
-/
example (x y z : R) :
    x * (y + z) + y * (z + x) + z * (x + y) = 2 * x * y + 2 * y * z + 2 * x * z := by
  ring

/-
## Homomorphisms and isomorphisms

Now that we have a ring `R` and a ring `S`,
a ring homomorphism from `R` to `S` is written `f : R →+* S`.
Like a function, we can apply a homomorphism `f` to an element `x : R`
by writing `f x`.
The `simp` tactic knows basic facts about ring homomorphisms.
For example, that they preserve the operations `+`, `*`, `0`, and `1`.
-/
example (f : R →+* S) (x y : R) : f (1 + x * y) + f 0 = 1 + f x * f y := by
  simp

/-
Let's try defining the composition of two ring homomorphisms.
We have to supply the definition of the map,
and then prove that it respects the ring structure.

Try filling in the `sorry`s below using `intro` and `simp`.
-/
def RingHom.comp (g : S →+* T) (f : R →+* S) : R →+* T where
  toFun x := g (f x)
  map_one' := by
    -- sorry
    simp
    -- sorry
  map_mul' := by
    -- sorry
    intros
    simp
    -- sorry
  map_zero' := by
    -- sorry
    simp
    -- sorry
  map_add' := by
    -- sorry
    intros
    simp
    -- sorry

/-
A ring isomorphism between `R` and `S` is written `e : R ≃+* S`.
We can apply `e` as a function from `R` to `S` by writing `e x`, where `x : R`.
To apply `e` in the other direction, from `S` to `R`, we write `e.symm y`, where `y : S`.

To define a ring isomorphism, we have to supply two maps: `toFun : R → S` and `invFun : S → R`
and show that they are inverses to each other,
in addition to showing that addition and multiplication are preserved.
Try showing the composition of two isomorphisms is again an isomorphism.

Hint: `Function.LeftInverse` and `Function.RightInverse` are forall-statements.
Try unfolding them or using `intro x` to make progress.
-/
def RingEquiv.comp (g : S ≃+* T) (f : R ≃+* S) : R ≃+* T where
  toFun x := g (f x)
  invFun x := f.symm (g.symm x)
  left_inv := by
    -- sorry
    intro x
    simp
    -- sorry
  right_inv := by
    -- sorry
    intro x
    simp
    -- sorry
  map_add' := by
    -- sorry
    intros
    simp
    -- sorry
  map_mul' := by
    -- sorry
    intros
    simp
    -- sorry

/-
## Ideals and ideal quotients

An ideal in the ring `R` is written in Mathlib as `I : Ideal R`.
For an element `x : R` of our ring, we can assert `x` is in the ideal `I`
by writing `x ∈ I`.

Unfortunately, we cannot rely on `simp` to prove membership of an ideal.
The tactic `aesop` does a powerful (but slower) search through many more facts.
-/
example (I : Ideal R) (x y : R) (hx : x ∈ I) : y * x + x * y - 0 ∈ I := by
  aesop

/-
An important ideal is the kernel of the ring homomorphism.
We can write it as `ker f : Ideal R`, where `f : R →+* S`.
The kernel is defined as containing all the elements mapped to `0` by `f`:
-/
example (f : R →+* S) (x : R) : x ∈ ker f ↔ f x = 0 := by
  rw [mem_ker]

/-
To define an ideal, we give a definition for the carrier set, and then prove it is closed
under addition and multiplication on the left.
(Ideals are left-ideals by default in Mathlib.)

Try showing the intersection of two ideals is again an ideal.
-/
def Ideal.inter (I J : Ideal R) : Ideal R where
  carrier := I ∩ J
  add_mem' := by
    -- sorry
    aesop
    -- sorry
  zero_mem' := by
    -- sorry
    aesop
    -- sorry
  smul_mem' := by
    -- sorry
    aesop
    -- sorry

/-
Finally, let's look at ideal quotients. If `I` is an ideal of the ring `R`,
then we write the quotient of `R` modulo `I` as `R ⧸ I`.
(This is not the division symbol! Type `\/` to write the quotient symbol.)
In set theory terms, the elements of `R ⧸ I` are equivalence classes of elements in `R`.
The quotient is again a ring and we can treat it just like `R`, `S`, `T` above,
by taking elements of the quotient and adding and multiplying them together:
-/
example (I : Ideal R) (x y z : R ⧸ I) :
    x * (y + z) + y * (z + x) + z * (x + y) = 2 * x * y + 2 * y * z + 2 * x * z := by
  ring

/-
There are two important homomorphisms involving quotients.
First, the canonical map from `R` into the quotient ring `R ⧸ I`, which is called
`Ideal.Quotient.mk I : R →+* R ⧸ I`.

In set theory terms, this map sends each element of `R` to its equivalence class in `R ⧸ I`.
Two elements have the same equivalence class when their difference is in the ideal:
-/
example (I : Ideal R) (x y : R) (h : x - y ∈ I) :
    Ideal.Quotient.mk I x = Ideal.Quotient.mk I y := by
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact h

/-
The other important map goes out of the quotient, and is called `Ideal.Quotient.lift` in Lean.
This turns a homomorphism `f : R →+* S` into a homomorphism
`Ideal.Quotient.lift I f hfI : R ⧸ I →+* S`, where `I : Ideal R` and `hfI` is a proof
that `f` is well-defined.

This gives us the final ingredient we need to start proving the First Isomorphism Theorem.
First, we will show any homomorphism `f : R →+* S` is well-defined as a map `R ⧸ ker f →+* S`.

Try filling in the missing proof using `intro`, `rw`, `apply` and/or `exact`.
-/
def kerLift (f : R →+* S) : R ⧸ ker f →+* S :=
  Ideal.Quotient.lift _ f fun x => by
    -- sorry
    intro hx
    rw [mem_ker] at hx
    exact hx
    -- sorry

/-
After a new definition, it is a good idea to make lemmas for its basic properties.
-/
theorem kerLift_mk (f : R →+* S) (x : R) : kerLift f (Ideal.Quotient.mk (ker f) x) = f x := by
  -- sorry
  unfold kerLift
  simp
  -- sorry

/-
When we are given a quotient element `x : R ⧸ I`, it is often a useful proof step to
choose a representative `x' : R` for this quotient element.
The statement that `x' : R` is a representative for `x : R ⧸ I` is written `Ideal.Quotient.mk I x' = x`. 
The fact that each `x : R ⧸ I` has a representative can be written `∃ x', Ideal.Quotient.mk I x' = x`.
Recalling the definition of `Function.Surjective` from `04Exists.lean`,
we can see that `∃ x', Ideal.Quotient.mk I x' = x` is the same as
`Function.Surjective (Ideal.Quotient.mk I)`, which is available as the theorem `Ideal.Quotient.mk_surjective`
in Mathlib.

To give an example, let's start a proof that `kerLift` is injective.
We first use `Ideal.Quotient.mk_surjective` to choose a representative `x'` for `x`.
Then we replace `x` with `Ideal.Quotient.mk I x'` everywhere.

Try finishing the proof. Here are a few useful lemmas:
`Ideal.Quotient.eq_zero_iff_mem`, `kerLift_mk`, `mem_ker`.
-/
theorem kerLift_injective' (f : R →+* S) (x : R ⧸ ker f) (hx : kerLift f x = 0) : x = 0 := by
  rcases Ideal.Quotient.mk_surjective x with ⟨x', hx'⟩
  rw [← hx']
  rw [← hx'] at hx
  -- sorry
  rw [kerLift_mk] at hx
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_ker]
  exact hx
  -- sorry

/-
Let's restate that result using `Function.Injective`.
-/
theorem kerLift_injective (f : R →+* S) : Function.Injective (kerLift f) := by
  rw [injective_iff_map_eq_zero]
  exact kerLift_injective' f

/-
## First isomorphism theorem

We have all the ingredients to prove a form of the first isomorphism theorem:
if `f : R →+* S` is a surjective ring homomorphism, `R ⧸ ker f` is isomorphic to `S`,
by the explicit isomorphism we will define below.
To give the inverse function, we use the definition `surjInv` which gives an arbitrary
right inverse to a surjective function `f` (if `hf` is the proof that `f` is surjective,
the proof that `surjInv` is a right inverse, is called `rightInverse_surjInv hf`).
-/
def firstIsomorphismTheorem (f : R →+* S) (hf : Function.Surjective f) :
    R ⧸ ker f ≃+* S :=
  { toFun := kerLift f
    invFun x := Ideal.Quotient.mk (ker f) (surjInv hf x)
    right_inv := rightInverse_surjInv hf 
    map_mul' := by
      -- sorry
      intros
      simp
      -- sorry
    map_add' := by
      -- sorry
      intros
      simp
      -- sorry
    left_inv := by
      -- This is where it all comes together.
      -- Try following this proof sketch:
      -- * Introduce a variable `x : R ⧸ ker f`.
      -- * Choose a representative for `x`, like we did in `kerLift_injective'`.
      -- * Apply our theorem `kerLift_injective`.
      -- * Repeatedly rewrite `kerLift _ (Ideal.Quotient.mk _ _)` using `kerLift_mk`.
      -- * Finish by rewriting with `rightInverse_surjInv`.
      -- sorry
      intro x
      rcases Ideal.Quotient.mk_surjective x with ⟨x', hx'⟩
      rw [← hx']
      apply kerLift_injective
      rw [kerLift_mk]
      rw [kerLift_mk]
      rw [rightInverse_surjInv hf]
      -- sorry
    }

end Tutorial
