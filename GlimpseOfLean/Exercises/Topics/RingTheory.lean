import GlimpseOfLean.Library.Ring

setup
open PiNotation BigOperators Function Classical
noncomputable section

namespace GlimpseOfLean

/-
# Commutative rings and their quotients

This files gives a tour through the objects needed to do ring theory: rings, ring homomorphisms and
isomorphisms, ideals and quotients. The first part is completely elementary, using only the
definition of commutative rings. The middle part introduces quotient of such rings by ideals and
culminate with a proof of Nœther’s first isomorphism theorem. The last part uses the arithmetic of
ideals and culminates with a proof of the Chinese remainder theorem.
-/

open RingHom Function

/-
In order to say “Let `R` a an arbitrary commutative ring, we write
`{R : Type*} [CommRing R]` to declare a type `R` and then assume it is equipped
with a commutative ring structure.
-/

/-
Now, given elements `x y z : R` we can apply the ring operators such as `+`, `-`, `*`, `0` and `1`
to the elements of the ring and get new elements.
The `ring` tactic can simplify the resulting expressions.

(Here, `2` is an abbreviation for `1 + 1`, `3` is `1 + 1 + 1`, ...)
-/
example {R : Type*} [CommRing R] (x y z : R) :
    x * (y + z) + y * (z + x) + z * (x + y) = 2 * x * y + 2 * y * z + 2 * x * z := by
  ring

/-
## Homomorphisms and isomorphisms

Given a ring `R` and a ring `S`, a ring homomorphism from `R` to `S` is written
`f : R →+* S`.
Like a function, we can apply a homomorphism `f` to an element `x : R`
by writing `f x`.
The `simp` tactic knows basic facts about ring homomorphisms.
For example, that they preserve the operations `+`, `*`, `0`, and `1`.
-/
section homomorphisms
variable {R S : Type*} [CommRing R] [CommRing S]


example (f : R →+* S) (x y : R) :
    f (1 + x * y) + f 0 = 1 + f x * f y := by
  simp

variable {T : Type*} [CommRing T]
/-
Let's try defining the composition of two ring homomorphisms.
We have to supply the definition of the map,
and then prove that it respects the ring structure.
Of course Mathlib already has this, but we are redoing it as an exercise.

Try filling in the `sorry`s below using `intro` and `simp`.
-/
def RingHom.comp (g : S →+* T) (f : R →+* S) : R →+* T where
  toFun x := g (f x)
  map_one' := by
    sorry
  map_mul' := by
    sorry
  map_zero' := by
    sorry
  map_add' := by
    sorry

/-
A ring isomorphism between `R` and `S` is written `e : R ≃+* S`.
We can apply `e` as a function from `R` to `S` by writing `e x`, where `x : R`.
To apply `e` in the other direction, from `S` to `R`, we write `e.symm y`, where `y : S`.

To define a ring isomorphism directly, we have to supply two maps: `toFun : R → S` and
`invFun : S → R` and show that they are inverses to each other, in addition to showing that addition
and multiplication are preserved. We will see below an example that does not explicitly provide
the inverse morphism.
Try showing the composition of two isomorphisms is again an isomorphism.

Hint: `Function.LeftInverse` and `Function.RightInverse` are forall-statements.
Try unfolding them or using `intro x` to make progress.
-/
def RingEquiv.comp (g : S ≃+* T) (f : R ≃+* S) : R ≃+* T where
  toFun x := g (f x)
  invFun x := f.symm (g.symm x)
  left_inv := by
    sorry
  right_inv := by
    sorry
  map_add' := by
    sorry
  map_mul' := by
    sorry

end homomorphisms

/-
## Ideals and ideal quotients

An ideal in the ring `R` is written in Mathlib as `I : Ideal R`.
For an element `x : R` of our ring, we can assert `x` is in the ideal `I`
by writing `x ∈ I`.

Unfortunately, we cannot rely on `simp` to prove membership of an ideal.
The tactic `aesop` does a powerful (but slower) search through many more facts.
-/

variable {R} [CommRing R]

example (I : Ideal R) (x y : R) (hx : x ∈ I) : y * x + x * y - 0 ∈ I := by
  aesop

/-
An important ideal is the kernel of the ring homomorphism.
We can write it as `ker f : Ideal R`, where `f : R →+* S`.
The kernel is defined as containing all the elements mapped to `0` by `f`:
-/
example {S} [CommRing S] (f : R →+* S) (x : R) : x ∈ ker f ↔ f x = 0 := by
  rw [mem_ker]

/-
To define an ideal, we give a definition for the carrier set, and then prove it is closed
under multiplication on the left (hence also on the right since our rings are commutative here).

Try showing the intersection of two ideals is again an ideal (of course Mathlib already knows this,
it is only an exercise).
-/
def Ideal.inter (I J : Ideal R) : Ideal R where
  carrier := I ∩ J
  add_mem' := by
    sorry
  zero_mem' := by
    sorry
  smul_mem' := by
    sorry

/-
Finally, let's look at ideal quotients. If `I` is an ideal of the ring `R`,
then we write the quotient of `R` modulo `I` as `R ⧸ I`.
(This is not the division symbol! Type `\/` to write the quotient symbol.)
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

Two elements of `R` are mapped to the same element in the quotient when their difference is in the
ideal:
-/
example (I : Ideal R) (x y : R) (h : x - y ∈ I) :
    Ideal.Quotient.mk I x = Ideal.Quotient.mk I y := by
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact h

/- We can say this more concisely: the kernel of `Ideal.Quotient.mk I` is exactly `I`. -/

example (I : Ideal R) : ker (Ideal.Quotient.mk I) = I :=
  Ideal.mk_ker

/-
The quotient `R⧸I` and the homomorphism `Ideal.Quotient.mk I` form the “smallest” pair of
a ring and a homomorphism from `R` vanishing on `I`: any other such homomorphism factors
through it. This is the universal property of `R⧸I`. The factored homomorphism is
`Ideal.Quotient.lift I f hfI : R ⧸ I →+* S`
where `f : R →+* S` and `hfI : ∀ a ∈ I, f a = 0`.

This gives us the final ingredient we need to start proving the First Isomorphism Theorem.
First, we will show any homomorphism `f : R →+* S` is well-defined as a map `R ⧸ ker f →+* S`.

Try filling in the missing proof using `intro`, `rw`, `apply` and/or `exact`.
-/

section universal_property
variable {S} [CommRing S]

def kerLift (f : R →+* S) : R ⧸ ker f →+* S :=
  Ideal.Quotient.lift (ker f) f fun x ↦ by
    sorry

/-
After a new definition, it is a good idea to make lemmas for its basic properties.
-/
theorem kerLift_mk (f : R →+* S) (x : R) : kerLift f (Ideal.Quotient.mk (ker f) x) = f x := by
  sorry

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
  sorry

/-
Let's restate that result using `Function.Injective`.
-/
theorem kerLift_injective (f : R →+* S) : Injective (kerLift f) := by
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
      sorry
    map_add' := by
      sorry
    left_inv := by
      -- This is where it all comes together.
      -- Try following this proof sketch:
      -- * Introduce a variable `x : R ⧸ ker f`.
      -- * Choose a representative for `x`, like we did in `kerLift_injective'`.
      -- * Apply our theorem `kerLift_injective`.
      -- * Repeatedly rewrite `kerLift _ (Ideal.Quotient.mk _ _)` using `kerLift_mk`.
      -- * Finish by rewriting with `rightInverse_surjInv`.
      sorry
    }

end universal_property
end GlimpseOfLean

/- ## Arithmetic on ideals and the Chinese remainder theorem

We now take a glimpse of more advanced theory with the Chinese remainder theorem for ideals in a
commutative ring. This is a generalization of the well-known elementary version for integers.
-/
section chinese
open RingHom

namespace Ideal
-- one effect of the above line it to allow writing `Quotient` instead of `Ideal.Quotient`

section definition_and_injectivity
-- `R` is our commutative ring.
variable {R} [CommRing R]

-- `I` is our family of ideals, parametrized by the type `ι`.
variable {ι : Type} (I : ι → Ideal R)

/-
We want to create a ring homomorphism from the quotient of `R` by the intersections of the `I i`’s
to the product of the quotients `R⧸(I i)`.
For every `i : ι` we have a homomorphism from `R` to `R⧸(I i)`, namely `Quotient.mk (I i)`.
Gathering all those in a map from `R` to the products `Π i, (R ⧸ I i)` is a job for
`Pi.ringHom`. We will need the lemma `ker_Pi_Quotient_mk` about this `Pi.ringHom`.
And then we need `Ideal.lift` to factors this through the quotient of `R` by the intersection
`⨅ i, I i`. Be careful that, depending on the font you are using, the intersection symbol `⨅` and the
product `Π` could be tricky to distinguish.
-/

def chineseMap  : (R ⧸ ⨅ i, I i) →+* Π i, R ⧸ I i :=
  Quotient.lift (⨅ i, I i) (Pi.ringHom fun i : ι ↦ Quotient.mk (I i))
    (by sorry)

/- Let’s record two slighlty different spelling of how this map acts on elements, by definition. -/

lemma chineseMap_mk (x : R) : chineseMap I (Quotient.mk _ x) = fun i : ι ↦ Quotient.mk (I i) x :=
  rfl

lemma chineseMap_mk' (x : R) (i : ι) : chineseMap I (Quotient.mk _ x) i = Quotient.mk (I i) x :=
  rfl

/-
This map is always injective, without any assumption on the ideal family. This is a variation
on the injectivity from the previous section.
-/
lemma chineseMap_injective : Injective (chineseMap I) := by
  sorry
end definition_and_injectivity

/-
Surjectivity by contrast needs some assumption.
The elementary version deals with a finite family of pairwise coprime integers. In the general case
we want to use a finite family of pairwise coprime ideals.

There is a commutative semi-ring structure on `Ideal R`. This sounds like an exotic algebraic
structure but it’s the same one you have on `ℕ`: it very much looks like a commutative ring except
there is no subtraction operation. Two ideal `I` and `J` are coprime if `I + J = 1`
where `1` is the unit of `Ideal R`, namely the ideal containing all elements of `R`.
The fact that this condition applied to ideals `nℤ` and `mℤ` of `ℤ` being coprime is essentially
Bézout’s identity.
There is also an order relation on `Ideal R`, and `1` is the top element `⊤`.

The key lemma in the proof of the Chinese remainder theorem is the following one which is proved by
induction on the finite set `s`. There is an interesting point here. On paper you would probably say
you prove it by induction on the cardinal of `s`. And you would put some order on `s` simply to be
able to single out a “last” element. Typically `s` would be `{1, …, n}` for some natural number `n`.
In Lean we simply say `s` is a finite set and apply the induction principle `Finset.induction`
saying that, in order to prove something for all finite sets in some type `ι`, it suffices to prove
it for the empty set and, assuming it for some set `s` proving it for `s ∪ {i}` for every `i` not in
`s`. The structure of the proof is given below, so you don’t
have to remember how to

The union `s ∪ {i}` is spelled `insert i s`. The following lemmas about this operation will be useful:
-/
#check Finset.mem_insert_of_mem

#check Finset.mem_insert_self

variable {R : Type*} [CommRing R] {ι : Type}

lemma coprime_iInf_of_coprime {I : Ideal R} {J : ι → Ideal R} {s : Finset ι} :
    (∀ j ∈ s, I + J j = 1) → I + (⨅ j ∈ s, J j) = 1 := by
  induction s using Finset.induction with
  | empty =>
      sorry
  | @insert i s _ hs =>
      intro h
      rw [Finset.iInf_insert, inf_comm, one_eq_top, eq_top_iff, ← one_eq_top]
      set K := ⨅ j ∈ s, J j
      sorry

/-
We are now ready to prove surjectivity in the Chinese remainder theorem. We will need to write a sum
over the finite type `ι`. For any `f : ι → R`, the sum of values of `f` is `∑ i, f i`.
Useful lemmas about this operation include `map_sum` which says that homomorphisms commute with such
sums and `Finset.sum_univ_eq_single` which allows to rewrite this sum under the assumption that `f`
is non-zero only for a single element of `ι`.
-/

lemma chineseMap_surjective [Fintype ι] {I : ι → Ideal R} (hI : ∀ i j, i ≠ j → I i + I j = 1) :
    Surjective (chineseMap I) := by
  intro g
  -- The role of the `choose` tactic should be clear if you compare the tactic state before and
  -- after calling it.
  choose f hf using fun i ↦ Quotient.mk_surjective (g i)
  have key : ∀ i, ∃ e : R, Quotient.mk (I i) e = 1 ∧ ∀ j, j ≠ i → Quotient.mk (I j) e = 0 := by
    intro i
    have hI' : ∀ j ∈ ({i} : Finset ι)ᶜ, I i + I j = 1 := by
      sorry
    sorry
  choose e he using key
  sorry

/- We can now put everything together to get the Chinese remainder isomorphism. -/

noncomputable def chineseIso [Fintype ι] (I : ι → Ideal R) (hI : ∀ i j, i ≠ j → I i + I j = 1) :
   (R ⧸ ⨅ i, I i) ≃+* Π i, R ⧸ I i :=
{ Equiv.ofBijective _ ⟨chineseMap_injective I, chineseMap_surjective hI⟩, chineseMap I with }

end Ideal
end chinese

