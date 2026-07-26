import FormalSchemes.CompletionNestedBasicOpen

set_option linter.style.header false
-- The formal-spectrum morphisms range over the nested localization/completion towers of the
-- completed tensor product, which are slow for the elaborator and the kernel; raise the budgets.
set_option linter.style.setOption false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The geometric completed-tensor / away-localization interchange, second factor

The left-factor interchange `CompletedTensorAwayInterchange.interchangeOpenImmersion`
(`FormalSchemes/CompletedTensorAwayInterchangeSpf.lean`) realises the localise-then-tensor patch
`Spf((A{1/f}) ⊗̂_R B)` as the open subscheme `D(1 ⊗ f) ⊆ Spf(A ⊗̂_R B)` cut out by the invertibility
of `f̄ = inl f` (the image of `f` from the *first* tensor factor). This file delivers the mirror
statement localising the *second* factor: for `g : B` it produces the open immersion

  `Spf(A ⊗̂_R (B{1/g})) ⟶ Spf(A ⊗̂_R B)`

with underlying-space range the basic open `D(1 ⊗ g) = D(inr g) ⊆ Spf(A ⊗̂_R B)`.

Rather than rebuilding the ring-level localization machinery, the second-factor immersion is
obtained by **geometric conjugation** of the left-factor immersion with the completed-tensor
isomorphism `CompletedTensorProduct.commEquiv : A ⊗̂_R B ≃+* B ⊗̂_R A`. Concretely, promoting
`commEquiv` to an isomorphism of formal spectra (via `FormalSpectrum.isoOfAdicRingEquiv`) yields
`commSpfIso : Spf(A ⊗̂_R B) ≅ Spf(B ⊗̂_R A)`, and

  `rightInterchangeOpenImmersion g = commSpfIso.hom ≫ interchangeOpenImmersion (localising the first
  factor of `B ⊗̂_R A` at `g`) ≫ commSpfIso.hom`.

The range computation transports the basic open `D(inl g) ⊆ Spf(B ⊗̂_R A)` of the left-factor
immersion across `commSpfIso` back to `D(inr g) ⊆ Spf(A ⊗̂_R B)`, using that `commEquiv` sends the
class of `inl_{B,A} g` to the class of `inr_{A,B} g` (`commEquiv_inl`).

## Main results

* `CompletedTensorAwayInterchange.isAdicHom_commEquiv`: the commutativity isomorphism is an adic
  homomorphism, carrying the ideal of definition of `A ⊗̂_R B` onto that of `B ⊗̂_R A`.
* `CompletedTensorAwayInterchange.commSpfIso`: the induced isomorphism of formal spectra
  `Spf(A ⊗̂_R B) ≅ Spf(B ⊗̂_R A)`.
* `CompletedTensorAwayInterchange.rightInterchangeOpenImmersion`: the second-factor interchange
  morphism `Spf(A ⊗̂_R (B{1/g})) ⟶ Spf(A ⊗̂_R B)`.
* `CompletedTensorAwayInterchange.isOpenImmersion_rightInterchangeOpenImmersion`: it is a
  `LocallyRingedSpace.IsOpenImmersion`.
* `CompletedTensorAwayInterchange.range_rightInterchangeOpenImmersion_base`: its underlying-space
  range is the basic open `D(inr g) ⊆ Spf(A ⊗̂_R B)`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum

universe u

namespace CompletedTensorAwayInterchange

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-! ### The commutativity isomorphism as an adic homomorphism -/

/-- The commutativity isomorphism `A ⊗̂_R B ≃+* B ⊗̂_R A` is an **adic homomorphism**: it carries
the ideal of definition of `A ⊗̂_R B` onto that of `B ⊗̂_R A`. Since `IsAdicHom I J φ` is
definitionally `I.map φ = J`, this reduces (after `idealOfDefinition_eq_map` and `Ideal.map_map`)
to the ring-hom
equality `commEquiv ∘ algebraMap = algebraMap`, which holds because `commEquiv` fixes the image of
the base: `commEquiv (algebraMap r) = commEquiv (inl (algebraMap r)) = inr (algebraMap r) =
algebraMap r`. -/
theorem isAdicHom_commEquiv (hI : I.FG) :
    IsAdicHom (CompletedTensorProduct.idealOfDefinition R I A B)
      (CompletedTensorProduct.idealOfDefinition R I B A)
      (CompletedTensorProduct.commEquiv (R := R) (I := I) (A := A) (B := B) hI).toRingHom := by
  have hcomp :
      (CompletedTensorProduct.commEquiv (R := R) (I := I) (A := A) (B := B) hI).toRingHom.comp
        (algebraMap R (CompletedTensorProduct R I A B)) =
      algebraMap R (CompletedTensorProduct R I B A) := by
    refine RingHom.ext (fun r => ?_)
    change CompletedTensorProduct.commEquiv hI
        (algebraMap R (CompletedTensorProduct R I A B) r) =
        algebraMap R (CompletedTensorProduct R I B A) r
    rw [← (CompletedTensorProduct.inl R I A B).commutes r,
      CompletedTensorProduct.commEquiv_inl,
      (CompletedTensorProduct.inr R I B A).commutes r]
  change (CompletedTensorProduct.idealOfDefinition R I A B).map
      (CompletedTensorProduct.commEquiv (R := R) (I := I) (A := A) (B := B) hI).toRingHom =
      CompletedTensorProduct.idealOfDefinition R I B A
  rw [CompletedTensorProduct.idealOfDefinition_eq_map, Ideal.map_map, hcomp]
  exact (CompletedTensorProduct.idealOfDefinition_eq_map).symm

/-! ### The induced commutativity isomorphism of formal spectra -/

/-- **The commutativity isomorphism of affine formal spectra** `Spf(A ⊗̂_R B) ≅ Spf(B ⊗̂_R A)`,
induced by the ring isomorphism `commEquiv` via `FormalSpectrum.isoOfAdicRingEquiv` applied to the
adic homomorphism `isAdicHom_commEquiv`. Kept general in `A B`, so it can be instantiated both at
`(A, B{1/g})` and at `(B, A)`. -/
def commSpfIso (hI : I.FG) :
    FormalSpectrum.locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I A B) ≅
      FormalSpectrum.locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I B A) :=
  FormalSpectrum.isoOfAdicRingEquiv _ _
    (CompletedTensorProduct.commEquiv (R := R) (I := I) (A := A) (B := B) hI)
    (isAdicHom_commEquiv I hI)

/-! ### The second-factor interchange open immersion -/

/-- **The second-factor interchange open immersion** `Spf(A ⊗̂_R (B{1/g})) ⟶ Spf(A ⊗̂_R B)`,
obtained by geometric conjugation of the left-factor immersion `interchangeOpenImmersion`
(localising the first factor of `B ⊗̂_R A` at `g`) with the commutativity isomorphism `commSpfIso`:

  `commSpfIso.hom ≫ interchangeOpenImmersion ≫ commSpfIso.hom`.

The intermediate objects are presented so that the three composite legs' sources and targets line
up syntactically: the target `Spf((B{1/g}) ⊗̂_R A)` of the first leg matches the source of the
left-factor immersion at `(A := B) (B := A) (f := g)`. -/
def rightInterchangeOpenImmersion (g : B) (hI : I.FG) :
    FormalSpectrum.locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I A
        (FormalSpectrum.awayCompletion (I.map (algebraMap R B)) g)) ⟶
      FormalSpectrum.locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I A B) :=
  (commSpfIso (A := A) (B := FormalSpectrum.awayCompletion (I.map (algebraMap R B)) g) I hI).hom ≫
    interchangeOpenImmersion (A := B) (B := A) I g hI ≫
      (commSpfIso (A := B) (B := A) I hI).hom

/-- **The second-factor interchange open immersion is a `LocallyRingedSpace.IsOpenImmersion`**: it
is the composite of two isomorphisms (`commSpfIso.hom`) with the left-factor open immersion
(`isOpenImmersion_interchangeOpenImmersion`), and isomorphisms are open immersions. -/
theorem isOpenImmersion_rightInterchangeOpenImmersion (g : B) (hI : I.FG) :
    LocallyRingedSpace.IsOpenImmersion (rightInterchangeOpenImmersion (A := A) I g hI) := by
  haveI := isOpenImmersion_interchangeOpenImmersion (A := B) (B := A) I g hI
  unfold rightInterchangeOpenImmersion
  infer_instance

/-! ### The range of the second-factor interchange immersion -/

/-- The preimage of the basic open `D(inr_{A,B} g) ⊆ Spf(A ⊗̂_R B)` under the base map of the
inverse `commSpfIso.inv` (`= mapTop` of `commEquiv`) is the basic open
`D(inl_{B,A} g) ⊆ Spf(B ⊗̂_R A)`: the level map sends the class of `inl_{B,A} g` to that of
`inr_{A,B} g` (`commEquiv_inl`), and
`FormalSpectrum.map_preimage_basicOpen` turns preimages of basic opens into basic opens. -/
theorem commSpfIso_inv_base_preimage_basicOpen (g : B) (hI : I.FG) :
    ⇑(commSpfIso (A := B) (B := A) I hI).inv.base ⁻¹'
        (FormalSpectrum.basicOpen (CompletedTensorProduct.idealOfDefinition R I B A)
          (CompletedTensorProduct.inl R I B A g) :
          Set (FormalSpectrum (CompletedTensorProduct.idealOfDefinition R I B A))) =
      (FormalSpectrum.basicOpen (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inr R I A B g) :
        Set (FormalSpectrum (CompletedTensorProduct.idealOfDefinition R I A B))) := by
  have hval :
      (CompletedTensorProduct.commEquiv (R := R) (I := I) (A := B) (B := A) hI).toRingHom
        (CompletedTensorProduct.inl R I B A g) = CompletedTensorProduct.inr R I A B g :=
    CompletedTensorProduct.commEquiv_inl (R := R) (I := I) (A := B) (B := A) hI g
  have hpre := FormalSpectrum.map_preimage_basicOpen
    (CompletedTensorProduct.idealOfDefinition R I B A)
    (CompletedTensorProduct.idealOfDefinition R I A B)
    (CompletedTensorProduct.commEquiv (R := R) (I := I) (A := B) (B := A) hI).toRingHom
    (isAdicHom_commEquiv (A := B) (B := A) I hI).le_comap
    (CompletedTensorProduct.inl R I B A g)
  rw [hval] at hpre
  have hset := congrArg (fun U : TopologicalSpace.Opens
      (FormalSpectrum (CompletedTensorProduct.idealOfDefinition R I A B)) =>
      (↑U : Set (FormalSpectrum (CompletedTensorProduct.idealOfDefinition R I A B)))) hpre
  exact hset

/-- **The underlying-space range of the second-factor interchange open immersion** is the basic
open `D(inr_{A,B} g) ⊆ Spf(A ⊗̂_R B)`. The base map factors as an isomorphism (surjective) followed
by the left-factor immersion followed by an isomorphism; stripping the leading iso with
`range_iso_hom_comp_base`, computing the left-factor range with
`range_interchangeOpenImmersion_base`, and transporting the image across the trailing iso
(`commSpfIso_inv_base_preimage_basicOpen`) gives `D(inr g)`. -/
theorem range_rightInterchangeOpenImmersion_base (g : B) (hI : I.FG) :
    Set.range (rightInterchangeOpenImmersion (A := A) I g hI).base =
      (FormalSpectrum.basicOpen (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inr R I A B g) :
        Set (FormalSpectrum (CompletedTensorProduct.idealOfDefinition R I A B))) := by
  unfold rightInterchangeOpenImmersion
  rw [range_iso_hom_comp_base]
  have hcomp : ⇑(interchangeOpenImmersion (A := B) (B := A) I g hI ≫
        (commSpfIso (A := B) (B := A) I hI).hom).base =
      ⇑(commSpfIso (A := B) (B := A) I hI).hom.base ∘
        ⇑(interchangeOpenImmersion (A := B) (B := A) I g hI).base := by
    ext x
    simp only [LocallyRingedSpace.comp_toHom, PresheafedSpace.comp_base, TopCat.hom_comp,
      ContinuousMap.coe_comp, Function.comp_apply]
  rw [hcomp, Set.range_comp,
    range_interchangeOpenImmersion_base (A := B) (B := A) I g hI,
    ← commSpfIso_inv_base_preimage_basicOpen I g hI]
  exact congrFun (Set.image_eq_preimage_of_inverse
    (LocallyRingedSpace.iso_hom_base_inv_base_apply (commSpfIso (A := B) (B := A) I hI))
    (LocallyRingedSpace.iso_inv_base_hom_base_apply (commSpfIso (A := B) (B := A) I hI))) _

end CompletedTensorAwayInterchange
