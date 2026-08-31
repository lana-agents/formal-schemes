import FormalSchemes.CompletedTensorAwayInterchange
import FormalSchemes.BasicOpenImmersionLRS
import FormalSchemes.AdicMorphism
import FormalSchemes.SpfRingEquivIso

set_option linter.style.header false
-- The formal-spectrum morphisms range over the nested localization/completion towers of the
-- completed tensor product, which are slow for the elaborator and the kernel; raise the budgets.
set_option linter.style.setOption false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The geometric completed-tensor / away-localization interchange

The ring-level interchange `CompletedTensorAwayInterchange.equiv`
(`FormalSchemes/CompletedTensorAwayInterchange.lean`) identifies the two ways of building "the
completed tensor product with the `f`-chart of `A`":

* localise-then-tensor `L = (A{1/f}) ⊗̂_R B = CompletedTensorProduct R I (A{1/f}) B`;
* tensor-then-localise `T = (A ⊗̂_R B){1/f̄} = C{1/f̄}`,

as complete adic `R`-algebras, carrying the ideal of definition of the left (`IL`) onto that of the
right (`IT`) via `equiv_map_idealOfDefinition`. This file promotes that ring isomorphism to the
*geometric* statement on affine formal spectra: the induced isomorphism of formal spectra
`Spf L ≅ Spf T`, and the resulting open immersion `Spf L ↪ Spf C` onto the basic open `D(f̄)`.

This is the overlap datum `Spf(A{1/f} ⊗̂_R B) ↪ Spf(A ⊗̂_R B)` used in the general glued fibre
product of formal schemes: it exhibits the localise-then-tensor patch as the open subscheme of the
tensor `Spf C` cut out by the invertibility of `f̄ = inl f`.

## Main results

* `CompletedTensorAwayInterchange.equivSpfIso`: the isomorphism of affine formal spectra
  `Spf IL ≅ Spf IT` induced by the ring isomorphism `equiv`.
* `CompletedTensorAwayInterchange.interchangeOpenImmersion`: the morphism
  `Spf IL ⟶ Spf C` given by `equivSpfIso.hom` followed by the basic-open chart at `f̄`.
* `CompletedTensorAwayInterchange.isOpenImmersion_interchangeOpenImmersion`: it is a
  `LocallyRingedSpace.IsOpenImmersion`.
* `CompletedTensorAwayInterchange.range_interchangeOpenImmersion_base`: its underlying-space range
  is the basic open `D(f̄) ⊆ Spf C`.

The abstract construction the first of those runs on — `FormalSpectrum.isoOfAdicRingEquiv`, an
isomorphism of formal spectra from a ring isomorphism carrying one ideal of definition onto the
other — was written here but is not about completed tensor products, and now lives in
`FormalSchemes.SpfRingEquivIso` with the three lemmas it uses. Nothing about it changed.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Ideal

universe u

/-- Bridging the two coercions of a ring isomorphism into `Ideal.map`: mapping an ideal along the
underlying ring homomorphism `e.toRingHom` agrees with mapping along `e` itself. Definitionally
true (both use the underlying function), and cheap — it avoids forcing the elaborator to unfold a
large concrete isomorphism to reconcile the two coercions. -/
theorem Ideal.map_ringEquiv_toRingHom {S T : Type*} [CommRing S] [CommRing T]
    (e : S ≃+* T) (J : Ideal S) : J.map e.toRingHom = J.map e := rfl

namespace CompletedTensorAwayInterchange

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable (f : A)

/-! ### The two adic homomorphisms

`IsAdicHom I J φ` is *definitionally* `I.map φ = J`; both directions of the ideal-of-definition
transport are recorded here, so that each induces a morphism of formal spectra via
`FormalSpectrum.locallyRingedSpaceMap`. -/

/-- The interchange isomorphism is an **adic homomorphism** `IL → IT`: it carries the ideal of
definition of `L = (A{1/f}) ⊗̂_R B` onto that of `T = C{1/f̄}`. This is just
`equiv_map_idealOfDefinition` read through the definition of `IsAdicHom`. -/
theorem isAdicHom_equiv (hI : I.FG) :
    IsAdicHom
      (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)
      (FormalSpectrum.awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f))
      (equiv I f hI).toRingHom := by
  have : (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B).map
        (equiv I f hI).toRingHom =
      FormalSpectrum.awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f) := by
    rw [Ideal.map_ringEquiv_toRingHom]
    exact equiv_map_idealOfDefinition I f hI
  exact this

/-! ### The induced isomorphism of formal spectra -/

/-- **The interchange isomorphism of affine formal spectra** `Spf IL ≅ Spf IT`, induced by the ring
isomorphism `equiv` via the abstract construction `FormalSpectrum.isoOfAdicRingEquiv` applied to the
adic homomorphism `isAdicHom_equiv`. -/
def equivSpfIso (hI : I.FG) :
    FormalSpectrum.locallyRingedSpaceObj
        (CompletedTensorProduct.idealOfDefinition R I
          (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B) ≅
      FormalSpectrum.locallyRingedSpaceObj
        (FormalSpectrum.awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
          (CompletedTensorProduct.inl R I A B f)) :=
  FormalSpectrum.isoOfAdicRingEquiv _ _ (equiv I f hI) (isAdicHom_equiv I f hI)

/-! ### The open immersion onto the basic open `D(f̄)` -/

/-- The ideal of definition of `C = A ⊗̂_R B` is finitely generated when `I` is: it is the
extension `I·C`. -/
theorem idealOfDefinition_fg (hI : I.FG) :
    (CompletedTensorProduct.idealOfDefinition R I A B).FG := by
  rw [CompletedTensorProduct.idealOfDefinition_eq_map]
  exact hI.map _

/-- **The interchange open immersion** `Spf IL ⟶ Spf C`: the isomorphism of formal spectra
`equivSpfIso` followed by the affine basic-open chart of `C` at `f̄ = inl f`. This is the overlap
datum realising `Spf((A{1/f}) ⊗̂_R B)` as the open subscheme `D(f̄) ⊆ Spf(A ⊗̂_R B)`. -/
def interchangeOpenImmersion (hI : I.FG) :
    FormalSpectrum.locallyRingedSpaceObj
        (CompletedTensorProduct.idealOfDefinition R I
          (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B) ⟶
      FormalSpectrum.locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I A B) :=
  (equivSpfIso I f hI).hom ≫
    FormalSpectrum.basicOpenChart (CompletedTensorProduct.idealOfDefinition R I A B)
      (CompletedTensorProduct.inl R I A B f)

/-- **The interchange open immersion is a `LocallyRingedSpace.IsOpenImmersion`**: it is the
composite of an isomorphism (`equivSpfIso.hom`) with the basic-open chart, which is an open
immersion for `I` (hence `I·C`) finitely generated
(`FormalSpectrum.isOpenImmersion_basicOpenChart`). -/
theorem isOpenImmersion_interchangeOpenImmersion (hI : I.FG) :
    LocallyRingedSpace.IsOpenImmersion (interchangeOpenImmersion (B := B) I f hI) := by
  haveI := FormalSpectrum.isOpenImmersion_basicOpenChart
    (CompletedTensorProduct.idealOfDefinition R I A B) (CompletedTensorProduct.inl R I A B f)
    (idealOfDefinition_fg I hI)
  unfold interchangeOpenImmersion
  infer_instance

/-- The underlying-space **range** of the interchange open immersion is the basic open
`D(f̄) ⊆ Spf C`: the base map factors as an isomorphism (surjective) followed by the chart's base
map, whose range is `D(f̄)` (`FormalSpectrum.range_basicOpenChart_base`). -/
theorem range_interchangeOpenImmersion_base (hI : I.FG) :
    Set.range (interchangeOpenImmersion (B := B) I f hI).base =
      (FormalSpectrum.basicOpen (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f) :
        Set (FormalSpectrum (CompletedTensorProduct.idealOfDefinition R I A B))) := by
  have hsurj : Function.Surjective ⇑(equivSpfIso (B := B) I f hI).hom.base := fun y =>
    ⟨(equivSpfIso (B := B) I f hI).inv.base y,
      LocallyRingedSpace.iso_inv_base_hom_base_apply (equivSpfIso (B := B) I f hI) y⟩
  have hbase : (interchangeOpenImmersion (B := B) I f hI).base =
      (equivSpfIso (B := B) I f hI).hom.base ≫
        (FormalSpectrum.basicOpenChart (CompletedTensorProduct.idealOfDefinition R I A B)
          (CompletedTensorProduct.inl R I A B f)).base := rfl
  rw [hbase, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr hsurj, Set.image_univ]
  exact FormalSpectrum.range_basicOpenChart_base _ _ (idealOfDefinition_fg I hI)

end CompletedTensorAwayInterchange
