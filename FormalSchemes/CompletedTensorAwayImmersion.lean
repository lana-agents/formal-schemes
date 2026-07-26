import FormalSchemes.CompletedTensorAwayInterchange
import FormalSchemes.SpfFunctorial
import FormalSchemes.BasicOpenImmersionLRS

set_option linter.style.header false
-- The interchange ring maps live over nested localization/completion towers; keep the elaborator,
-- instance-cache and kernel budgets generous, matching `CompletedTensorAwayInterchange.lean`.
set_option linter.style.setOption false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The overlap open immersion for the general fibre product

Fix an adic base `(R, I)` with `I` finitely generated, two `R`-algebras `A` and `B`, and an element
`f : A`. Write `C = A ⊗̂_R B = CompletedTensorProduct R I A B` and
`f̄ = CompletedTensorProduct.inl R I A B f : C` for the image `f ⊗ 1`. The completed-tensor /
away-localization interchange
(`FormalSchemes/CompletedTensorAwayInterchange.lean`) is the ring isomorphism
`equiv : (A{1/f}) ⊗̂_R B ≃+* C{1/f̄}` carrying the ideal of definition of the left onto that of the
right. This file records its **geometric incarnation**: the induced open immersion of affine formal
schemes
```
Spf((A{1/f}) ⊗̂_R B) ↪ Spf(A ⊗̂_R B)
```
onto the basic open `D(f̄) ⊆ Spf(A ⊗̂_R B)`.

This is the concrete overlap datum the **general glued fibre product** of formal schemes (EGA I
§10.7, issues 226/227) glues along on double overlaps: when one builds `X ×_{Spf R} Spf B` (or the
full `X ×_S Y`) by gluing the affine charts `Spf(A_i ⊗̂_R B)`, the overlap of two charts is the base
change of the overlap `D(f) ⊆ Spf A_i` of `X`, and identifying "restrict the affine product to
`D(f̄)`" with "the affine product of the restricted chart `Spf A_i{1/f}` with `Spf B`" is exactly
this open immersion.

The construction mirrors the affine basic-open completion immersion
`formalCompletion.basicOpenImmersion` (`FormalSchemes/CompletionBasicOpen.lean`): the interchange
isomorphism, transported to formal spectra by the merged `Spf`-functor laws, followed by the affine
basic-open chart `FormalSpectrum.basicOpenChart` of `Spf C` at `f̄`.

## Main definitions and results

* `CompletedTensorAwayInterchange.chartIso`: `Spf` of the interchange ring isomorphism, identifying
  `Spf((A{1/f}) ⊗̂_R B)` with the source `Spf(C{1/f̄})` of the affine basic-open chart of `Spf C`.
* `CompletedTensorAwayInterchange.overlapChart`: the overlap morphism
  `Spf((A{1/f}) ⊗̂_R B) ⟶ Spf(A ⊗̂_R B)`.
* `CompletedTensorAwayInterchange.overlapChart_isOpenImmersion`: it is an open immersion.
* `CompletedTensorAwayInterchange.range_overlapChart`: its range is the basic open `D(f̄)`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
-/

noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry FormalSpectrum

universe u

namespace CompletedTensorAwayInterchange

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable (f : A)

/-- The ideal of definition of the affine fibre product `A ⊗̂_R B` is finitely generated (it is the
extension of the finitely generated `I` along the structure map). -/
theorem tensorIdealOfDefinition_fg (hI : I.FG) :
    (CompletedTensorProduct.idealOfDefinition R I A B).FG := by
  rw [CompletedTensorProduct.idealOfDefinition_eq_map]
  exact hI.map _

/-- `backwardHom` carries the ideal of definition of the tensor-then-localise ring `C{1/f̄}` into
that of the localise-then-tensor ring `(A{1/f}) ⊗̂_R B` (the `m = 1` case of continuity). -/
theorem backwardHom_le_comap (hI : I.FG) :
    awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f) ≤
      (CompletedTensorProduct.idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R A)) f) B).comap (backwardHom I f hI) := by
  intro x hx
  rw [Ideal.mem_comap]
  have := backwardHom_mem_pow I f hI 1 (by rwa [pow_one] : x ∈ _ ^ 1)
  rwa [pow_one] at this

/-- `forwardHom` carries the ideal of definition of `(A{1/f}) ⊗̂_R B` into that of `C{1/f̄}` (the
`m = 1` case of continuity). -/
theorem forwardHom_le_comap (hI : I.FG) :
    CompletedTensorProduct.idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R A)) f) B ≤
      (awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f)).comap (forwardHom I f hI) := by
  intro x hx
  rw [Ideal.mem_comap]
  have := forwardHom_mem_pow I f hI 1 (by rwa [pow_one] : x ∈ _ ^ 1)
  rwa [pow_one] at this

/-- **The interchange isomorphism as an isomorphism of formal spectra.** `Spf` of the ring
isomorphism `equiv`, identifying the underlying locally ringed space of `Spf((A{1/f}) ⊗̂_R B)` with
that of the source `Spf(C{1/f̄})` of the affine basic-open chart of `Spf C`. The two `Spf`-morphisms
are mutually inverse because the interchange is a ring isomorphism, via the merged `Spf`-functor
laws. -/
def chartIso (hI : I.FG) :
    locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R A)) f) B) ≅
      locallyRingedSpaceObj (awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f)) where
  hom := locallyRingedSpaceMap _ _ (backwardHom I f hI) (backwardHom_le_comap I f hI)
  inv := locallyRingedSpaceMap _ _ (forwardHom I f hI) (forwardHom_le_comap I f hI)
  hom_inv_id := by
    have hIK : CompletedTensorProduct.idealOfDefinition R I
          (awayCompletion (I.map (algebraMap R A)) f) B ≤
        (CompletedTensorProduct.idealOfDefinition R I
          (awayCompletion (I.map (algebraMap R A)) f) B).comap
          ((backwardHom I f hI).comp (forwardHom I f hI)) := by
      rw [backward_comp_forward]; exact (Ideal.comap_id _).ge
    rw [← locallyRingedSpaceMap_comp (hIK := hIK),
      locallyRingedSpaceMap_congr (φ₂ := RingHom.id _) (hφ := backward_comp_forward I f hI)]
    exact locallyRingedSpaceMap_id _
  inv_hom_id := by
    have hIK : awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
          (CompletedTensorProduct.inl R I A B f) ≤
        (awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
          (CompletedTensorProduct.inl R I A B f)).comap
          ((forwardHom I f hI).comp (backwardHom I f hI)) := by
      rw [forward_comp_backward]; exact (Ideal.comap_id _).ge
    rw [← locallyRingedSpaceMap_comp (hIK := hIK),
      locallyRingedSpaceMap_congr (φ₂ := RingHom.id _) (hφ := forward_comp_backward I f hI)]
    exact locallyRingedSpaceMap_id _

/-- **The overlap open immersion** `Spf((A{1/f}) ⊗̂_R B) ⟶ Spf(A ⊗̂_R B)`: the interchange
isomorphism `chartIso` followed by the affine basic-open chart of `Spf(A ⊗̂_R B)` at
`f̄ = f ⊗ 1`. This is the concrete overlap datum the general glued fibre product glues along on
double overlaps. -/
def overlapChart (hI : I.FG) :
    locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R A)) f) B) ⟶
      locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I A B) :=
  (chartIso I f hI).hom ≫
    basicOpenChart (CompletedTensorProduct.idealOfDefinition R I A B)
      (CompletedTensorProduct.inl R I A B f)

/-- **The overlap chart is an open immersion**: an isomorphism (`chartIso`) followed by the affine
basic-open chart open immersion (`isOpenImmersion_basicOpenChart`). -/
instance overlapChart_isOpenImmersion (hI : I.FG) :
    LocallyRingedSpace.IsOpenImmersion (overlapChart (B := B) I f hI) := by
  haveI : LocallyRingedSpace.IsOpenImmersion
      (basicOpenChart (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f)) :=
    isOpenImmersion_basicOpenChart (CompletedTensorProduct.idealOfDefinition R I A B)
      (CompletedTensorProduct.inl R I A B f) (tensorIdealOfDefinition_fg I hI)
  change LocallyRingedSpace.IsOpenImmersion
    ((chartIso I f hI).hom ≫
      basicOpenChart (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f))
  exact LocallyRingedSpace.IsOpenImmersion.comp _ _

/-- **The range of the overlap chart is the basic open `D(f̄)`** of `Spf(A ⊗̂_R B)`, where
`f̄ = f ⊗ 1`. The underlying map factors as the affine basic-open chart (range `D(f̄)`) after the
surjective iso `chartIso`. -/
theorem range_overlapChart (hI : I.FG) :
    Set.range (overlapChart I f hI).base =
      (basicOpen (CompletedTensorProduct.idealOfDefinition R I A B)
          (CompletedTensorProduct.inl R I A B f) :
        Set (FormalSpectrum (CompletedTensorProduct.idealOfDefinition R I A B))) := by
  have hsurj : Function.Surjective ⇑(chartIso (B := B) I f hI).hom.base := by
    intro x
    refine ⟨(chartIso I f hI).inv.base x, ?_⟩
    have hx : ((chartIso I f hI).inv ≫ (chartIso I f hI).hom).base x = x := by
      rw [(chartIso I f hI).inv_hom_id]; rfl
    simpa only [LocallyRingedSpace.comp_toHom, PresheafedSpace.comp_base, TopCat.hom_comp,
      ContinuousMap.coe_comp, Function.comp_apply] using hx
  change Set.range ⇑(((chartIso I f hI).hom ≫
    basicOpenChart (CompletedTensorProduct.idealOfDefinition R I A B)
      (CompletedTensorProduct.inl R I A B f)).base) = _
  have hcomp : ⇑(((chartIso I f hI).hom ≫
        basicOpenChart (CompletedTensorProduct.idealOfDefinition R I A B)
          (CompletedTensorProduct.inl R I A B f)).base) =
      ⇑(basicOpenChart (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f)).base ∘
        ⇑(chartIso I f hI).hom.base := by
    ext x
    simp only [LocallyRingedSpace.comp_toHom, PresheafedSpace.comp_base, TopCat.hom_comp,
      ContinuousMap.coe_comp, Function.comp_apply]
  rw [hcomp, Set.range_comp, Set.range_eq_univ.mpr hsurj, Set.image_univ]
  exact range_basicOpenChart_base (CompletedTensorProduct.idealOfDefinition R I A B)
    (CompletedTensorProduct.inl R I A B f) (tensorIdealOfDefinition_fg I hI)

end CompletedTensorAwayInterchange

end
