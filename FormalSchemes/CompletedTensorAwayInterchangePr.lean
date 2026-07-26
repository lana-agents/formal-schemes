import FormalSchemes.CompletedTensorAwayInterchangeSpf
import FormalSchemes.AffineFibreProduct

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Naturality of the second projection under the away-localization interchange

The away-localization interchange open immersion
`CompletedTensorAwayInterchange.interchangeOpenImmersion`
(`FormalSchemes.CompletedTensorAwayInterchangeSpf`) realises the localise-then-tensor chart
`Spf((A{1/f}) ⊗̂_R B)` as the basic open `D(f̄) ⊆ Spf(A ⊗̂_R B)`. This file records that it is a
morphism **over the affine base `Spf B`**: composing it with the second fibre-product projection
`fibrePr₂ = Spf(inr) : Spf(A ⊗̂_R B) ⟶ Spf B` recovers the second projection of the localised chart
`Spf((A{1/f}) ⊗̂_R B) ⟶ Spf B`.

This is the away-localization counterpart of the `mapSpf`-naturality square
`mapSpf_comp_fibrePr₂` (`FormalSchemes.CompletedTensorMapSpfPr`): together they are the two data a
*glued* fibre product `X ×_S Y` consumes on double overlaps to make the glued projection
`pr₂ : X ×_S Y ⟶ Y` well defined across charts. It feeds the projections of the two-patch fibre
product (issue 236) and the Tate self-product (issues 228/237), and the general fibre product
(issue 227).

The statement is phrased directly in terms of `FormalSpectrum.locallyRingedSpaceMap` of the two
`inr` homomorphisms (of which `fibrePr₂` is `IsAdicHom.spfMap`, i.e. definitionally the same
locally-ringed-space map), so it needs no adic-ring instances and applies after unfolding
`fibrePr₂`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum

universe u

namespace CompletedTensorAwayInterchange

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable (f : A)

/-- **The interchange open immersion is a morphism over the affine base `Spf B`.** Composing the
away-localization interchange chart `Spf((A{1/f}) ⊗̂_R B) ⟶ Spf(A ⊗̂_R B)` with the second
projection `fibrePr₂ = Spf(inr) : Spf(A ⊗̂_R B) ⟶ Spf B` recovers the second projection of the
localised chart. Phrased via `locallyRingedSpaceMap` of the two `inr`s; `fibrePr₂` unfolds to
exactly these maps. -/
theorem interchangeOpenImmersion_comp_locallyRingedSpaceMap_inr (hI : I.FG) :
    interchangeOpenImmersion I f hI ≫
        FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R B))
          (CompletedTensorProduct.idealOfDefinition R I A B)
          (CompletedTensorProduct.inr R I A B).toRingHom
          CompletedTensorProduct.inr_isAdicHom.le_comap =
      FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R B))
          (CompletedTensorProduct.idealOfDefinition R I
            (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)
          (CompletedTensorProduct.inr R I
            (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B).toRingHom
          CompletedTensorProduct.inr_isAdicHom.le_comap := by
  have haway : IsAdicHom (CompletedTensorProduct.idealOfDefinition R I A B)
      (FormalSpectrum.awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f))
      (FormalSpectrum.awayCompletionHom (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f)) :=
    FormalSpectrum.map_awayCompletionHom _ _
  have h1 : IsAdicHom (I.map (algebraMap R B))
      (FormalSpectrum.awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f))
      ((FormalSpectrum.awayCompletionHom (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f)).comp
        (CompletedTensorProduct.inr R I A B).toRingHom) :=
    (CompletedTensorProduct.inr_isAdicHom (R := R) (I := I) (A := A) (B := B)).comp haway
  have hsymm : IsAdicHom
      (FormalSpectrum.awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f))
      (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)
      (equiv I f hI).symm.toRingHom :=
    FormalSpectrum.isAdicHom_ringEquiv_symm (equiv I f hI) (isAdicHom_equiv I f hI)
  have h2 := h1.comp hsymm
  rw [interchangeOpenImmersion, equivSpfIso, FormalSpectrum.isoOfAdicRingEquiv, basicOpenChart,
    Category.assoc,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (I.map (algebraMap R B)) (CompletedTensorProduct.idealOfDefinition R I A B)
      (FormalSpectrum.awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f))
      (CompletedTensorProduct.inr R I A B).toRingHom
      (FormalSpectrum.awayCompletionHom (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f))
      CompletedTensorProduct.inr_isAdicHom.le_comap
      (FormalSpectrum.le_comap_awayCompletionHom _ _) h1.le_comap,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (I.map (algebraMap R B))
      (FormalSpectrum.awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f))
      (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)
      ((FormalSpectrum.awayCompletionHom (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f)).comp
        (CompletedTensorProduct.inr R I A B).toRingHom)
      (equiv I f hI).symm.toRingHom h1.le_comap hsymm.le_comap h2.le_comap]
  refine FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _ ?_
  refine RingHom.ext fun b => ?_
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  change (equiv I f hI).symm _ = _
  rw [RingEquiv.symm_apply_eq, equiv_apply, forwardHom_inr, forwardHomB_apply]

end CompletedTensorAwayInterchange
