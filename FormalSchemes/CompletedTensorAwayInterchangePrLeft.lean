import FormalSchemes.CompletedTensorAwayInterchangeSpf
import FormalSchemes.AffineFibreProduct

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Naturality of the first projection under the away-localization interchange

The away-localization interchange open immersion
`CompletedTensorAwayInterchange.interchangeOpenImmersion`
(`FormalSchemes.CompletedTensorAwayInterchangeSpf`) realises the localise-then-tensor chart
`Spf((A{1/f}) ⊗̂_R B)` as the basic open `D(f̄) ⊆ Spf(A ⊗̂_R B)`. This file records how it behaves
under the **first** fibre-product projection `fibrePr₁ = Spf(inl) : Spf(A ⊗̂_R B) ⟶ Spf A`. Unlike
the second projection (where the affine base `Spf B` is untouched by the localisation, see
`FormalSchemes.CompletedTensorAwayInterchangePr`), the first factor *is* localised, so composing the
interchange with the first projection lands in `Spf A` via the affine basic-open chart of `A`:

`interchange ≫ Spf(inl : A → A ⊗̂_R B) = Spf(inl : A{1/f} → A{1/f} ⊗̂_R B) ≫ Spf(A → A{1/f})`.

This is the away-localization / first-factor counterpart of the `mapSpf`-naturality square
`mapSpf_comp_fibrePr₁` (`FormalSchemes.CompletedTensorMapSpfPr`): together they are the two data a
*glued* fibre product `X ×_S Y` consumes on double overlaps to make the glued **first** projection
`pr₁ : X ×_S Y ⟶ X` well defined across charts, when the base `X` is glued (as for the two-patch
fibre product of issue 236 and the Tate self-product of issues 228/237).

Everything is phrased directly in terms of `FormalSpectrum.locallyRingedSpaceMap` of the two `inl`
homomorphisms and the structural completion map `awayCompletionHom` (of which `fibrePr₁` and the
affine basic-open chart are, respectively, definitionally the same locally-ringed-space maps), so it
needs no adic-ring instances and applies after unfolding `fibrePr₁`.

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

/-- The `le_comap` datum for the affine basic-open chart of `A` at `f`, phrased with the ideal of
definition `I·(A{1/f})` of `A{1/f}` (rather than `awayCompletionIdeal`). -/
theorem le_comap_awayCompletionHom_base :
    I.map (algebraMap R A) ≤
      (I.map (algebraMap R (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f))).comap
        (FormalSpectrum.awayCompletionHom (I.map (algebraMap R A)) f) := by
  rw [FormalSpectrum.map_algebraMap_awayCompletion_eq]
  exact FormalSpectrum.le_comap_awayCompletionHom (I.map (algebraMap R A)) f

/-- **The interchange open immersion followed by the first projection is the localised first
projection followed by the basic-open chart of `A`.** Composing the away-localization interchange
chart `Spf((A{1/f}) ⊗̂_R B) ⟶ Spf(A ⊗̂_R B)` with the first fibre-product projection
`fibrePr₁ = Spf(inl) : Spf(A ⊗̂_R B) ⟶ Spf A` recovers the first projection of the localised chart
`Spf((A{1/f}) ⊗̂_R B) ⟶ Spf(A{1/f})` followed by the affine basic-open chart `Spf(A{1/f}) ⟶ Spf A`.
Phrased via `locallyRingedSpaceMap` of the two `inl`s and the completion map `awayCompletionHom`;
`fibrePr₁` unfolds to exactly the `inl` maps. -/
theorem interchangeOpenImmersion_comp_locallyRingedSpaceMap_inl (hI : I.FG) :
    interchangeOpenImmersion I f hI ≫
        FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R A))
          (CompletedTensorProduct.idealOfDefinition R I A B)
          (CompletedTensorProduct.inl R I A B).toRingHom
          CompletedTensorProduct.inl_isAdicHom.le_comap =
      FormalSpectrum.locallyRingedSpaceMap
          (I.map (algebraMap R (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f)))
          (CompletedTensorProduct.idealOfDefinition R I
            (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)
          (CompletedTensorProduct.inl R I
            (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B).toRingHom
          CompletedTensorProduct.inl_isAdicHom.le_comap ≫
        FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R A))
          (I.map (algebraMap R (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f)))
          (FormalSpectrum.awayCompletionHom (I.map (algebraMap R A)) f)
          (le_comap_awayCompletionHom_base I f) := by
  -- Adic-morphism side conditions for fusing the three `locallyRingedSpaceMap`s on the left.
  have haway : IsAdicHom (CompletedTensorProduct.idealOfDefinition R I A B)
      (FormalSpectrum.awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f))
      (FormalSpectrum.awayCompletionHom (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f)) :=
    FormalSpectrum.map_awayCompletionHom _ _
  have h1 : IsAdicHom (I.map (algebraMap R A))
      (FormalSpectrum.awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f))
      ((FormalSpectrum.awayCompletionHom (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f)).comp
        (CompletedTensorProduct.inl R I A B).toRingHom) :=
    (CompletedTensorProduct.inl_isAdicHom (R := R) (I := I) (A := A) (B := B)).comp haway
  have hsymm : IsAdicHom
      (FormalSpectrum.awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f))
      (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)
      (equiv I f hI).symm.toRingHom :=
    FormalSpectrum.isAdicHom_ringEquiv_symm (equiv I f hI) (isAdicHom_equiv I f hI)
  have h2 := h1.comp hsymm
  -- Adic-morphism side condition for fusing the two `locallyRingedSpaceMap`s on the right.
  have h3 : I.map (algebraMap R A) ≤ Ideal.comap
      ((CompletedTensorProduct.inl R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B).toRingHom.comp
        (FormalSpectrum.awayCompletionHom (I.map (algebraMap R A)) f))
      (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B) := by
    rw [← Ideal.comap_comap]
    exact (le_comap_awayCompletionHom_base I f).trans
      (Ideal.comap_mono CompletedTensorProduct.inl_isAdicHom.le_comap)
  rw [interchangeOpenImmersion, equivSpfIso, FormalSpectrum.isoOfAdicRingEquiv, basicOpenChart,
    Category.assoc,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (I.map (algebraMap R A)) (CompletedTensorProduct.idealOfDefinition R I A B)
      (FormalSpectrum.awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f))
      (CompletedTensorProduct.inl R I A B).toRingHom
      (FormalSpectrum.awayCompletionHom (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f))
      CompletedTensorProduct.inl_isAdicHom.le_comap
      (FormalSpectrum.le_comap_awayCompletionHom _ _) h1.le_comap,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (I.map (algebraMap R A))
      (FormalSpectrum.awayCompletionIdeal (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f))
      (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)
      ((FormalSpectrum.awayCompletionHom (CompletedTensorProduct.idealOfDefinition R I A B)
        (CompletedTensorProduct.inl R I A B f)).comp
        (CompletedTensorProduct.inl R I A B).toRingHom)
      (equiv I f hI).symm.toRingHom h1.le_comap hsymm.le_comap h2.le_comap,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (I.map (algebraMap R A))
      (I.map (algebraMap R (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f)))
      (CompletedTensorProduct.idealOfDefinition R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B)
      (FormalSpectrum.awayCompletionHom (I.map (algebraMap R A)) f)
      (CompletedTensorProduct.inl R I
        (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) f) B).toRingHom
      (le_comap_awayCompletionHom_base I f) CompletedTensorProduct.inl_isAdicHom.le_comap h3]
  refine FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _ ?_
  refine RingHom.ext fun a => ?_
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  change (equiv I f hI).symm _ = _
  rw [RingEquiv.symm_apply_eq, equiv_apply, forwardHom_inl]
  -- Both sides now `A{1/f̄}`-elements; reduce to localization functoriality of `awayMapₐ`.
  simp only [FormalSpectrum.awayCompletionHom, RingHom.comp_apply, forwardAwayHom_algebraMap]
  congr 1
  simp only [Localization.awayMapₐ, IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map]
  exact (IsLocalization.map_eq _ a).symm

end CompletedTensorAwayInterchange
