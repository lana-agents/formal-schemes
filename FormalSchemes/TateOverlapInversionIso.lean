import FormalSchemes.TateChartTransition
import FormalSchemes.TateOverlapInversion

set_option linter.style.header false
set_option linter.style.show false

/-!
# The geometric 𝔾m-inversion overlap transition of the Tate curve

Fix an adic ring `R` with finitely generated ideal of definition `I` and a Tate parameter `q : R`,
and let `A = R{x, y} / (x·y − q)` be the coordinate ring of the formal Tate annulus. Issue 436
(`FormalSchemes.TateOverlapInversion`) delivered the **ring-level** 𝔾m-inversion transition

```
annulusOverlapInversion : A[x⁻¹]^∧  ≃+*  A[y⁻¹]^∧
```

realising `X ↦ Y⁻¹` (the genuine Néron 2-gon gluing, contrasting the coordinate-swap
`annulusOverlapTransition` which realises `X ↦ Y` and yields the *non-separated*
line-with-doubled-origin). This file promotes that ring isomorphism to the **geometric** level,
mirroring the existing flip pipeline (`FormalSchemes.TateOverlapTransitionIso`,
`FormalSchemes.TateChartTransition`) verbatim with an `…Inv` suffix. Everything here is **purely
additive**: no existing declaration is modified, so nothing downstream breaks. This is the safe
prerequisite that the model rewire (issue 435c) will consume to make `𝔈_q = tateCurveModel`
separated.

## Main results

* `annulusOverlapInversion_isAdicHom` / `annulusOverlapInversion_symm_isAdicHom`: the inversion ring
  isomorphism and its inverse are **adic homomorphisms** — they carry the ideal of definition of one
  overlap chart onto that of the other. The forward direction factors as the composite of the x-side
  𝔾m-inversion automorphism `annulusOverlapInvX` (which preserves the ideal of definition because it
  fixes the image of the base `R`) with the already-established flip adic homomorphism.
* `annulusOverlapInversionSpf`: the induced isomorphism of locally ringed spaces
  `Spf(A[x⁻¹]^∧) ≅ Spf(A[y⁻¹]^∧)`, the `Spf` of the inversion ring isomorphism.
* `annulusChartTransitionInvSpf`: the geometric overlap transition on the annulus **charts**
  `Spf A{1/x} ≅ Spf A{1/y}`, obtained by conjugating `annulusOverlapInversionSpf` with the two chart
  domain identifications `annulusChartDomainSpfX` / `annulusChartDomainSpfY`.
* `annulusOverlapInversion_symm_comp_algebraMap`: the **`R`-linearity crux** at the ring level — the
  inverse inversion transition composed with `R → A[y⁻¹]^∧` equals `R → A[x⁻¹]^∧`.
  This is the load-bearing ring identity for the geometric structural-map compatibility of the
  corrected model (the `…Inv` analogue of `annulusOverlapTransitionInv_comp_algebraMap`).

**Scope.** This delivers the geometric transition iso for the corrected (inversion) Tate gluing and
the ring-level `R`-linearity crux that its structural-map compatibility rests on. The full geometric
structural-map crux `annulusOverlapChart ≫ s = annulusChartTransitionInvSpf.hom ≫
annulusOverlapChartY ≫ s` (the `…Inv` analogue of `annulusOverlapChart_comp_structMap`,
`FormalSchemes.TateChainStructMap`) is the responsibility of the model rewire (issue 435c), where it
is consumed by `tateCurveModelStructMap`.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4, §10.15.
-/

noncomputable section

open Ideal AlgebraicGeometry CategoryTheory FormalSpectrum

universe u

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- The ideal of definition of `A[x⁻¹]^∧` is the extension of `I` along the structural map
`R → A[x⁻¹]^∧`. (This is `annulusLocIdeal = I·A[x⁻¹]` pushed through the completion, collapsed by
the scalar tower.) -/
theorem idealOfDefinition_annulusLocIdeal_eq :
    AdicCompletion.idealOfDefinition (annulusLocIdeal R I q)
      = I.map (algebraMap R (annulusOverlap R I q)) := by
  rw [show AdicCompletion.idealOfDefinition (annulusLocIdeal R I q)
        = (annulusLocIdeal R I q).map
          (algebraMap (annulusLoc R I q) (annulusOverlap R I q)) from rfl,
    IsScalarTower.algebraMap_eq R (annulusLoc R I q) (annulusOverlap R I q), ← Ideal.map_map]

/-- A ring endomorphism of `A[x⁻¹]^∧` fixing the image of the base `R` preserves the ideal of
definition (which is the extension of `I` along `R → A[x⁻¹]^∧`). -/
theorem isAdicHom_of_fix_algebraMap (φ : annulusOverlap R I q →+* annulusOverlap R I q)
    (hφ : φ.comp (algebraMap R (annulusOverlap R I q)) = algebraMap R (annulusOverlap R I q)) :
    IsAdicHom (AdicCompletion.idealOfDefinition (annulusLocIdeal R I q))
      (AdicCompletion.idealOfDefinition (annulusLocIdeal R I q)) φ := by
  change (AdicCompletion.idealOfDefinition (annulusLocIdeal R I q)).map φ
      = AdicCompletion.idealOfDefinition (annulusLocIdeal R I q)
  rw [idealOfDefinition_annulusLocIdeal_eq, Ideal.map_map, hφ]

variable (hI : I.FG)

/-- The x-side 𝔾m-inversion automorphism fixes the image of the base `R`, as a `RingHom.comp`. -/
theorem annulusOverlapInvX_comp_algebraMap :
    (annulusOverlapInvX R I q hI).toRingHom.comp (algebraMap R (annulusOverlap R I q)) =
      algebraMap R (annulusOverlap R I q) := by
  refine RingHom.ext fun r => ?_
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  exact annulusOverlapInvX_algebraMap R I q hI r

/-- The inverse of the x-side 𝔾m-inversion automorphism also fixes the image of the base `R`. -/
theorem annulusOverlapInvX_symm_comp_algebraMap :
    (annulusOverlapInvX R I q hI).symm.toRingHom.comp (algebraMap R (annulusOverlap R I q)) =
      algebraMap R (annulusOverlap R I q) := by
  refine RingHom.ext fun r => ?_
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [RingEquiv.symm_apply_eq]
  exact (annulusOverlapInvX_algebraMap R I q hI r).symm

/-- The x-side 𝔾m-inversion automorphism is an **adic homomorphism**: it preserves the ideal of
definition of `A[x⁻¹]^∧`, because it fixes the image of the base `R`. -/
theorem annulusOverlapInvX_isAdicHom :
    IsAdicHom (AdicCompletion.idealOfDefinition (annulusLocIdeal R I q))
      (AdicCompletion.idealOfDefinition (annulusLocIdeal R I q))
      (annulusOverlapInvX R I q hI).toRingHom :=
  isAdicHom_of_fix_algebraMap R I q _ (annulusOverlapInvX_comp_algebraMap R I q hI)

/-- The inverse x-side 𝔾m-inversion automorphism is an **adic homomorphism**. -/
theorem annulusOverlapInvX_symm_isAdicHom :
    IsAdicHom (AdicCompletion.idealOfDefinition (annulusLocIdeal R I q))
      (AdicCompletion.idealOfDefinition (annulusLocIdeal R I q))
      (annulusOverlapInvX R I q hI).symm.toRingHom :=
  isAdicHom_of_fix_algebraMap R I q _ (annulusOverlapInvX_symm_comp_algebraMap R I q hI)

/-- The forward inversion transition, as a `RingHom.comp` of the flip transition after the x-side
𝔾m-inversion. -/
theorem annulusOverlapInversion_toRingHom_eq :
    (annulusOverlapInversion R I q hI).toRingHom =
      (annulusOverlapTransitionHom R I q hI).comp (annulusOverlapInvX R I q hI).toRingHom := by
  refine RingHom.ext fun x => ?_
  show annulusOverlapInversion R I q hI x
    = annulusOverlapTransitionHom R I q hI (annulusOverlapInvX R I q hI x)
  rw [annulusOverlapInversion_apply, annulusOverlapTransition_apply]

/-- The inverse inversion transition, as a `RingHom.comp` of the inverse x-side 𝔾m-inversion after
the inverse flip transition. -/
theorem annulusOverlapInversion_symm_toRingHom_eq :
    (annulusOverlapInversion R I q hI).symm.toRingHom =
      (annulusOverlapInvX R I q hI).symm.toRingHom.comp (annulusOverlapTransitionInv R I q hI) := by
  refine RingHom.ext fun y => ?_
  show (annulusOverlapInversion R I q hI).symm y
    = (annulusOverlapInvX R I q hI).symm (annulusOverlapTransitionInv R I q hI y)
  rw [annulusOverlapInversion_symm_apply, annulusOverlapTransition_symm_apply]

/-- **The forward inversion transition is an adic homomorphism**: it carries the ideal of definition
of `A[x⁻¹]^∧` onto that of `A[y⁻¹]^∧`. It factors as the x-side 𝔾m-inversion (ideal-preserving)
followed by the flip transition (`annulusOverlapTransition_isAdicHom`). -/
theorem annulusOverlapInversion_isAdicHom :
    IsAdicHom (AdicCompletion.idealOfDefinition (annulusLocIdeal R I q))
      (AdicCompletion.idealOfDefinition (annulusLocIdealY R I q))
      (annulusOverlapInversion R I q hI).toRingHom := by
  rw [annulusOverlapInversion_toRingHom_eq]
  exact (annulusOverlapInvX_isAdicHom R I q hI).comp (annulusOverlapTransition_isAdicHom R I q hI)

/-- **The inverse inversion transition is an adic homomorphism.** -/
theorem annulusOverlapInversion_symm_isAdicHom :
    IsAdicHom (AdicCompletion.idealOfDefinition (annulusLocIdealY R I q))
      (AdicCompletion.idealOfDefinition (annulusLocIdeal R I q))
      (annulusOverlapInversion R I q hI).symm.toRingHom := by
  rw [annulusOverlapInversion_symm_toRingHom_eq]
  exact (annulusOverlapTransition_symm_isAdicHom R I q hI).comp
    (annulusOverlapInvX_symm_isAdicHom R I q hI)

/-- Left round-trip of the inversion transition: inverse after forward is the identity. -/
theorem annulusOverlapInversion_symm_comp_self :
    (annulusOverlapInversion R I q hI).symm.toRingHom.comp
        (annulusOverlapInversion R I q hI).toRingHom =
      RingHom.id (annulusOverlap R I q) := by
  refine RingHom.ext fun x => ?_
  simp

/-- Right round-trip of the inversion transition: forward after inverse is the identity. -/
theorem annulusOverlapInversion_comp_symm :
    (annulusOverlapInversion R I q hI).toRingHom.comp
        (annulusOverlapInversion R I q hI).symm.toRingHom =
      RingHom.id (annulusOverlapY R I q) := by
  refine RingHom.ext fun y => ?_
  simp

/-- **The geometric 𝔾m-inversion overlap transition** `Spf(A[x⁻¹]^∧) ≅ Spf(A[y⁻¹]^∧)`: the `Spf` of
the inversion ring isomorphism `annulusOverlapInversion` (issue 436). This is the corrected
transition `t_{n,n+1}` of the Tate 2-gon at the level of locally ringed spaces, contrasting the
non-separated flip transition `annulusOverlapTransitionSpf`. -/
def annulusOverlapInversionSpf :
    FormalSpectrum.locallyRingedSpaceObj
        (AdicCompletion.idealOfDefinition (annulusLocIdeal R I q)) ≅
      FormalSpectrum.locallyRingedSpaceObj
        (AdicCompletion.idealOfDefinition (annulusLocIdealY R I q)) where
  hom := FormalSpectrum.locallyRingedSpaceMap _ _ (annulusOverlapInversion R I q hI).symm.toRingHom
    (annulusOverlapInversion_symm_isAdicHom R I q hI).le_comap
  inv := FormalSpectrum.locallyRingedSpaceMap _ _ (annulusOverlapInversion R I q hI).toRingHom
    (annulusOverlapInversion_isAdicHom R I q hI).le_comap
  hom_inv_id := by
    have hIK : AdicCompletion.idealOfDefinition (annulusLocIdeal R I q) ≤
        (AdicCompletion.idealOfDefinition (annulusLocIdeal R I q)).comap
          ((annulusOverlapInversion R I q hI).symm.toRingHom.comp
            (annulusOverlapInversion R I q hI).toRingHom) := by
      rw [annulusOverlapInversion_symm_comp_self]; exact (Ideal.comap_id _).ge
    rw [← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIK),
      FormalSpectrum.locallyRingedSpaceMap_congr (φ₂ := RingHom.id (annulusOverlap R I q))
        (hφ := annulusOverlapInversion_symm_comp_self R I q hI)]
    exact FormalSpectrum.locallyRingedSpaceMap_id _
  inv_hom_id := by
    have hIK : AdicCompletion.idealOfDefinition (annulusLocIdealY R I q) ≤
        (AdicCompletion.idealOfDefinition (annulusLocIdealY R I q)).comap
          ((annulusOverlapInversion R I q hI).toRingHom.comp
            (annulusOverlapInversion R I q hI).symm.toRingHom) := by
      rw [annulusOverlapInversion_comp_symm]; exact (Ideal.comap_id _).ge
    rw [← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIK),
      FormalSpectrum.locallyRingedSpaceMap_congr (φ₂ := RingHom.id (annulusOverlapY R I q))
        (hφ := annulusOverlapInversion_comp_symm R I q hI)]
    exact FormalSpectrum.locallyRingedSpaceMap_id _

/-- **The geometric 𝔾m-inversion overlap transition on the annulus charts**
`Spf A{1/x} ≅ Spf A{1/y}`:
conjugate `annulusOverlapInversionSpf` with the two chart domain identifications
`annulusChartDomainSpfX` / `annulusChartDomainSpfY`. This is the corrected `t`-transition datum, on
the concrete overlap chart domains, that the rewired `tateCurveGlueData'` (issue 435c) consumes in
place of the non-separated `annulusChartTransitionSpf`. -/
def annulusChartTransitionInvSpf :
    FormalSpectrum.locallyRingedSpaceObj
        (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q)) ≅
      FormalSpectrum.locallyRingedSpaceObj
        (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q)) :=
  annulusChartDomainSpfX R I q ≪≫ annulusOverlapInversionSpf R I q hI ≪≫
    (annulusChartDomainSpfY R I q).symm

/-- **The `R`-linearity crux of the inversion transition** (ring level): the inverse inversion
transition `A[y⁻¹]^∧ →+* A[x⁻¹]^∧` composed with the structural map `R → A[y⁻¹]^∧` equals the
structural map `R → A[x⁻¹]^∧`; i.e. the corrected transition is a morphism of `R`-algebras. This is
the `…Inv` analogue of `annulusOverlapTransitionInv_comp_algebraMap` and the ring-level reason the
per-patch structural morphisms of the corrected model agree on the overlaps. -/
theorem annulusOverlapInversion_symm_comp_algebraMap :
    (annulusOverlapInversion R I q hI).symm.toRingHom.comp
        (algebraMap R (annulusOverlapY R I q)) =
      algebraMap R (annulusOverlap R I q) := by
  refine RingHom.ext fun r => ?_
  show (annulusOverlapInversion R I q hI).symm (algebraMap R (annulusOverlapY R I q) r) = _
  rw [← annulusOverlapInversion_algebraMap R I q hI r, RingEquiv.symm_apply_apply]

/-- **Geometric acceptance witness: the corrected transition glues by genuine 𝔾m-inversion, not the
swap.** The ring homomorphism underlying the forward geometric transition
`annulusOverlapInversionSpf.hom` is precisely `(annulusOverlapInversion R I q hI).symm.toRingHom`
(the map that `FormalSpectrum.locallyRingedSpaceMap` sends to that hom); read through the crux
identification `overlapEquiv`, it carries the `y`-chart unit `overlapY` to `X (-1)`, i.e. `Y ↦ X⁻¹`.
The coordinate *swap* `annulusChartTransitionSpf` would instead give `X 1`, so this lemma certifies
that `annulusChartTransitionInvSpf` realises the Néron 2-gon gluing `x₀·y₁ = 1` and hence that the
rerouted `tateCurveModel` (issue 435) is separated. It is the geometric-level repackaging of the
ring-level witness `overlapEquiv_annulusOverlapInversion_symm_overlapY` (issue 436). -/
theorem overlapEquiv_annulusOverlapInversionSpf_ringHom_overlapY :
    overlapEquiv R I q hI
        ((annulusOverlapInversion R I q hI).symm.toRingHom
          (algebraMap (annulusAlgebra R I q) (annulusOverlapY R I q) (overlapY R I q))) =
      RestrictedLaurentSeries.X R I (-1) :=
  overlapEquiv_annulusOverlapInversion_symm_overlapY R I q hI

end
