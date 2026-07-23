import FormalSchemes.TateTransition
import FormalSchemes.AdicMorphism
import FormalSchemes.SpfFunctorial

set_option linter.style.header false

/-!
# The geometric overlap transition isomorphism of the Tate annulus chain

Fix an adic ring `R` with ideal of definition `I` (finitely generated) and a Tate parameter
`q : R`, and let `A = R{x, y} / (x·y − q)` be the coordinate ring of the formal Tate annulus. The
overlap of two consecutive annulus patches `U_n = Spf A_n` and `U_{n+1} = Spf A_{n+1}` is
identified, through the coordinate swap `x ↔ y`, with the completed-localization charts

```
A[x⁻¹]^∧  ≅  A[y⁻¹]^∧ .
```

The **ring-level** transition `annulusOverlapTransition : A[x⁻¹]^∧ ≃+* A[y⁻¹]^∧` (issue 133/134,
`FormalSchemes.TateTransition`, PR #37) is already available. This file promotes it to the
**geometric** transition `t_{n,n+1}` that the `FormalScheme.GlueData` assembly of the Tate chain
(issue 134b / 208) consumes: an isomorphism of the affine formal open subschemes

```
Δ_x : Spf(A[x⁻¹]^∧)  ≅  Spf(A[y⁻¹]^∧) .
```

## Main results

* `annulusOverlapTransition_isAdicHom` / `annulusOverlapTransition_symm_isAdicHom`: the ring
  transition and its inverse are adic homomorphisms (they carry the ideal of definition of one
  overlap chart onto that of the other), built from the already-established localization-ideal
  transport `annulusLocTransition_map_ideal` and the completion functor
  `AdicCompletion.mapCompletion`.
* `annulusOverlapTransitionSpf`: the induced isomorphism of locally ringed spaces
  `Spf(A[x⁻¹]^∧) ≅ Spf(A[y⁻¹]^∧)`, obtained as `Spf` of the ring equivalence via the merged
  `Spf`-functor laws (`locallyRingedSpaceMap_comp`/`_id`/`_congr`, issue 60).

**Scope.** This delivers the geometric transition iso between the completed-localization overlap
charts. Its bridge to the chart *domains* `Spf(A{1/x})` used by `annulusOverlapChart`
(`FormalSchemes.TateOverlapImmersion`) — via `awayCompletionEquivAnnulusOverlap` — and its wiring
into the `t`, `t'`, `t_fac`, `cocycle` fields of the `ℤ`-indexed `FormalScheme.GlueData` are the
remaining work of issue 134b (208).

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4.
-/

noncomputable section

open Ideal AlgebraicGeometry CategoryTheory FormalSpectrum

universe u

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- The forward overlap transition `A[x⁻¹]^∧ →+* A[y⁻¹]^∧` is an **adic homomorphism**: it carries
the ideal of definition of `A[x⁻¹]^∧` onto that of `A[y⁻¹]^∧`. Both inequalities come from
`AdicCompletion.idealOfDefinition_map_le` applied to the two directions of the localization-ideal
transport `annulusLocTransition_map_ideal` / `annulusLocTransition_symm_map_ideal`. -/
theorem annulusOverlapTransition_isAdicHom (hI : I.FG) :
    IsAdicHom (AdicCompletion.idealOfDefinition (annulusLocIdeal R I q))
      (AdicCompletion.idealOfDefinition (annulusLocIdealY R I q))
      (annulusOverlapTransitionHom R I q hI) := by
  have hfwd : (AdicCompletion.idealOfDefinition (annulusLocIdeal R I q)).map
      (annulusOverlapTransitionHom R I q hI) ≤
        AdicCompletion.idealOfDefinition (annulusLocIdealY R I q) :=
    AdicCompletion.idealOfDefinition_map_le
      (annulusLocTransition R I q hI : annulusLoc R I q →+* annulusLocY R I q)
      (le_of_eq (annulusLocTransition_map_ideal R I q hI)) (hI.map _)
  have hinv : (AdicCompletion.idealOfDefinition (annulusLocIdealY R I q)).map
      (annulusOverlapTransitionInv R I q hI) ≤
        AdicCompletion.idealOfDefinition (annulusLocIdeal R I q) :=
    AdicCompletion.idealOfDefinition_map_le
      ((annulusLocTransition R I q hI).symm : annulusLocY R I q →+* annulusLoc R I q)
      (le_of_eq (annulusLocTransition_symm_map_ideal R I q hI)) (hI.map _)
  refine le_antisymm hfwd ?_
  calc AdicCompletion.idealOfDefinition (annulusLocIdealY R I q)
      = ((AdicCompletion.idealOfDefinition (annulusLocIdealY R I q)).map
          (annulusOverlapTransitionInv R I q hI)).map (annulusOverlapTransitionHom R I q hI) := by
        rw [Ideal.map_map, annulusOverlapTransition_right, Ideal.map_id]
    _ ≤ (AdicCompletion.idealOfDefinition (annulusLocIdeal R I q)).map
          (annulusOverlapTransitionHom R I q hI) := Ideal.map_mono hinv

/-- The inverse overlap transition `A[y⁻¹]^∧ →+* A[x⁻¹]^∧` is an **adic homomorphism**. -/
theorem annulusOverlapTransition_symm_isAdicHom (hI : I.FG) :
    IsAdicHom (AdicCompletion.idealOfDefinition (annulusLocIdealY R I q))
      (AdicCompletion.idealOfDefinition (annulusLocIdeal R I q))
      (annulusOverlapTransitionInv R I q hI) := by
  have hinv : (AdicCompletion.idealOfDefinition (annulusLocIdealY R I q)).map
      (annulusOverlapTransitionInv R I q hI) ≤
        AdicCompletion.idealOfDefinition (annulusLocIdeal R I q) :=
    AdicCompletion.idealOfDefinition_map_le
      ((annulusLocTransition R I q hI).symm : annulusLocY R I q →+* annulusLoc R I q)
      (le_of_eq (annulusLocTransition_symm_map_ideal R I q hI)) (hI.map _)
  have hfwd : (AdicCompletion.idealOfDefinition (annulusLocIdeal R I q)).map
      (annulusOverlapTransitionHom R I q hI) ≤
        AdicCompletion.idealOfDefinition (annulusLocIdealY R I q) :=
    AdicCompletion.idealOfDefinition_map_le
      (annulusLocTransition R I q hI : annulusLoc R I q →+* annulusLocY R I q)
      (le_of_eq (annulusLocTransition_map_ideal R I q hI)) (hI.map _)
  refine le_antisymm hinv ?_
  calc AdicCompletion.idealOfDefinition (annulusLocIdeal R I q)
      = ((AdicCompletion.idealOfDefinition (annulusLocIdeal R I q)).map
          (annulusOverlapTransitionHom R I q hI)).map (annulusOverlapTransitionInv R I q hI) := by
        rw [Ideal.map_map, annulusOverlapTransition_left, Ideal.map_id]
    _ ≤ (AdicCompletion.idealOfDefinition (annulusLocIdealY R I q)).map
          (annulusOverlapTransitionInv R I q hI) := Ideal.map_mono hfwd

/-- **The geometric overlap transition** `Spf(A[x⁻¹]^∧) ≅ Spf(A[y⁻¹]^∧)` of the Tate chain: `Spf` of
the ring isomorphism `annulusOverlapTransition`. This is the transition `t_{n,n+1}` between the two
overlap charts of consecutive annulus patches, at the level of locally ringed spaces. The two
`Spf`-morphisms are mutually inverse because `annulusOverlapTransition` is a ring isomorphism, via
the merged `Spf`-functor laws. -/
def annulusOverlapTransitionSpf (hI : I.FG) :
    FormalSpectrum.locallyRingedSpaceObj
        (AdicCompletion.idealOfDefinition (annulusLocIdeal R I q)) ≅
      FormalSpectrum.locallyRingedSpaceObj
        (AdicCompletion.idealOfDefinition (annulusLocIdealY R I q)) where
  hom := FormalSpectrum.locallyRingedSpaceMap _ _ (annulusOverlapTransitionInv R I q hI)
    (annulusOverlapTransition_symm_isAdicHom R I q hI).le_comap
  inv := FormalSpectrum.locallyRingedSpaceMap _ _ (annulusOverlapTransitionHom R I q hI)
    (annulusOverlapTransition_isAdicHom R I q hI).le_comap
  hom_inv_id := by
    have hIK : AdicCompletion.idealOfDefinition (annulusLocIdeal R I q) ≤
        (AdicCompletion.idealOfDefinition (annulusLocIdeal R I q)).comap
          ((annulusOverlapTransitionInv R I q hI).comp (annulusOverlapTransitionHom R I q hI)) := by
      rw [annulusOverlapTransition_left]; exact (Ideal.comap_id _).ge
    rw [← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIK),
      FormalSpectrum.locallyRingedSpaceMap_congr (φ₂ := RingHom.id (annulusOverlap R I q))
        (hφ := annulusOverlapTransition_left R I q hI)]
    exact FormalSpectrum.locallyRingedSpaceMap_id _
  inv_hom_id := by
    have hIK : AdicCompletion.idealOfDefinition (annulusLocIdealY R I q) ≤
        (AdicCompletion.idealOfDefinition (annulusLocIdealY R I q)).comap
          ((annulusOverlapTransitionHom R I q hI).comp (annulusOverlapTransitionInv R I q hI)) := by
      rw [annulusOverlapTransition_right]; exact (Ideal.comap_id _).ge
    rw [← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIK),
      FormalSpectrum.locallyRingedSpaceMap_congr (φ₂ := RingHom.id (annulusOverlapY R I q))
        (hφ := annulusOverlapTransition_right R I q hI)]
    exact FormalSpectrum.locallyRingedSpaceMap_id _
