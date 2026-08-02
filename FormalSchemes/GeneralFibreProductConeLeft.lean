import FormalSchemes.GeneralFibreProductProjectionLeft
import FormalSchemes.GeneralFibreProductExposeXStructMap

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The cone identity of the general fibre product `X ×_{Spf R} Spf B`

`FormalSchemes.GeneralFibreProductProjectionLeft` builds the first projection
`pr₁ : X ×_{Spf R} Spf B ⟶ X` (into the glued target exposed by
`FormalSchemes.GeneralFibreProductExposeX`), `FormalSchemes.GeneralFibreProductProjection` builds
the second projection `pr₂ : X ×_{Spf R} Spf B ⟶ Spf B`, and
`FormalSchemes.GeneralFibreProductExposeXStructMap` builds the structural morphism
`f = xStructMap : X ⟶ Spf R` of the exposed `X`.

This file closes brick 233b-cont (issue 316, Step 3): the **cone identity**

`pr₁ ≫ f = pr₂ ≫ g`   over   `Spf R`,

where `f = xStructMap : X ⟶ Spf R` and `g = Spf(algebraMap R B) : Spf B ⟶ Spf R` is the base map
of the affine factor. It is proved by `FormalScheme.GlueData.hom_ext`: restricting both sides
along each glue inclusion `ι i` of the fibre product reduces — via `ι_pr₁`/`ι_xStructMap` on the
left and `ι_pr₂` on the right — to the per-chart identity

`pr₁Chart i ≫ xStructMapChart i = pr₂Chart(A_i) ≫ g`

(`AffineChartedFibreDatumX.cone_identity_chart`). Each side fuses through
`FormalSpectrum.locallyRingedSpaceMap_comp` into a single `locallyRingedSpaceMap` out of
`Spf(A_i ⊗̂_R B)`, and the underlying ring maps agree because both
`inl : A_i → A_i ⊗̂_R B` and `inr : B → A_i ⊗̂_R B` are `R`-algebra maps: their composites with
the base structure maps both equal `algebraMap R (A_i ⊗̂_R B)` (`AlgHom.comp_algebraMap`). This is
the affine cone identity `CompletedTensorProduct.fibre_cone_comm`, reproved in the instance-light
world of raw `locallyRingedSpaceMap`s (the datum carries no adic-ring structure on the general
charts `A_i`, so `fibre_cone_comm` — which needs those instances — is not invoked directly).

## Main definitions

* `AffineChartedFibreDatumX.cone_identity_chart`: the per-chart cone identity.
* `AffineChartedFibreDatumX.cone_identity`: the glued cone identity `pr₁ ≫ f = pr₂ ≫ g`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum
open CompletedTensorProduct

universe u

namespace AlgebraicGeometry

/-- Continuity of a composite ring homomorphism, in `comap` form. -/
private theorem le_comap_comp' {S T U : Type u} [CommRing S] [CommRing T] [CommRing U]
    {J : Ideal S} {K : Ideal T} {L : Ideal U} (φ : S →+* T) (ψ : T →+* U)
    (hJK : J ≤ K.comap φ) (hKL : K ≤ L.comap ψ) : J ≤ L.comap (ψ.comp φ) :=
  fun _ hx => hKL (hJK hx)

namespace AffineChartedFibreDatumX

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable {B : Type u} [CommRing B] [Algebra R B]
variable (D : AffineChartedFibreDatumX R I hI B)

/-- **The per-chart cone identity.** The first projection of chart `i` followed by the per-chart
structural morphism of `X` equals the second projection of chart `i` followed by the base map
`g = Spf(algebraMap R B)`. Both sides collapse to a single `locallyRingedSpaceMap` out of
`Spf(A_i ⊗̂_R B)`, and the underlying ring maps agree because `inl.comp (algebraMap R A_i)` and
`inr.comp (algebraMap R B)` both equal `algebraMap R (A_i ⊗̂_R B)` (`AlgHom.comp_algebraMap`). -/
theorem cone_identity_chart (i : D.J) :
    letI := D.commRing
    letI := D.algebra
    D.pr₁Chart i ≫ D.xStructMapChart i =
      pr₂Chart R I B (D.A i) ≫
        FormalSpectrum.locallyRingedSpaceMap I (I.map (algebraMap R B)) (algebraMap R B)
          Ideal.le_comap_map := by
  letI := D.commRing
  letI := D.algebra
  rw [pr₁Chart, xStructMapChart, pr₂Chart,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (I := I) (J := I.map (algebraMap R (D.A i)))
      (K := CompletedTensorProduct.idealOfDefinition R I (D.A i) B)
      (φ := algebraMap R (D.A i))
      (ψ := (CompletedTensorProduct.inl R I (D.A i) B).toRingHom)
      (hIJ := Ideal.le_comap_map)
      (hJK := CompletedTensorProduct.inl_isAdicHom.le_comap)
      (hIK := le_comap_comp' (algebraMap R (D.A i))
        (CompletedTensorProduct.inl R I (D.A i) B).toRingHom
        Ideal.le_comap_map CompletedTensorProduct.inl_isAdicHom.le_comap),
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (I := I) (J := I.map (algebraMap R B))
      (K := CompletedTensorProduct.idealOfDefinition R I (D.A i) B)
      (φ := algebraMap R B)
      (ψ := (CompletedTensorProduct.inr R I (D.A i) B).toRingHom)
      (hIJ := Ideal.le_comap_map)
      (hJK := CompletedTensorProduct.inr_isAdicHom.le_comap)
      (hIK := le_comap_comp' (algebraMap R B)
        (CompletedTensorProduct.inr R I (D.A i) B).toRingHom
        Ideal.le_comap_map CompletedTensorProduct.inr_isAdicHom.le_comap)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _
    ((AlgHom.comp_algebraMap (CompletedTensorProduct.inl R I (D.A i) B)).trans
      (AlgHom.comp_algebraMap (CompletedTensorProduct.inr R I (D.A i) B)).symm)

/-- **The cone identity of the general fibre product** `pr₁ ≫ f = pr₂ ≫ g` over `Spf R`, with
`f = xStructMap : X ⟶ Spf R` the structural morphism of the exposed `X` and
`g = Spf(algebraMap R B) : Spf B ⟶ Spf R` is the base map of the affine factor. Proved by
`FormalScheme.GlueData.hom_ext`: restricting along each glue inclusion `ι i` reduces to
`cone_identity_chart` via `ι_pr₁`/`ι_xStructMap` (left) and `ι_pr₂` (right). -/
theorem cone_identity :
    letI := D.commRing
    letI := D.algebra
    D.pr₁ ≫ D.xStructMap =
      D.pr₂ ≫ FormalSpectrum.locallyRingedSpaceMap I (I.map (algebraMap R B)) (algebraMap R B)
        Ideal.le_comap_map := by
  letI := D.commRing
  letI := D.algebra
  suffices h : ∀ (i : D.J), D.formalGlueData.ι i ≫ D.pr₁ ≫ D.xStructMap =
      D.formalGlueData.ι i ≫ D.pr₂ ≫
        FormalSpectrum.locallyRingedSpaceMap I (I.map (algebraMap R B)) (algebraMap R B)
          Ideal.le_comap_map by
    exact D.formalGlueData.hom_ext h
  -- The index type `J` of the glue data is semireducible (the `GlueData.ofGlueData'` object-defeq
  -- wall), so `rw`/`simp` cannot match against `ι i`; chase the equality in term mode instead,
  -- where the defeq is discharged at elaboration.
  intro i
  exact (Category.assoc _ _ _).symm.trans <|
    (((D.ι_pr₁ i) =≫ D.xStructMap).trans <|
      (Category.assoc _ _ _).trans <|
        (D.pr₁Chart i ≫= D.ι_xStructMap i).trans <|
          (D.cone_identity_chart i).trans <|
            ((D.ι_pr₂ i).symm =≫ _).trans (Category.assoc _ _ _))

end AffineChartedFibreDatumX

end AlgebraicGeometry
