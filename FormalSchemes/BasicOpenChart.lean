import FormalSchemes.SpfMap
import FormalSchemes.Sections
import FormalSchemes.Completion
import FormalSchemes.LocalizationQuotient
import Mathlib.RingTheory.Spectrum.Prime.Topology

set_option linter.style.header false

/-!
# The affine basic-open chart of a formal spectrum

Let `R` be an adic ring with ideal of definition `I` and let `f : R`. The basic open
`D(f) ⊆ Spf R` is realised, as an affine formal scheme, by the formal spectrum of the completed
localization `R{1/f} := AdicCompletion (I·R_f) R_f` (`R_f = Localization.Away f`): the sections of
`O_{Spf R}` over `D(f)` are exactly this completed localization (`sectionsBasicOpenEquiv`,
`FormalSchemes/Sections.lean`). This is the formal-geometry analogue of `Spec R_f ≅ D(f) ⊆ Spec R`
(`AlgebraicGeometry.basicOpenIsoSpecAway`) and is the chart out of which the Tate chain (issue 68)
is glued.

This file establishes the **underlying open embedding** of that chart: the continuous map
`Spf R{1/f} → Spf R` induced (via `FormalSpectrum.map`) by the structural ring map
`R → R_f → R{1/f}` is an open topological embedding whose range is exactly `D(f)`. This is the
`base_open` half of the eventual `LocallyRingedSpace.IsOpenImmersion` statement (the remaining
`c_iso`/stalk-iso half, feeding `SheafedSpace.IsOpenImmersion.of_stalk_iso`, is left as follow-up;
see the module note below).

## Main definitions and results

* `FormalSpectrum.awayCompletion I f`, `FormalSpectrum.awayCompletionIdeal I f`: the completed
  localization `R{1/f}` and its ideal of definition.
* `FormalSpectrum.basicOpenChartBase I f`: the underlying map `Spf R{1/f} → Spf R` of the chart.
* `FormalSpectrum.range_basicOpenChartBase`: its range is `basicOpen I f = D(f)`.
* `FormalSpectrum.isOpenEmbedding_basicOpenChartBase`: it is an open topological embedding.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1 (10.1.4).
* [The Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7).
-/

noncomputable section

open TopologicalSpace Topology

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R) (f : R)

/-- The completed localization `R{1/f}`: the `I`-adic completion of the localization `R_f`. Its
sections identification with `Γ(D(f), O_{Spf R})` is `FormalSpectrum.sectionsBasicOpenEquiv`. -/
abbrev awayCompletion : Type u :=
  AdicCompletion (I.map (algebraMap R (Localization.Away f))) (Localization.Away f)

/-- The ideal of definition of `R{1/f}` (the extension of `I·R_f` along the completion map). -/
abbrev awayCompletionIdeal : Ideal (awayCompletion I f) :=
  AdicCompletion.idealOfDefinition (I.map (algebraMap R (Localization.Away f)))

/-- The structural ring map `R → R{1/f}`, factoring through `R_f = Localization.Away f`. -/
def awayCompletionHom : R →+* awayCompletion I f :=
  (algebraMap (Localization.Away f) (awayCompletion I f)).comp
    (algebraMap R (Localization.Away f))

theorem map_awayCompletionHom :
    I.map (awayCompletionHom I f) = awayCompletionIdeal I f := by
  rw [awayCompletionHom, ← Ideal.map_map]

theorem le_comap_awayCompletionHom :
    I ≤ (awayCompletionIdeal I f).comap (awayCompletionHom I f) :=
  Ideal.map_le_iff_le_comap.mp (map_awayCompletionHom I f).le

/-- The underlying continuous map `Spf R{1/f} → Spf R` of the affine basic-open chart. -/
def basicOpenChartBase : FormalSpectrum (awayCompletionIdeal I f) → FormalSpectrum I :=
  map I (awayCompletionIdeal I f) (awayCompletionHom I f) (le_comap_awayCompletionHom I f)

/-- The residue ring `R{1/f} ⧸ (I·R{1/f})` of the completed localization is the localization of
`R ⧸ I` away from the residue of `f`: completion does not change the level-`0` thickening, and
localization commutes with quotient. -/
def awayCompletionResidueEquiv (hI : I.FG) :
    (awayCompletion I f) ⧸ (awayCompletionIdeal I f) ≃+*
      Localization.Away (Ideal.Quotient.mk I f) :=
  (AdicCompletion.quotientEquiv (I.map (algebraMap R (Localization.Away f))) (hI.map _)).trans
    (Localization.awayQuotientEquiv f I).symm

/-- The level-`1` residue identification `AdicCompletion.quotientEquiv` sends the residue of the
completion image `algebraMap B (AdicCompletion K B) b` to the residue `Ideal.Quotient.mk K b`:
completion does not move elements coming from `B` at the level-`1` thickening. -/
private theorem quotientEquiv_mk_algebraMap {B : Type u} [CommRing B] (K : Ideal B) (hK : K.FG)
    (b : B) :
    AdicCompletion.quotientEquiv K hK
        (Ideal.Quotient.mk (AdicCompletion.idealOfDefinition K)
          (algebraMap B (AdicCompletion K B) b)) =
      Ideal.Quotient.mk K b := by
  rw [AdicCompletion.quotientEquiv]
  simp only [RingEquiv.coe_trans, Function.comp_apply]
  rw [Ideal.quotEquivOfEq_mk, AdicCompletion.quotientEquivPow_mk, AlgHom.commutes,
    Ideal.Quotient.algebraMap_eq, Ideal.quotEquivOfEq_mk]

/-- The chart's residue map `R ⧸ I → R{1/f} ⧸ (I·R{1/f})`, transported along
`awayCompletionResidueEquiv`, is the localization map `R ⧸ I → (R ⧸ I)_{f̄}`. This is the crux
identification: it exhibits the base map of the chart as the comap of a localization-away map. -/
theorem awayCompletionResidueEquiv_comp_residueRingHom (hI : I.FG) :
    (awayCompletionResidueEquiv I f hI).toRingHom.comp
        (residueRingHom I (awayCompletionIdeal I f) (awayCompletionHom I f)
          (le_comap_awayCompletionHom I f)) =
      algebraMap (R ⧸ I) (Localization.Away (Ideal.Quotient.mk I f)) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  simp only [residueRingHom]
  rw [Ideal.quotientMap_mk, awayCompletionResidueEquiv, RingEquiv.trans_apply]
  simp only [awayCompletionHom, RingHom.comp_apply]
  rw [quotientEquiv_mk_algebraMap, RingEquiv.symm_apply_eq,
    Localization.awayQuotientEquiv_algebraMap]
  rfl

/-- The ring homomorphism underlying the base map of the chart factors, after transport along
`awayCompletionResidueEquiv`, through the localization-away map: `residue = σ.symm ∘ (localization
map)`. This is the ring-theoretic content behind both the range and open-embedding statements. -/
private theorem quotientMap_eq_comp (hI : I.FG) :
    Ideal.quotientMap (awayCompletionIdeal I f) (awayCompletionHom I f)
        (le_comap_awayCompletionHom I f) =
      (awayCompletionResidueEquiv I f hI).symm.toRingHom.comp
        (algebraMap (R ⧸ I) (Localization.Away (Ideal.Quotient.mk I f))) := by
  have key := awayCompletionResidueEquiv_comp_residueRingHom I f hI
  simp only [residueRingHom] at key
  rw [← key, ← RingHom.comp_assoc, RingEquiv.symm_toRingHom_comp_toRingHom, RingHom.id_comp]

theorem range_basicOpenChartBase (hI : I.FG) :
    Set.range (basicOpenChartBase I f) = (basicOpen I f : Set (FormalSpectrum I)) := by
  have hsurj : Function.Surjective (PrimeSpectrum.comap
      (awayCompletionResidueEquiv I f hI).symm.toRingHom) :=
    (PrimeSpectrum.homeomorphOfRingEquiv (awayCompletionResidueEquiv I f hI)).surjective
  have hrange : Set.range (PrimeSpectrum.comap (Ideal.quotientMap (awayCompletionIdeal I f)
        (awayCompletionHom I f) (le_comap_awayCompletionHom I f))) =
      (PrimeSpectrum.basicOpen (Ideal.Quotient.mk I f) : Set (PrimeSpectrum (R ⧸ I))) := by
    rw [quotientMap_eq_comp I f hI, PrimeSpectrum.comap_comp, hsurj.range_comp]
    exact PrimeSpectrum.localization_away_comap_range
      (Localization.Away (Ideal.Quotient.mk I f)) (Ideal.Quotient.mk I f)
  exact hrange

theorem isOpenEmbedding_basicOpenChartBase (hI : I.FG) :
    IsOpenEmbedding (basicOpenChartBase I f) := by
  have hopen : IsOpenEmbedding (PrimeSpectrum.comap (Ideal.quotientMap (awayCompletionIdeal I f)
      (awayCompletionHom I f) (le_comap_awayCompletionHom I f))) := by
    rw [quotientMap_eq_comp I f hI, PrimeSpectrum.comap_comp]
    exact (PrimeSpectrum.localization_away_isOpenEmbedding _ (Ideal.Quotient.mk I f)).comp
      (PrimeSpectrum.homeomorphOfRingEquiv (awayCompletionResidueEquiv I f hI)).isOpenEmbedding
  exact hopen

end FormalSpectrum
