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
`base_open` half of the `LocallyRingedSpace.IsOpenImmersion` statement; the `c_iso`/stalk-iso half,
feeding `SheafedSpace.IsOpenImmersion.of_stalk_iso`, is proved in
`FormalSchemes.BasicOpenImmersionLRS`, where the two are assembled into
`FormalSpectrum.isOpenImmersion_basicOpenChart`.

## Main definitions and results

* `FormalSpectrum.awayCompletion I f`, `FormalSpectrum.awayCompletionIdeal I f`: the completed
  localization `R{1/f}` and its ideal of definition.
* `FormalSpectrum.basicOpenChartBase I f`: the underlying map `Spf R{1/f} → Spf R` of the chart.
* `FormalSpectrum.range_basicOpenChartBase`: its range is `basicOpen I f = D(f)`.
* `FormalSpectrum.isOpenEmbedding_basicOpenChartBase`: it is an open topological embedding.
* `FormalSpectrum.awayCompletionHom_comp_algebraMap`: the structural map `A → A{1/g}^` of a
  completed localization is a map of `R`-algebras.
* `FormalSpectrum.isAdicRing_awayCompletionIdeal`: `R{1/f}` is a complete adic ring whenever `I`
  is finitely generated.
* `FormalSpectrum.map_algebraMap_awayCompletion`, its `rfl` case
  `FormalSpectrum.map_algebraMap_awayCompletion_eq`, and
  `FormalSpectrum.awayCompletionIdeal_eq_map_algebraMap`: the ideal-convention bookkeeping —
  `awayCompletionIdeal L g` is the extension of the base ideal `I` along `R → A{1/g}^`, in the
  spellings the rest of the tree meets it in. These live here, rather than in the modules that
  need them, because their ingredients are all defined in this file and this module is in the
  import closure of every consumer; their own docstrings record how many times each had been
  written out elsewhere before issues 881 and 895 moved them.

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

/-- **`R{1/f}` is a complete adic ring** for `I` finitely generated, with `I·R{1/f}` as ideal of
definition — so `Spf R{1/f}` is an affine formal scheme and the affine-target colimit property
applies to it.

This is `AdicCompletion.isAdicRing_map` at the localization, and it is *not* an instance: it needs
`I.FG`, which is not synthesizable, so the modules that build on the chart carry
`[IsAdicRing (awayCompletionIdeal I f)]` as a hypothesis (`FormalSchemes/AdicOnSections.lean`) and
their consumers discharge it with this lemma. It lives here, next to `awayCompletionIdeal`
itself, for the reason recorded above for the ideal-convention lemmas: every consumer already
imports this module. Issue 1062 first named it in `FormalSchemes/ThickeningChartSpfHom.lean`,
which is too high in the hierarchy for the files that had been writing the one-liner out inline;
issue 1065 moved it here and routed those eighteen sites through it. -/
theorem isAdicRing_awayCompletionIdeal (hI : I.FG) : IsAdicRing (awayCompletionIdeal I f) :=
  AdicCompletion.isAdicRing_map _ (hI.map _)

/-- **The structural map of a completed localization is a map of algebras over any base.** If `A`
is an `R`-algebra, then `A → A{1/g}^` precomposed with `R → A` is `R → A{1/g}^`.

This is `IsScalarTower.algebraMap_eq R A (awayCompletion L g)` — the tower instance is already
available and `awayCompletionHom L g` is the `A`-algebra structure map of `awayCompletion L g` on
the nose. The lemma exists because callers meet the left-hand side spelled `awayCompletionHom`,
which no Mathlib rewrite fires on; it is the bridge between the two spellings, not new content.

Stated at an arbitrary ideal `L` of `A`, and here rather than in a downstream module, because it is
the general form that every layer wants: it was previously declared **four** times — the general
version in `FormalSchemes.RelativeTopFiniteTypeBasis`, out of reach of the gluing layer without
importing the whole topologically-finite-type sub-tower, plus two instances of it re-proved in
`FormalSchemes.CompletedTensorAwayInterchange` and
`FormalSchemes.CompletedTensorAwayInterchangePrLeft`, and a pointwise fourth in the former under an
unrelated name. Issue 881 consolidated them here, beside `awayCompletionHom` itself.

The binder `R` deliberately shadows this file's section variable `R`, which there is the *chart*
ring; `A`, `L` and `g` are fresh names. A declaration's own binders shadow section variables, and
the file's `I` and `f` are then not referenced at all, so neither is auto-included and the
signature is exactly the form its consumer modules pass. -/
theorem awayCompletionHom_comp_algebraMap {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {L : Ideal A} (g : A) :
    (awayCompletionHom L g).comp (algebraMap R A) = algebraMap R (awayCompletion L g) :=
  (IsScalarTower.algebraMap_eq R A (awayCompletion L g)).symm

/-- **The ideal of definition of `A{1/g}^` is the extension of `L` along `A → A{1/g}^`**, with the
structural map spelled as an `algebraMap` rather than as `awayCompletionHom`.

This is `map_awayCompletionHom` — the two are the *same term*, since `awayCompletionHom L g` is
`algebraMap A (awayCompletion L g)` on the nose (see `awayCompletionHom_comp_algebraMap`). It
earns a name for the same reason that one does: `rw` is syntactic, so a goal spelled with
`algebraMap` is not reachable from `map_awayCompletionHom`. It is the bridge between the two
spellings, not new content. -/
theorem awayCompletionIdeal_eq_map_algebraMap {A : Type u} [CommRing A] {L : Ideal A} (g : A) :
    L.map (algebraMap A (awayCompletion L g)) = awayCompletionIdeal L g :=
  map_awayCompletionHom L g

/-- **The ideal of definition of `A{1/g}^`, written as the extension of the base ideal.** If `A` is
an `R`-algebra whose ideal `L` is the extension `I·A`, then `I·(A{1/g}^)` is `awayCompletionIdeal L
g`.

The hypothesis `h` is what makes this the general form of the whole family: the three ideals the
tree cares about — `I.map (algebraMap R A)` itself, `CompletedTensorProduct.idealOfDefinition`, and
whatever a chart datum supplies — all satisfy it, but only the first satisfies it by `rfl`.
`map_algebraMap_awayCompletion_eq` below is that `rfl` case, which is what almost every call site
wants.

Proof: `awayCompletionHom_comp_algebraMap` turns `algebraMap R (A{1/g}^)` into
`awayCompletionHom L g ∘ algebraMap R A`, `Ideal.map_map` splits the extension in two, `h`
identifies the inner half with `L`, and `map_awayCompletionHom` closes it. Every ingredient is in
this file, which is why the statement belongs here.

This fact was previously declared **seven** times across the tree, in five modules, none of which
could reach the general version: it lived in `FormalSchemes.AwayTopFiniteType`, a topologically-
finite-type module in the closure of none of its consumers — the same layering fault, and the same
sub-tower, that issue 881 extracted `awayCompletionHom_comp_algebraMap` from. Issue 895
consolidated them here. -/
theorem map_algebraMap_awayCompletion {R : Type u} [CommRing R] {I : Ideal R} {A : Type u}
    [CommRing A] [Algebra R A] {L : Ideal A} (g : A) (h : I.map (algebraMap R A) = L) :
    I.map (algebraMap R (awayCompletion L g)) = awayCompletionIdeal L g := by
  rw [← awayCompletionHom_comp_algebraMap (L := L) g, ← Ideal.map_map, h, map_awayCompletionHom]

/-- **The ideal-convention bridge.** The ideal of definition of the chart algebra `A{1/f}`, spelled
as an affine-charted datum spells it (`I.map (algebraMap R (A i))`), is the `awayCompletionIdeal`
of the chart. Both are the image of `I` under `R → A → A_f → A{1/f}`.

The `rfl` case of `map_algebraMap_awayCompletion`, and the form every call site outside
`FormalSchemes.CompletedTensorAwayInterchange` uses. -/
theorem map_algebraMap_awayCompletion_eq {R : Type u} [CommRing R] (I : Ideal R) {A : Type u}
    [CommRing A] [Algebra R A] (f : A) :
    I.map (algebraMap R (awayCompletion (I.map (algebraMap R A)) f)) =
      awayCompletionIdeal (I.map (algebraMap R A)) f :=
  map_algebraMap_awayCompletion f rfl

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
