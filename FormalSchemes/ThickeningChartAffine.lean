import FormalSchemes.ThickeningChartRestrict
import FormalSchemes.AwayCompletionResiduePow
import Mathlib.AlgebraicGeometry.AffineScheme

set_option linter.style.header false

/-!
# The chart of a thickening cut out by a basic open is affine, and it is the thickening of `R{1/r}`

Umbrella 59 runs *cover `X` by affines → pull the cover back to `|Spf R|` → refine by basic opens
`D(r)` → run the affine case on each chart → glue*. `ThickeningCommonBase.lean`,
`ThickeningCoverPullback.lean`, `ThickeningBasicOpenRefinement.lean` and
`ThickeningChartRestrict.lean` deliver the first three steps, and `AwayCompletionResiduePow.lean`
delivers the ring theory the fourth needs. What was missing between them is one geometric step:
the chart really is `Spec` of the ring the fourth step is about.

This file supplies it. For `r : R` and each level `n`, the open
`D(r̄) ⊆ Spec (R ⧸ Iⁿ⁺¹)` — which is where `D(r) ⊆ |Spf R|` goes under the homeomorphism
`thickeningTopIso`, by `thickeningOpen_basicOpen` — is an affine scheme, and it is `Spec` of the
`n`-th infinitesimal thickening of `R{1/r}`:

```
D(r̄) ⊆ Spec (R ⧸ Iⁿ⁺¹)   ≅   Spec ((R ⧸ Iⁿ⁺¹)_r̄)   ≅   Spec (R{1/r} ⧸ (I·R{1/r})ⁿ⁺¹)
```

the first isomorphism being Mathlib's `basicOpenIsoSpecAway` and the second `Spec` of
`awayCompletionResidueEquivPow` (issue 1043). **And it is an isomorphism of towers**: the charts
at level `n` and `n + 1` are joined by the restriction of `Spec.map (stepRingHom I n)`, the
thickenings of `R{1/r}` are joined by `Spec.map (stepRingHom (awayCompletionIdeal I r) n)`, and
`chartStep_comp_chartIsoSpec` says the square commutes. That levelwise-plus-compatible package is
exactly the hypothesis `thickeningRestrictionEquiv` (`IndSchemeColimitEquiv.lean`) needs in order
to run for the ring `R{1/r}` rather than for `R`.

## `Scheme` versus `LocallyRingedSpace`

`ThickeningChartRestrict.lean` deferred this question, saying it should be reopened at "the first
step that genuinely needs **affine** opens". This is that step, and the answer taken here is:
**this module knows what a `Scheme` is; nothing upstream of it does.** It imports
`Mathlib.AlgebraicGeometry.AffineScheme` — which the `Thickening*` subtree does not have, so that
`AlgebraicGeometry.Scheme`, `basicOpenIsoSpecAway` and `Scheme.Hom.resLE` are all unknown
identifiers there — and every module below keeps its `X : LocallyRingedSpace.{u}` target
unchanged.

That costs nothing, because the bridge is definitional, and both halves of it are theorems here
rather than assertions: `Scheme.forgetToLocallyRingedSpace_obj_Spec` and
`Scheme.forgetToLocallyRingedSpace_map_Spec_map` are `rfl`. So `chartIsoLRS` and
`chartStepLRS_comp_chartIsoLRS` restate the scheme-level results in the layer the `Thickening*`
modules are actually stated about, with no transport.

## Main definitions

* `FormalSpectrum.chartOpen I r n`: the chart `D(r̄)` of the `n`-th thickening, as an open of the
  *scheme* `Spec (R ⧸ Iⁿ⁺¹)`.
* `FormalSpectrum.chartStep I r n`: the tower's transition map, restricted to the charts.
* `FormalSpectrum.chartRingMap I r hI n`: the ring map `R ⧸ Iⁿ⁺¹ ⟶ R{1/r} ⧸ (I·R{1/r})ⁿ⁺¹` whose
  `Spec` is the chart inclusion read through the identification.
* `FormalSpectrum.chartIsoSpec I r hI n`: **the identification**, and `chartIsoLRS` its image in
  `LocallyRingedSpace`.

## Main results

* `FormalSpectrum.chartOpen_le_thickeningChart`: the variance alignment — a basic open of
  `|Spf R|` refining the pulled-back cover lands, at every level, inside
  `ThickeningChartRestrict.lean`'s chart.
* `FormalSpectrum.stepRingHom_comp_chartRingMap`: the identification is a map of towers at ring
  level.
* `FormalSpectrum.chartStep_comp_chartIsoSpec` and `FormalSpectrum.chartStepLRS_comp_chartIsoLRS`:
  **the payoff** — the charts of the tower of `Spf R` over `D(r)`, *with their transition maps*,
  are the tower of `Spf R{1/r}`.
* `FormalSpectrum.mem_chartOpen_comap`: `D(r) ⊆ |Spf R|` is the preimage of the chart under the
  map of spectra induced by `R ⧸ Iⁿ⁺¹ ↠ R ⧸ I`, whence `FormalSpectrum.chartOpen_ne_top` and
  `FormalSpectrum.chartOpen_ne_bot` — the chart is a proper nonempty open as soon as `D(r)` is.
* `FormalSpectrum.chartOpen_formalLine_ne_top`, `FormalSpectrum.chartOpen_formalLine_ne_bot`: the
  witness section discharges both at `ℤ⟦X⟧`, at every level of the tower.

## Implementation notes

`chartOpen` carries the `(Spec _).Opens` ascription rather than being a bare
`Opens (PrimeSpectrum (R ⧸ Iⁿ⁺¹))`. Without it `PrimeSpectrum.basicOpen …` elaborates as the
latter, which is not something the `Scheme.Opens.toScheme` coercion applies to, and the error
reports a *sort* mismatch — `Scheme` is a `Type (u + 1)` where an `Opens` of `Type u` was wanted —
which points at the `≅` rather than at the missing coercion. The two spellings are definitionally
equal; the ascription only tells elaboration which one to use.

`Scheme.Spec.mapIso (chartRingIso …).op` — not `Spec.mapIso`, which does not exist — is how a
ring isomorphism becomes an isomorphism of affine schemes. `.op` already reverses the direction,
so the `.symm` that reads naturally there is wrong and fails with a direction mismatch whose
error message names both spellings of the same object.

`hI : I.FG` is required wherever `awayCompletionResidueEquivPow` is, and `[IsAdicRing I]` does not
supply it. The purely topological results (`chartOpen_le_thickeningChart`, `chartOpen_ne_top`,
`chartOpen_ne_bot`) do not need it.

The two `rfl` bridges are stated in `AlgebraicGeometry.Scheme`, not in `FormalSpectrum`: their
statements are about Mathlib's `Scheme.forgetToLocallyRingedSpace` and mention nothing of this
project. See `ThickeningChartRestrict.lean`'s implementation notes for the rule.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.10).
* [The Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The forgetful functor to `LocallyRingedSpace` takes `Spec` to `Spec.locallyRingedSpaceObj` —
definitionally, which is half of what makes the scheme-level results usable one layer down. -/
theorem forgetToLocallyRingedSpace_obj_Spec (A : CommRingCat.{u}) :
    Scheme.forgetToLocallyRingedSpace.obj (Spec A) = Spec.locallyRingedSpaceObj A :=
  rfl

/-- …and it takes `Spec.map` to `Spec.locallyRingedSpaceMap`, which is the other half. -/
theorem forgetToLocallyRingedSpace_map_Spec_map {A B : CommRingCat.{u}} (φ : A ⟶ B) :
    Scheme.forgetToLocallyRingedSpace.map (Spec.map φ) = Spec.locallyRingedSpaceMap φ :=
  rfl

end AlgebraicGeometry.Scheme

namespace FormalSpectrum

section Chart

variable {R : Type u} [CommRing R] (I : Ideal R) (r : R)

/-- `(R ⧸ Iⁿ)_r̄`, the residue-side localization whose tower `AwayCompletionResiduePow.lean` is
about. -/
abbrev residueAway (n : ℕ) := Localization.Away (Ideal.Quotient.mk (I ^ n) r)

/-- The structure map `R ⧸ Iⁿ ⟶ (R ⧸ Iⁿ)_r̄`, in `CommRingCat`. -/
abbrev residueAwayAlgebraMap (n : ℕ) :
    CommRingCat.of (R ⧸ I ^ n) ⟶ CommRingCat.of (residueAway I r n) :=
  CommRingCat.ofHom (algebraMap (R ⧸ I ^ n) (residueAway I r n))

/-- **The chart of the `n`-th thickening cut out by `D(r)`.** By `thickeningOpen_basicOpen` this
is where `D(r) ⊆ |Spf R|` goes under `thickeningTopIso`; the `(Spec _).Opens` ascription is what
lets it be coerced to a `Scheme`. -/
abbrev chartOpen (n : ℕ) : (Spec (CommRingCat.of (R ⧸ I ^ (n + 1)))).Opens :=
  PrimeSpectrum.basicOpen (Ideal.Quotient.mk (I ^ (n + 1)) r)

/-- The tower's transition map sends the class of `r` to the class of `r`. -/
theorem stepRingHom_mk (n : ℕ) :
    (stepRingHom I n) (Ideal.Quotient.mk (I ^ (n + 1 + 1)) r) = Ideal.Quotient.mk (I ^ (n + 1)) r :=
  Ideal.Quotient.factor_mk (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) r

/-- The chart at level `n` is exactly the preimage of the chart at level `n + 1` — so the tower's
transition map restricts to the charts. -/
theorem chartOpen_le_preimage (n : ℕ) :
    chartOpen I r n ≤ (Spec.map (stepRingHom I n)) ⁻¹ᵁ (chartOpen I r (n + 1)) := by
  rw [SpecMap_preimage_basicOpen, stepRingHom_mk]

/-- **The transition map of the tower of charts.** -/
def chartStep (n : ℕ) : (chartOpen I r n).toScheme ⟶ (chartOpen I r (n + 1)).toScheme :=
  (Spec.map (stepRingHom I n)).resLE _ _ (chartOpen_le_preimage I r n)

@[reassoc]
theorem chartStep_comp_ι (n : ℕ) :
    chartStep I r n ≫ (chartOpen I r (n + 1)).ι =
      (chartOpen I r n).ι ≫ Spec.map (stepRingHom I n) :=
  Scheme.Hom.resLE_comp_ι _ _

/-- **The chart is affine**: Mathlib's `basicOpenIsoSpecAway` at the class of `r`. -/
def chartIsoSpecAway (n : ℕ) :
    (chartOpen I r n).toScheme ≅ Spec (CommRingCat.of (residueAway I r (n + 1))) :=
  basicOpenIsoSpecAway _

theorem chartIsoSpecAway_inv_comp_ι (n : ℕ) :
    (chartIsoSpecAway I r n).inv ≫ (chartOpen I r n).ι =
      Spec.map (residueAwayAlgebraMap I r (n + 1)) := by
  rw [chartIsoSpecAway, Iso.inv_comp_eq]
  exact (basicOpenIsoSpecAway_hom_SpecMap _).symm

/-- The level-`n` identification of issue 1043, in `CommRingCat`:
`R{1/r} ⧸ (I·R{1/r})ⁿ⁺¹ ≅ (R ⧸ Iⁿ⁺¹)_r̄`. -/
def chartRingIso (hI : I.FG) (n : ℕ) :
    CommRingCat.of (awayCompletion I r ⧸ (awayCompletionIdeal I r) ^ (n + 1)) ≅
      CommRingCat.of (residueAway I r (n + 1)) :=
  (awayCompletionResidueEquivPow I r hI (n + 1)).toCommRingCatIso

/-- **The ring map the chart inclusion is `Spec` of**, once the identification is applied:
`R ⧸ Iⁿ⁺¹ ⟶ R{1/r} ⧸ (I·R{1/r})ⁿ⁺¹`. -/
def chartRingMap (hI : I.FG) (n : ℕ) :
    CommRingCat.of (R ⧸ I ^ (n + 1)) ⟶
      CommRingCat.of (awayCompletion I r ⧸ (awayCompletionIdeal I r) ^ (n + 1)) :=
  residueAwayAlgebraMap I r (n + 1) ≫ (chartRingIso I r hI n).inv

/-- The residue tower's transition map is compatible with the structure maps to the localizations.
This is `residueAwayMap_algebraMap` (issue 1043) turned into an equation of ring maps, and it is
the only computation in this file that touches elements. -/
theorem stepRingHom_comp_residueAwayAlgebraMap (n : ℕ) :
    stepRingHom I n ≫ residueAwayAlgebraMap I r (n + 1) =
      residueAwayAlgebraMap I r (n + 1 + 1) ≫
        CommRingCat.ofHom (residueAwayMap I r (Nat.le_succ (n + 1))) := by
  refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_))
  simpa [stepRingHom, Ideal.Quotient.factor_mk] using
    (residueAwayMap_algebraMap I r (Nat.le_succ (n + 1)) x).symm

/-- `residueAwayMap_comp_equivPow_step` (issue 1043), in `CommRingCat`. -/
theorem chartRingIso_hom_comp_residueAwayMap (hI : I.FG) (n : ℕ) :
    (chartRingIso I r hI (n + 1)).hom ≫
        CommRingCat.ofHom (residueAwayMap I r (Nat.le_succ (n + 1))) =
      stepRingHom (awayCompletionIdeal I r) n ≫ (chartRingIso I r hI n).hom := by
  ext x
  exact RingHom.congr_fun (residueAwayMap_comp_equivPow_step I r hI n) x

theorem residueAwayMap_comp_chartRingIso_inv (hI : I.FG) (n : ℕ) :
    CommRingCat.ofHom (residueAwayMap I r (Nat.le_succ (n + 1))) ≫ (chartRingIso I r hI n).inv =
      (chartRingIso I r hI (n + 1)).inv ≫ stepRingHom (awayCompletionIdeal I r) n := by
  rw [← cancel_epi (chartRingIso I r hI (n + 1)).hom, Iso.hom_inv_id_assoc, ← Category.assoc,
    chartRingIso_hom_comp_residueAwayMap, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The identification is a map of towers, at ring level.** The two towers are
`n ↦ R ⧸ Iⁿ⁺¹` with `stepRingHom I` and `n ↦ R{1/r} ⧸ (I·R{1/r})ⁿ⁺¹` with
`stepRingHom (awayCompletionIdeal I r)`; this says `chartRingMap` is a morphism between them. -/
theorem stepRingHom_comp_chartRingMap (hI : I.FG) (n : ℕ) :
    stepRingHom I n ≫ chartRingMap I r hI n =
      chartRingMap I r hI (n + 1) ≫ stepRingHom (awayCompletionIdeal I r) n := by
  rw [chartRingMap, chartRingMap, ← Category.assoc, stepRingHom_comp_residueAwayAlgebraMap,
    Category.assoc, residueAwayMap_comp_chartRingIso_inv, Category.assoc]

/-- **The chart of the `n`-th thickening of `Spf R` over `D(r)` is `Spec` of the `n`-th thickening
of `R{1/r}`.** The composite of `basicOpenIsoSpecAway` with `Spec` of issue 1043's identification.
-/
def chartIsoSpec (hI : I.FG) (n : ℕ) :
    (chartOpen I r n).toScheme ≅
      Spec (CommRingCat.of (awayCompletion I r ⧸ (awayCompletionIdeal I r) ^ (n + 1))) :=
  (chartIsoSpecAway I r n).trans (Scheme.Spec.mapIso (chartRingIso I r hI n).op)

/-- Read through the identification, the chart inclusion is `Spec (chartRingMap …)`. -/
theorem chartIsoSpec_inv_comp_ι (hI : I.FG) (n : ℕ) :
    (chartIsoSpec I r hI n).inv ≫ (chartOpen I r n).ι = Spec.map (chartRingMap I r hI n) := by
  rw [chartIsoSpec, Iso.trans_inv, Category.assoc, chartIsoSpecAway_inv_comp_ι, chartRingMap,
    Spec.map_comp]
  rfl

/-- **The payoff: the identification is an isomorphism of towers, not merely levelwise.** The
charts of the tower of `Spf R` over `D(r)`, joined by `chartStep`, *are* the tower of thickenings
of `R{1/r}`, joined by `stepRingHom (awayCompletionIdeal I r)`.

This is what `thickeningRestrictionEquiv` (`IndSchemeColimitEquiv.lean`) needs in order to run for
`R{1/r}`. Producing an actual morphism `Spf R{1/r} ⟶ X` from it needs an affine *target*, which is
a hypothesis on `X` that nothing here supplies; that is the next step, not this one. -/
theorem chartStep_comp_chartIsoSpec (hI : I.FG) (n : ℕ) :
    chartStep I r n ≫ (chartIsoSpec I r hI (n + 1)).hom =
      (chartIsoSpec I r hI n).hom ≫
        Spec.map (stepRingHom (awayCompletionIdeal I r) n) := by
  rw [← Iso.eq_comp_inv, ← cancel_mono (chartOpen I r (n + 1)).ι, chartStep_comp_ι,
    Category.assoc, Category.assoc, chartIsoSpec_inv_comp_ι,
    (Iso.inv_comp_eq _).mp (chartIsoSpec_inv_comp_ι I r hI n), Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp, stepRingHom_comp_chartRingMap]

/-- The same identification in `LocallyRingedSpace`, which is the layer every `Thickening*` module
is stated about. No transport: `Scheme.forgetToLocallyRingedSpace.obj (Spec A)` and
`Spec.locallyRingedSpaceObj A` are the same object by `rfl`. -/
def chartIsoLRS (hI : I.FG) (n : ℕ) :
    (chartOpen I r n).toScheme.toLocallyRingedSpace ≅
      Spec.locallyRingedSpaceObj
        (CommRingCat.of (awayCompletion I r ⧸ (awayCompletionIdeal I r) ^ (n + 1))) :=
  Scheme.forgetToLocallyRingedSpace.mapIso (chartIsoSpec I r hI n)

/-- **The tower square, in `LocallyRingedSpace`.** The image of `chartStep_comp_chartIsoSpec`
under `Scheme.forgetToLocallyRingedSpace`, whose action on `Spec.map` is
`Spec.locallyRingedSpaceMap` definitionally. -/
theorem chartStepLRS_comp_chartIsoLRS (hI : I.FG) (n : ℕ) :
    Scheme.forgetToLocallyRingedSpace.map (chartStep I r n) ≫ (chartIsoLRS I r hI (n + 1)).hom =
      (chartIsoLRS I r hI n).hom ≫
        Spec.locallyRingedSpaceMap (stepRingHom (awayCompletionIdeal I r) n) :=
  (Scheme.forgetToLocallyRingedSpace.map_comp _ _).symm.trans
    ((congrArg Scheme.forgetToLocallyRingedSpace.map
        (chartStep_comp_chartIsoSpec I r hI n)).trans
      (Scheme.forgetToLocallyRingedSpace.map_comp _ _))

/-! ### The chart is a proper nonempty open as soon as `D(r)` is

`chartOpen` is an open of the `n`-th thickening, but whether it is *proper* and *nonempty* is
decided one level down, on `|Spf R| = Spec (R ⧸ I)`: the surjection `R ⧸ Iⁿ⁺¹ ↠ R ⧸ I` induces a
map of spectra under which `D(r) ⊆ |Spf R|` is the preimage of the chart. So both degeneracies
transfer, and the witness section below has only to exhibit an `r` with `D(r) ≠ ⊥, ⊤`.
-/

/-- The surjection `R ⧸ Iⁿ⁺¹ ↠ R ⧸ I` onto the residue ring, i.e. onto the level-`0` thickening.
-/
def residueStep (n : ℕ) : R ⧸ I ^ (n + 1) →+* R ⧸ I :=
  Ideal.Quotient.factor (Ideal.pow_le_self n.succ_ne_zero)

/-- **`D(r) ⊆ |Spf R|` is the preimage of the chart** under the map of spectra induced by
`residueStep`. True by definition once `Ideal.Quotient.factor_mk` has fired: both sides say that
the class of `r` avoids the prime. -/
theorem mem_chartOpen_comap (n : ℕ) (x : FormalSpectrum I) :
    PrimeSpectrum.comap (residueStep I n) x ∈ chartOpen I r n ↔ x ∈ basicOpen I r := by
  change Ideal.Quotient.mk (I ^ (n + 1)) r ∉ Ideal.comap (residueStep I n) x.asIdeal ↔ _
  rw [Ideal.mem_comap, residueStep, Ideal.Quotient.factor_mk]
  rfl

/-- **The chart is a proper open** whenever `D(r) ⊆ |Spf R|` is. -/
theorem chartOpen_ne_top (n : ℕ) (h : basicOpen I r ≠ ⊤) : chartOpen I r n ≠ ⊤ := fun hc =>
  h (eq_top_iff.mpr fun x _ => (mem_chartOpen_comap I r n x).mp (hc ▸ trivial))

/-- **The chart is nonempty** whenever `D(r) ⊆ |Spf R|` is. -/
theorem chartOpen_ne_bot (n : ℕ) (h : basicOpen I r ≠ ⊥) : chartOpen I r n ≠ ⊥ := by
  intro hc
  refine h (eq_bot_iff.mpr fun x hx => ?_)
  have hmem := (mem_chartOpen_comap I r n x).mpr hx
  rw [hc] at hmem
  exact hmem.elim

end Chart

section Alignment

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable {X : LocallyRingedSpace.{u}}

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The variance alignment.** `ThickeningBasicOpenRefinement.lean` produces a basic open
`D(r) ⊆ |Spf R|` sitting inside the pulled-back cover; `ThickeningChartRestrict.lean`'s
`thickeningChart` is instead a *preimage* `(f n) ⁻¹ U` of an open of the target `X`. This says the
first lands inside the second at every level, which is what lets `chartRestrict` be composed with
the affine identification above.

The transport is `thickeningOpen_basicOpen` (`StructureSheaf.lean`), which already says where
`D(r)` goes in the `n`-th thickening; the hypothesis `hr` is exactly what
`exists_basicOpen_le_map_commonBase` hands back. -/
theorem chartOpen_le_thickeningChart
    (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X)
    (hf : ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ f (n + 1) = f n)
    (U : Opens X.toTopCat) (r : R)
    (hr : basicOpen I r ≤ (Opens.map (commonBase I f)).obj U) (n : ℕ) :
    chartOpen I r n ≤ thickeningChart I f U n := by
  change PrimeSpectrum.basicOpen (Ideal.Quotient.mk (I ^ (n + 1)) r) ≤ thickeningChart I f U n
  rw [← thickeningOpen_basicOpen I n r]
  intro y hy
  have h1 : (thickeningTopIso I n).inv y ∈ basicOpen I r := hy
  have h2 := hr h1
  rw [map_commonBase_obj_eq_thickeningChart I f hf n U] at h2
  have h3 : (thickeningTopIso I n).hom ((thickeningTopIso I n).inv y) ∈
      thickeningChart I f U n := h2
  have hy2 : (thickeningTopIso I n).hom ((thickeningTopIso I n).inv y) = y :=
    (thickeningHomeomorph I (n + 1) n.succ_ne_zero).apply_symm_apply y
  rwa [hy2] at h3

end Alignment

section Witness

/-! ### Non-vacuity

Everything above holds at `I = ⊥`, where every thickening is `R` itself, and at an `r` whose
`D(r)` is `⊥` or `⊤`, where the chart says nothing about decomposing anything. The `2`-adic
witness of `TwoAdicWitness.lean` cannot discharge the second: `|Spf ℤ^| = PrimeSpectrum 𝔽₂` is a
one-point space, so every open of it is `⊥` or `⊤` — that is
`FormalSpectrum.twoAdic_exists_eq_top` in `FormalSchemes/TwoAdicDegeneracy.lean`.

So the witness here is `FormalLineWitness.lean`'s formal affine line `ℤ⟦X⟧`, whose residue ring is
`ℤ` and whose `|Spf|` is `Spec ℤ`. At `r = 2` the chart is proper (`twoChart_ne_top`) and nonempty
(the generic point of `Spec ℤ`), at *every* level of the tower.
-/

open Polynomial

private theorem fg_formalLineIdeal : (formalLineIdeal).FG :=
  polyXIdeal_fg.map _

private theorem basicOpen_two_ne_top : basicOpen formalLineIdeal 2 ≠ ⊤ := by
  have h := twoChart_ne_top true
  rwa [twoChart, if_pos rfl] at h

private theorem basicOpen_two_ne_bot : basicOpen formalLineIdeal 2 ≠ ⊥ := by
  intro h
  have hmem : ofPrimeInt ⟨⊥, Ideal.isPrime_bot⟩ ∈ basicOpen formalLineIdeal 2 := by
    rw [mem_basicOpen_ofPrimeInt, map_ofNat, map_ofNat]
    simp
  rw [h] at hmem
  exact hmem.elim

/-- **The chart of every thickening of `ℤ⟦X⟧` over `D(2)` is a proper open.** -/
theorem chartOpen_formalLine_ne_top (n : ℕ) : chartOpen formalLineIdeal 2 n ≠ ⊤ :=
  chartOpen_ne_top _ _ n basicOpen_two_ne_top

/-- **…and a nonempty one.** So the identification below is not an identification of the empty
scheme, nor of the whole thickening with itself. -/
theorem chartOpen_formalLine_ne_bot (n : ℕ) : chartOpen formalLineIdeal 2 n ≠ ⊥ :=
  chartOpen_ne_bot _ _ n basicOpen_two_ne_bot

/-- The tower square, instantiated at the witness — so the main theorem is exercised at an `I` and
an `r` for which the chart is provably neither `⊥` nor `⊤` at every level
(`chartOpen_formalLine_ne_bot`, `chartOpen_formalLine_ne_top`). -/
example (n : ℕ) :
    chartStep formalLineIdeal 2 n ≫
        (chartIsoSpec formalLineIdeal 2 fg_formalLineIdeal (n + 1)).hom =
      (chartIsoSpec formalLineIdeal 2 fg_formalLineIdeal n).hom ≫
        Spec.map (stepRingHom (awayCompletionIdeal formalLineIdeal 2) n) :=
  chartStep_comp_chartIsoSpec formalLineIdeal 2 fg_formalLineIdeal n

end Witness

end FormalSpectrum

end
