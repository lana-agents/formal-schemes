import FormalSchemes.ThickeningChartAffine
import FormalSchemes.IndSchemeColimitEquiv
import FormalSchemes.FormalLineWitness

set_option linter.style.header false

/-!
# Running the affine case on a chart: `Spf R{1/r} ⟶ X` from a compatible family

Umbrella 59 runs *cover `X` by affines → pull the cover back to `|Spf R|` → refine by basic opens
`D(r)` → **run the affine case on each chart** → glue*. This file is the fourth step.

The input is what the first three produce: a compatible family `f n : Spec (R ⧸ Iⁿ⁺¹) ⟶ X` out of
the infinitesimal thickenings, an open `U ⊆ X` on which `X` is affine, and a basic open
`D(r) ⊆ |Spf R|` lying over `U` (`hr`, which is exactly what
`exists_basicOpen_le_map_commonBase` hands back). The output is a morphism

```
Spf R{1/r} ⟶ X
```

together with the only thing about it a gluing argument can use — its restriction to the `n`-th
thickening of `R{1/r}`.

## How the affine case gets applied

`IndSchemeColimitEquiv.lean` has the affine-target colimit property as a bijection

```
(Spf S ⟶ Spec B)  ≃  ThickeningFamily J B
```

for any adic `(S, J)`. It is stated about *`Spf` of a ring*, so it cannot be applied to a chart of
`Spf R` unless that chart is itself the formal spectrum of a ring. Issue 1047
(`ThickeningChartAffine.lean`) is what makes it one: the chart of the `n`-th thickening cut out by
`D(r)` is `Spec (R{1/r} ⧸ (I·R{1/r})ⁿ⁺¹)`, **as a map of towers**. So the family restricted to
`D(r)` is literally a `ThickeningFamily (awayCompletionIdeal I r) B`, and the bijection applies at
`S = R{1/r}`.

Assembling the level-`n` member is four composable maps and needs no proof
(`chartFamily`). **The content of this file is that the assembled family is compatible**
(`chartFamily_step`) — the square

```
Spec (R{1/r} ⧸ (I·R{1/r})ⁿ⁺¹) ⟶ Spec (R{1/r} ⧸ (I·R{1/r})ⁿ⁺²)
             │                                  │
             ↓                                  ↓
          Spec B  ===========================  Spec B
```

which is where the three separate compatibilities on the tree — of the tower of charts
(`chartStepLRS_comp_chartIsoLRS`), of the restriction to `U`
(`stepChartRestrict_comp_chartRestrict`) and of the inclusion of the chart into it
(`chartStepLRS_comp_chartInclusion`, proved here) — have to be made to agree.

## The statement to cite downstream

`thickeningMap_comp_chartSpfHomAmbient`:

```lean
thickeningMap (awayCompletionIdeal I r) n ≫ chartSpfHomAmbient … =
  (chartIsoLRS I r hI n).inv ≫ (Spec _).ofRestrict (chartOpen I r n).isOpenEmbedding ≫ f n
```

Note what is **absent** from the right-hand side: the open `U` and the affine identification `e`.
The morphism `Spf R{1/r} ⟶ X` restricts on each thickening to `f n` read along the chart, with no
reference to the affine chart it was built from. That is the form the gluing step needs, and it is
what will make two overlapping charts agree.

## Main definitions

* `AlgebraicGeometry.LocallyRingedSpace.restrictLE`: restricting further along `V ≤ W`. Stated in
  the `LocallyRingedSpace` namespace, not in `FormalSpectrum` — see the implementation notes of
  `ThickeningChartRestrict.lean` for the rule.
* `FormalSpectrum.chartInclusion`: `D(r)`'s chart of the `n`-th thickening, included into
  `ThickeningChartRestrict.lean`'s chart over `U`.
* `FormalSpectrum.chartFamily`: the level-`n` member of the family on the tower of `R{1/r}`.
* `FormalSpectrum.chartSpfHom` and `FormalSpectrum.chartSpfHomAmbient`: the morphisms
  `Spf R{1/r} ⟶ Spec B` and `Spf R{1/r} ⟶ X`.

## Main results

* `FormalSpectrum.chartFamily_step`: **the theorem.** The family is compatible, so it is a
  `ThickeningFamily (awayCompletionIdeal I r) B`.
* `FormalSpectrum.thickeningMap_comp_chartSpfHom`, `FormalSpectrum.chartSpfHom_uniq`: the
  computation rule and its uniqueness.
* `FormalSpectrum.thickeningMap_comp_chartSpfHomAmbient`: the chart-free restriction rule quoted
  above.
* `FormalSpectrum.isAdicRing_awayCompletionIdeal`: `R{1/r}` is a complete adic ring for `I.FG`.
  Not previously named on the tree, although `AdicOnSections.lean` takes it as a hypothesis and
  `GeneralSeparatedChartCodiagonal.lean` re-derives it with `haveI` in eight places.

## Implementation notes

`IsAdicRing (awayCompletionIdeal I r)` enters the assembly section as an **instance hypothesis**,
not as something derived inside the proofs, because it appears in the *type* of `chartSpfHom`
(`locallyRingedSpaceObj (awayCompletionIdeal I r)` needs it). This is the shape
`AdicOnSections.lean` already uses; `isAdicRing_awayCompletionIdeal` is what a consumer
discharges it with, given `I.FG`.

Two declarations need `backward.isDefEq.respectTransparency false`. Both mix the two spellings of
one object: `chartStep` and `chartIsoLRS` are stated about `Spec (CommRingCat.of _)` (the `Scheme`,
because issue 1047 decided this layer knows what a `Scheme` is), while `chartRestrict` and
`stepChartRestrict` are stated about `Spec.locallyRingedSpaceObj (CommRingCat.of _)`. The two are
equal by `rfl` — that is exactly what `Scheme.forgetToLocallyRingedSpace_obj_Spec` says — but not
at `instances` transparency, so `rw` reports the goal as not type-correct and refuses to build a
motive. This is the same accommodation, for the same reason, that `ThickeningCocone.lean` carries.

The affine target enters as **data** (`B` and `e : X|_U ≅ Spec B`), not as an `IsAffineOpen`
predicate: `X` is a bare `LocallyRingedSpace`, so `IsAffineOpen` is not available, and narrowing
`X` to `Scheme` would undo the decision issue 1047 took. Carrying the iso costs nothing, because
an affine cover is what produced it in the first place.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.10).
* [The Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

/-- **Restricting further along an inclusion of opens.** For `V ≤ W`, the canonical morphism
`Y|_V ⟶ Y|_W` over `Y`, built by the universal property of the open immersion `Y|_W ⟶ Y`.

It lives in `AlgebraicGeometry.LocallyRingedSpace` rather than in `FormalSpectrum`: its statement
mentions no ring, no ideal and no spectrum. See `ThickeningChartRestrict.lean`'s implementation
notes for the rule. -/
def restrictLE {Y : LocallyRingedSpace.{u}} {V W : Opens Y.toTopCat} (h : V ≤ W) :
    Y.restrict V.isOpenEmbedding ⟶ Y.restrict W.isOpenEmbedding :=
  LocallyRingedSpace.IsOpenImmersion.lift (Y.ofRestrict W.isOpenEmbedding)
    (Y.ofRestrict V.isOpenEmbedding) (by
      rw [Y.range_ofRestrict W, Y.range_ofRestrict V]
      exact h)

/-- **`restrictLE` is a morphism over `Y`**, which is the only property of it anything uses. -/
@[reassoc]
theorem restrictLE_comp_ofRestrict {Y : LocallyRingedSpace.{u}} {V W : Opens Y.toTopCat}
    (h : V ≤ W) :
    restrictLE h ≫ Y.ofRestrict W.isOpenEmbedding = Y.ofRestrict V.isOpenEmbedding :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _

end AlgebraicGeometry.LocallyRingedSpace

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable {X : LocallyRingedSpace.{u}}

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **`R{1/r}` is a complete adic ring** for `I` finitely generated, with `I·R{1/r}` as ideal of
definition — so `Spf R{1/r}` is an affine formal scheme and the affine-target colimit property
applies to it. -/
theorem isAdicRing_awayCompletionIdeal (r : R) (hI : I.FG) :
    IsAdicRing (awayCompletionIdeal I r) :=
  AdicCompletion.isAdicRing_map _ (hI.map _)

variable (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X)
    (hf : ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ f (n + 1) = f n)
    (U : Opens X.toTopCat) (r : R)
    (hr : basicOpen I r ≤ (Opens.map (commonBase I f)).obj U)

/-- **The chart cut out by `D(r)`, inside the chart over `U`.** The variance alignment
`chartOpen_le_thickeningChart` says the first open is contained in the second at every level; this
is that containment as a morphism. -/
def chartInclusion (n : ℕ) :
    (Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).restrict
        (chartOpen I r n).isOpenEmbedding ⟶
      (Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).restrict
        (thickeningChart I f U n).isOpenEmbedding :=
  LocallyRingedSpace.restrictLE
    (Y := Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))))
    (chartOpen_le_thickeningChart I f hf U r hr n)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- `chartInclusion` is a morphism over the `n`-th thickening. -/
@[reassoc]
theorem chartInclusion_comp_ofRestrict (n : ℕ) :
    chartInclusion I f hf U r hr n ≫
        (Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).ofRestrict
          (thickeningChart I f U n).isOpenEmbedding =
      (Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).ofRestrict
        (chartOpen I r n).isOpenEmbedding :=
  LocallyRingedSpace.restrictLE_comp_ofRestrict _

omit [TopologicalSpace R] [IsAdicRing I] in
set_option linter.style.setOption false in
-- Mixes `Spec (CommRingCat.of _)` (from `chartStep`) with
-- `Spec.locallyRingedSpaceObj (CommRingCat.of _)` (from `stepChartRestrict`). The two are `rfl`
-- but not at `instances` transparency, which is the transparency `rw` builds its motive at.
set_option backward.isDefEq.respectTransparency false in
/-- **The chart inclusions commute with the two transition maps.** The tower of charts of `D(r)`
maps into the tower of charts over `U`, compatibly — proved by composing with the open immersion
`Y|_{chart} ⟶ Y`, which is a mono, where both sides become `chart ↪ Spec (R ⧸ Iⁿ⁺¹) ⟶
Spec (R ⧸ Iⁿ⁺²)`. -/
@[reassoc]
theorem chartStepLRS_comp_chartInclusion (n : ℕ) :
    Scheme.forgetToLocallyRingedSpace.map (chartStep I r n) ≫
        chartInclusion I f hf U r hr (n + 1) =
      chartInclusion I f hf U r hr n ≫ stepChartRestrict I f hf U n := by
  rw [← cancel_mono ((Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1 + 1)))).ofRestrict
      (thickeningChart I f U (n + 1)).isOpenEmbedding),
    Category.assoc, chartInclusion_comp_ofRestrict, Category.assoc,
    stepChartRestrict_comp_ofRestrict, ← Category.assoc, chartInclusion_comp_ofRestrict]
  exact congrArg Scheme.forgetToLocallyRingedSpace.map (chartStep_comp_ι I r n)

variable (hI : I.FG) (B : Type u) [CommRing B]
    (e : X.restrict U.isOpenEmbedding ≅ Spec.locallyRingedSpaceObj (CommRingCat.of B))

/-- **The level-`n` member of the family on the tower of `R{1/r}`**: identify the `n`-th
thickening of `R{1/r}` with the chart (issue 1047), include it into the chart over `U`, restrict
`f n` to that chart (issue 1036), and read `X|_U` as `Spec B`. Four composable maps; that this is
a *compatible* family is `chartFamily_step`. -/
def chartFamily (n : ℕ) :
    Spec.locallyRingedSpaceObj
        (CommRingCat.of (awayCompletion I r ⧸ (awayCompletionIdeal I r) ^ (n + 1))) ⟶
      Spec.locallyRingedSpaceObj (CommRingCat.of B) :=
  (chartIsoLRS I r hI n).inv ≫ chartInclusion I f hf U r hr n ≫ chartRestrict I f U n ≫ e.hom

omit [TopologicalSpace R] [IsAdicRing I] in
set_option linter.style.setOption false in
-- Same mixture of the two spellings of `Spec` as `chartStepLRS_comp_chartInclusion`; see the
-- implementation notes.
set_option backward.isDefEq.respectTransparency false in
/-- **The restricted family is a compatible family over the tower of `R{1/r}`.** This is the
theorem of this file: the transition map of the tower of `R{1/r}` is, read through the chart
identification, the transition map of the tower of charts, and the chart inclusions and the
restriction to `U` are each compatible with it. -/
theorem chartFamily_step (n : ℕ) :
    Spec.locallyRingedSpaceMap (stepRingHom (awayCompletionIdeal I r) n) ≫
        chartFamily I f hf U r hr hI B e (n + 1) =
      chartFamily I f hf U r hr hI B e n := by
  have hstep : Spec.locallyRingedSpaceMap (stepRingHom (awayCompletionIdeal I r) n) =
      (chartIsoLRS I r hI n).inv ≫ Scheme.forgetToLocallyRingedSpace.map (chartStep I r n) ≫
        (chartIsoLRS I r hI (n + 1)).hom := by
    rw [chartStepLRS_comp_chartIsoLRS, Iso.inv_hom_id_assoc]
  rw [chartFamily, chartFamily, hstep]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [chartStepLRS_comp_chartInclusion_assoc,
    ← Category.assoc (stepChartRestrict I f hf U n), stepChartRestrict_comp_chartRestrict]

section Assemble

variable [IsAdicRing (awayCompletionIdeal I r)]

/-- The family of `chartFamily`, packaged as a `ThickeningFamily` for the adic ring `R{1/r}`. -/
def chartThickeningFamily : ThickeningFamily (awayCompletionIdeal I r) B :=
  ⟨chartFamily I f hf U r hr hI B e, chartFamily_step I f hf U r hr hI B e⟩

/-- **The morphism `Spf R{1/r} ⟶ Spec B`**, by the affine-target colimit property
(`thickeningRestrictionEquiv`) applied to the adic ring `R{1/r}`. -/
def chartSpfHom : locallyRingedSpaceObj (awayCompletionIdeal I r) ⟶
    Spec.locallyRingedSpaceObj (CommRingCat.of B) :=
  (thickeningRestrictionEquiv (awayCompletionIdeal I r) B).symm
    (chartThickeningFamily I f hf U r hr hI B e)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Computation rule.** Cite this rather than unfolding `chartSpfHom`. -/
@[reassoc]
theorem thickeningMap_comp_chartSpfHom (n : ℕ) :
    thickeningMap (awayCompletionIdeal I r) n ≫ chartSpfHom I f hf U r hr hI B e =
      chartFamily I f hf U r hr hI B e n :=
  thickeningMap_comp_thickeningRestrictionEquiv_symm _ B _ n

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **…and it is the only morphism with that restriction**, since restriction to the thickenings
is injective. -/
theorem chartSpfHom_uniq
    (g : locallyRingedSpaceObj (awayCompletionIdeal I r) ⟶
      Spec.locallyRingedSpaceObj (CommRingCat.of B))
    (hg : ∀ n : ℕ, thickeningMap (awayCompletionIdeal I r) n ≫ g =
      chartFamily I f hf U r hr hI B e n) :
    g = chartSpfHom I f hf U r hr hI B e := by
  rw [chartSpfHom, Equiv.eq_symm_apply]
  exact Subtype.ext (funext hg)

/-- **The morphism into the ambient space**, `Spf R{1/r} ⟶ X`: compose with the affine
identification and the open immersion `X|_U ⟶ X`. -/
def chartSpfHomAmbient : locallyRingedSpaceObj (awayCompletionIdeal I r) ⟶ X :=
  chartSpfHom I f hf U r hr hI B e ≫ e.inv ≫ X.ofRestrict U.isOpenEmbedding

omit [TopologicalSpace R] [IsAdicRing I] in
set_option linter.style.setOption false in
-- Same mixture of the two spellings of `Spec`; see the implementation notes.
set_option backward.isDefEq.respectTransparency false in
/-- **The restriction rule, with the affine chart eliminated.** `chartSpfHomAmbient` restricts on
the `n`-th thickening of `R{1/r}` to `f n` read along the chart — and neither `U` nor `e` appears
on the right. This is the form a gluing argument consumes: it is a statement about the input
family alone, so two charts producing morphisms with this property agree wherever both are
defined. -/
theorem thickeningMap_comp_chartSpfHomAmbient (n : ℕ) :
    thickeningMap (awayCompletionIdeal I r) n ≫ chartSpfHomAmbient I f hf U r hr hI B e =
      (chartIsoLRS I r hI n).inv ≫
        (Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).ofRestrict
          (chartOpen I r n).isOpenEmbedding ≫ f n := by
  rw [chartSpfHomAmbient, ← Category.assoc, thickeningMap_comp_chartSpfHom, chartFamily]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [chartRestrict_comp_ofRestrict, chartInclusion_comp_ofRestrict_assoc]

end Assemble

section Witness

/-! ### Non-vacuity, and the one degeneracy that cannot be removed yet

Three degeneracies to rule out, and this section removes two of them.

`[IsAdicRing I]` holds at `I = ⊥`, where every thickening is `Spec R` and the tower is constant;
and `D(r)` may be `⊥` or `⊤`, where the chart decomposes nothing. Both are removed here by
building on `FormalLineWitness.lean`'s formal affine line `ℤ⟦X⟧` at `r = 2`, where
`ThickeningChartAffine.lean` already proves the chart is neither `⊥` nor `⊤` **at every level of
the tower** (`chartOpen_formalLine_ne_bot`, `chartOpen_formalLine_ne_top`).

The third is `U = ⊤`, and it is the one this file cannot remove. A witness with a proper `U`
needs an affine open of a *non-affine* `X` carrying a compatible family out of the thickenings,
and nothing on this tree produces one yet: the only formal-scheme-shaped `X` available is
`Spf R` itself, whose restriction to `D(s)` is `Spf R{1/s}` — an affine *formal* scheme, not the
`Spec` of a ring, so it is not an admissible `e`. That is a real gap and it is the honest reason
the witness below takes `U = ⊤`; the chart `D(2)` it runs on is genuinely proper regardless, so
`chartInclusion`, `chartIsoLRS` and the tower square are all exercised non-trivially.
-/

open Polynomial

attribute [local instance] isAdicRing_formalLineIdeal

/-- The affine target of the witness, `Spec ℤ`. -/
private abbrev witnessTarget : LocallyRingedSpace.{0} :=
  Spec.locallyRingedSpaceObj (CommRingCat.of ℤ)

/-- The witness family: the reductions of the structure map `ℤ → ℤ⟦X⟧`, compatible by
`specFamily`. -/
private def witnessFamily : ThickeningFamily formalLineIdeal ℤ :=
  specFamily formalLineIdeal ℤ (Int.castRingHom (AdicCompletion polyXIdeal ℤ[X]))

/-- `ℤ⟦X⟧{1/2}` is a complete adic ring, activated as a local instance so that
`Spf ℤ⟦X⟧{1/2}` can be spelled at all. Local, because `I.FG` is not synthesizable in general and a
global instance of this shape would be looked at by every unrelated search. -/
private theorem isAdicRing_awayCompletionIdeal_formalLine :
    IsAdicRing (awayCompletionIdeal formalLineIdeal 2) :=
  isAdicRing_awayCompletionIdeal _ _ (polyXIdeal_fg.map _)

attribute [local instance] isAdicRing_awayCompletionIdeal_formalLine

private theorem witness_hr :
    basicOpen formalLineIdeal 2 ≤
      (Opens.map (commonBase formalLineIdeal witnessFamily.1)).obj ⊤ := by
  simp

/-- **The tower square at the witness.** `chartFamily_step` instantiated at `ℤ⟦X⟧` and `r = 2`,
where the chart is a proper nonempty open of every thickening. -/
theorem chartFamily_step_formalLine (n : ℕ) :
    Spec.locallyRingedSpaceMap (stepRingHom (awayCompletionIdeal formalLineIdeal 2) n) ≫
        chartFamily formalLineIdeal witnessFamily.1 witnessFamily.2 ⊤ 2 witness_hr
          (polyXIdeal_fg.map _) ℤ witnessTarget.restrictTopIso (n + 1) =
      chartFamily formalLineIdeal witnessFamily.1 witnessFamily.2 ⊤ 2 witness_hr
        (polyXIdeal_fg.map _) ℤ witnessTarget.restrictTopIso n :=
  chartFamily_step _ _ _ _ _ _ _ _ _ n

/-- **The morphism `Spf ℤ⟦X⟧{1/2} ⟶ Spec ℤ` exists**, and restricts on each thickening to the
witness family read along the chart `D(2)`. -/
theorem thickeningMap_comp_chartSpfHomAmbient_formalLine (n : ℕ) :
    thickeningMap (awayCompletionIdeal formalLineIdeal 2) n ≫
        chartSpfHomAmbient formalLineIdeal witnessFamily.1 witnessFamily.2 ⊤ 2 witness_hr
          (polyXIdeal_fg.map _) ℤ witnessTarget.restrictTopIso =
      (chartIsoLRS formalLineIdeal 2 (polyXIdeal_fg.map _) n).inv ≫
        (Spec.locallyRingedSpaceObj (CommRingCat.of
            (AdicCompletion polyXIdeal ℤ[X] ⧸ formalLineIdeal ^ (n + 1)))).ofRestrict
          (chartOpen formalLineIdeal 2 n).isOpenEmbedding ≫ witnessFamily.1 n :=
  thickeningMap_comp_chartSpfHomAmbient _ _ _ _ _ _ _ _ _ n

end Witness

end FormalSpectrum

end
