import FormalSchemes.TateAwaySplit
import FormalSchemes.TateOverlapChartIso

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000

/-!
# The two summands of the Tate two-chart overlap are affine

Fix an adic base `(R, I)` with `q ∈ I`, and let `A = R{x, y}/(x·y − q)` be the coordinate ring of
the formal Tate annulus with ideal of definition `J = I·A`. Two independent facts about the overlap
`D(x + y) = D(x) ⊔ D(y)` of the two charts of `𝔈_q` are already on `master`:

* the **geometric** one (671, `FormalSchemes.TateOverlapChartIso`): the two presentations of the
  overlap are isomorphic, `tateOverlapChartIso : Spf A{1/(x+y)}^ ≅ Spf A{1/x}^ ⨿ Spf A{1/y}^`,
  built from a *range* equality through `IsOpenImmersion.isoOfRangeEq`;
* the **algebraic** one (644, `FormalSchemes.TateAwaySplit`): the ring splitting
  `awaySplitAlgEquiv : A{1/(x+y)}^ ≃ₐ[R] A{1/x}^ × A{1/y}^`.

Nothing so far connects them, and that is a problem for the glue-datum comparison of 601's brick 4:
`tateOverlapChartIso` is opaque, so a term such as `coprod.inl ≫ (tateOverlapChartIso …).inv`
cannot be reduced to ring theory and none of 672's computation rules apply to it. This file closes
exactly that gap, and nothing else.

## The mono argument, which is why this is cheap

One might expect the identification to require "`Spf` of a product ring is a coproduct". It does
not. The chart `basicOpenChart J (x + y)` is a **mono** (an open immersion), and 671's second
factorisation law `tateOverlapChartIso_inv_fac` gives, after `coprod.inl_desc`,

```
(coprod.inl ≫ (tateOverlapChartIso …).inv) ≫ basicOpenChart J (x + y) = annulusOverlapChart R I q
```

so `coprod.inl ≫ inv` is the **unique** morphism whose composite with the chart at `x + y` is the
chart at `x`. Identifying it with an explicitly constructed affine map therefore reduces to
checking that the candidate satisfies the same equation — and that is a statement about ring maps
into `A{1/x}^`, which `awaySplitEquiv_of` already computes.

## Main definitions and results

* `AlgebraicGeometry.annulusOverlapSummandX` / `annulusOverlapSummandY`: `Spf` of the two
  projections of the splitting.
* `AlgebraicGeometry.annulusOverlapSummandX_comp` / `annulusOverlapSummandY_comp`: each is a
  morphism *over* the chart at `x + y`, recovering the chart at `x` resp. at `y`.
* `AlgebraicGeometry.coprod_inl_comp_tateOverlapChartIso_inv` and
  `coprod_inr_comp_tateOverlapChartIso_inv`: **the headline** — the coproduct summand inclusions of
  the overlap are the `Spf` of the splitting's projections; with the `hom` forms
  `annulusOverlapSummandX_comp_tateOverlapChartIso_hom` and its `y` analogue.
* `AlgebraicGeometry.coprod_desc_annulusOverlapSummand`: the same statement packaged as
  `coprod.desc … = (tateOverlapChartIso …).inv`.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1, §10.8.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits FormalSpectrum

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-! ### The two projections of the splitting, as ring maps -/

/-- The first projection `A{1/(x+y)}^ → A{1/x}^` of the splitting `awaySplitEquiv` (644). -/
def annulusOverlapProjX (hq : q ∈ I) :
    awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q + overlapY R I q) →+*
      awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q) :=
  (RingHom.fst _ _).comp (TateAwaySplit.awaySplitEquiv R I q hq).toRingHom

/-- The second projection `A{1/(x+y)}^ → A{1/y}^` of the splitting. -/
def annulusOverlapProjY (hq : q ∈ I) :
    awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q + overlapY R I q) →+*
      awayCompletion (annulusIdealOfDefinition R I q) (overlapY R I q) :=
  (RingHom.snd _ _).comp (TateAwaySplit.awaySplitEquiv R I q hq).toRingHom

/-- **The first projection is a map under `A`**: precomposing with the structural map
`A → A{1/(x+y)}^` gives the structural map `A → A{1/x}^`. This is `awaySplitEquiv_of`
(the computation rule of 644) read on the first component, and it is the single ring-theoretic
input of this file — both the `le_comap` side condition and the geometric factorisation below are
formal consequences of it. -/
theorem annulusOverlapProjX_comp_awayCompletionHom (hq : q ∈ I) :
    (annulusOverlapProjX R I q hq).comp
        (awayCompletionHom (annulusIdealOfDefinition R I q)
          (overlapX R I q + overlapY R I q)) =
      awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q) := by
  refine RingHom.ext fun a => ?_
  have h := TateAwaySplit.awaySplitEquiv_of R I q hq a
  simp only [annulusOverlapProjX, RingHom.coe_comp, Function.comp_apply, RingHom.coe_fst,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, awayCompletionHom,
    AssociatedGraded.algebraMap_eq_of, h]

/-- **The second projection is a map under `A`**, the `y` analogue of
`annulusOverlapProjX_comp_awayCompletionHom`. -/
theorem annulusOverlapProjY_comp_awayCompletionHom (hq : q ∈ I) :
    (annulusOverlapProjY R I q hq).comp
        (awayCompletionHom (annulusIdealOfDefinition R I q)
          (overlapX R I q + overlapY R I q)) =
      awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q) := by
  refine RingHom.ext fun a => ?_
  have h := TateAwaySplit.awaySplitEquiv_of R I q hq a
  simp only [annulusOverlapProjY, RingHom.coe_comp, Function.comp_apply, RingHom.coe_snd,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, awayCompletionHom,
    AssociatedGraded.algebraMap_eq_of, h]

/-! ### The `le_comap` side conditions -/

/-- A ring map between two away completions of `A` that is a map **under `A`** carries the ideal of
definition of the source into that of the target.

Stated generically in `S`, `f`, `g` and `φ` rather than at the Tate annulus: the proof is the
`Ideal.map_map` bookkeeping around `map_awayCompletionHom`, and instantiating it later keeps the
concrete completion types out of the elaborator's way. -/
theorem le_comap_of_comp_awayCompletionHom {S : Type u} [CommRing S] (K : Ideal S) (f g : S)
    (φ : awayCompletion K f →+* awayCompletion K g)
    (hφ : φ.comp (awayCompletionHom K f) = awayCompletionHom K g) :
    awayCompletionIdeal K f ≤ (awayCompletionIdeal K g).comap φ := by
  rw [← Ideal.map_le_iff_le_comap, ← map_awayCompletionHom K f, Ideal.map_map, hφ,
    map_awayCompletionHom]

/-! ### The two summand inclusions -/

/-- **The `x`-summand of the overlap, as an affine morphism**: `Spf` of the first projection of the
splitting, `Spf A{1/x}^ ⟶ Spf A{1/(x+y)}^`. -/
def annulusOverlapSummandX (hq : q ∈ I) :
    locallyRingedSpaceObj
        (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q)) ⟶
      locallyRingedSpaceObj (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (overlapX R I q + overlapY R I q)) :=
  locallyRingedSpaceMap
    (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q + overlapY R I q))
    (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
    (annulusOverlapProjX R I q hq)
    (le_comap_of_comp_awayCompletionHom _ _ _ _
      (annulusOverlapProjX_comp_awayCompletionHom R I q hq))

/-- **The `y`-summand of the overlap, as an affine morphism**. -/
def annulusOverlapSummandY (hq : q ∈ I) :
    locallyRingedSpaceObj
        (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q)) ⟶
      locallyRingedSpaceObj (awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (overlapX R I q + overlapY R I q)) :=
  locallyRingedSpaceMap
    (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q + overlapY R I q))
    (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))
    (annulusOverlapProjY R I q hq)
    (le_comap_of_comp_awayCompletionHom _ _ _ _
      (annulusOverlapProjY_comp_awayCompletionHom R I q hq))

/-- **The `x`-summand lies over the chart at `x + y`**: composing it with the basic-open chart at
`x + y` recovers the chart at `x`. This is `Spf` of
`annulusOverlapProjX_comp_awayCompletionHom`. -/
@[reassoc]
theorem annulusOverlapSummandX_comp (hq : q ∈ I) :
    annulusOverlapSummandX R I q hq ≫
        basicOpenChart (annulusIdealOfDefinition R I q) (overlapX R I q + overlapY R I q) =
      annulusOverlapChart R I q := by
  rw [annulusOverlapSummandX, basicOpenChart, annulusOverlapChart, basicOpenChart,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (ψ := annulusOverlapProjX R I q hq)
      (φ := awayCompletionHom (annulusIdealOfDefinition R I q)
        (overlapX R I q + overlapY R I q))
      (hIK := by
        rw [annulusOverlapProjX_comp_awayCompletionHom]
        exact le_comap_awayCompletionHom _ _)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _
    (annulusOverlapProjX_comp_awayCompletionHom R I q hq)

/-- **The `y`-summand lies over the chart at `x + y`**. -/
@[reassoc]
theorem annulusOverlapSummandY_comp (hq : q ∈ I) :
    annulusOverlapSummandY R I q hq ≫
        basicOpenChart (annulusIdealOfDefinition R I q) (overlapX R I q + overlapY R I q) =
      annulusOverlapChartY R I q := by
  rw [annulusOverlapSummandY, basicOpenChart, annulusOverlapChartY, basicOpenChart,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (ψ := annulusOverlapProjY R I q hq)
      (φ := awayCompletionHom (annulusIdealOfDefinition R I q)
        (overlapX R I q + overlapY R I q))
      (hIK := by
        rw [annulusOverlapProjY_comp_awayCompletionHom]
        exact le_comap_awayCompletionHom _ _)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _
    (annulusOverlapProjY_comp_awayCompletionHom R I q hq)

/-! ### The headline: the overlap identification is the splitting -/

/-- **The `x`-summand inclusion of the overlap is `Spf` of the splitting's first projection.**

Both sides are morphisms `Spf A{1/x}^ ⟶ Spf A{1/(x+y)}^` whose composite with the mono
`basicOpenChart J (x + y)` is `annulusOverlapChart` — for the left-hand side by 671's
`tateOverlapChartIso_inv_fac`, for the right-hand side by `annulusOverlapSummandX_comp`. -/
@[reassoc (attr := simp)]
theorem coprod_inl_comp_tateOverlapChartIso_inv (hq : q ∈ I) (hI : I.FG) :
    coprod.inl ≫ (tateOverlapChartIso R I q hq hI).inv = annulusOverlapSummandX R I q hq := by
  haveI := isOpenImmersion_basicOpenChart (annulusIdealOfDefinition R I q)
    (overlapX R I q + overlapY R I q) (annulusIdealOfDefinition_fg R I q hI)
  rw [← cancel_mono (basicOpenChart (annulusIdealOfDefinition R I q)
    (overlapX R I q + overlapY R I q)), Category.assoc, tateOverlapChartIso_inv_fac,
    coprod.inl_desc, annulusOverlapSummandX_comp]

/-- **The `y`-summand inclusion of the overlap is `Spf` of the splitting's second projection.** -/
@[reassoc (attr := simp)]
theorem coprod_inr_comp_tateOverlapChartIso_inv (hq : q ∈ I) (hI : I.FG) :
    coprod.inr ≫ (tateOverlapChartIso R I q hq hI).inv = annulusOverlapSummandY R I q hq := by
  haveI := isOpenImmersion_basicOpenChart (annulusIdealOfDefinition R I q)
    (overlapX R I q + overlapY R I q) (annulusIdealOfDefinition_fg R I q hI)
  rw [← cancel_mono (basicOpenChart (annulusIdealOfDefinition R I q)
    (overlapX R I q + overlapY R I q)), Category.assoc, tateOverlapChartIso_inv_fac,
    coprod.inr_desc, annulusOverlapSummandY_comp]

/-- The `hom` form of `coprod_inl_comp_tateOverlapChartIso_inv`: the summand map followed by the
overlap identification is the first coproduct inclusion. Shipped because the glue-datum comparison
rewrites in both directions. -/
@[reassoc (attr := simp)]
theorem annulusOverlapSummandX_comp_tateOverlapChartIso_hom (hq : q ∈ I) (hI : I.FG) :
    annulusOverlapSummandX R I q hq ≫ (tateOverlapChartIso R I q hq hI).hom = coprod.inl := by
  rw [← coprod_inl_comp_tateOverlapChartIso_inv R I q hq hI, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- The `hom` form of `coprod_inr_comp_tateOverlapChartIso_inv`. -/
@[reassoc (attr := simp)]
theorem annulusOverlapSummandY_comp_tateOverlapChartIso_hom (hq : q ∈ I) (hI : I.FG) :
    annulusOverlapSummandY R I q hq ≫ (tateOverlapChartIso R I q hq hI).hom = coprod.inr := by
  rw [← coprod_inr_comp_tateOverlapChartIso_inv R I q hq hI, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- **The packaged form**: the inverse of the overlap identification is the coproduct of the two
affine summand maps. This is the shape the glue-datum comparison of 601's brick 4 consumes, since
its transition law is checked summandwise by `coprod.hom_ext`. -/
@[reassoc]
theorem coprod_desc_annulusOverlapSummand (hq : q ∈ I) (hI : I.FG) :
    coprod.desc (annulusOverlapSummandX R I q hq) (annulusOverlapSummandY R I q hq) =
      (tateOverlapChartIso R I q hq hI).inv := by
  refine coprod.hom_ext ?_ ?_
  · rw [coprod.inl_desc, coprod_inl_comp_tateOverlapChartIso_inv]
  · rw [coprod.inr_desc, coprod_inr_comp_tateOverlapChartIso_inv]

end AlgebraicGeometry

end
