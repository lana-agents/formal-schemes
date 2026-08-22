import FormalSchemes.CompletedTensorAwayInterchangeMixedPullback
import FormalSchemes.TateOverlapSummandAffine
import FormalSchemes.TateTensorOverlapChartIso

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000

/-!
# The summands of the one-sided tensored Tate overlaps are `Spf` of the splitting's projections

Fix an adic base `(R, I)` with `I` finitely generated and a Tate parameter `q ∈ I`, let
`A = R{x, y}/(x·y − q)` be the coordinate ring of the formal Tate annulus and `C = A ⊗̂_R A`.

738/739 (`FormalSchemes.TateTensorOverlapChartIso`, `…IsoBoth`) identified each of the three
overlap shapes of `Spf A ×_{Spf R} Spf A` in its two presentations, for instance

```
tensorOverlapChartIsoFirst : Spf(A{1/(x+y)}^ ⊗̂_R A) ≅ Spf(A{1/x}^ ⊗̂_R A) ⨿ Spf(A{1/y}^ ⊗̂_R A) .
```

Those isomorphisms come from `IsOpenImmersion.isoOfRangeEq`, so they say what the two objects are
and **nothing about what the maps do**: a term such as
`coprod.inl ≫ (tensorOverlapChartIsoFirst …).inv` is opaque, and the glue-datum comparison of
601's brick 4 (705c) reduces its transition law summandwise by `coprod.hom_ext` and therefore has
to see through exactly those terms. This file closes that gap and nothing else.

It is the **tensored analogue of 703** (`FormalSchemes.TateOverlapSummandAffine`), which did the
same one level down, for the un-tensored overlap `Spf A{1/(x+y)}^ ≅ Spf A{1/x}^ ⨿ Spf A{1/y}^`.

## The two arguments, both cheap

*The mono argument*, inherited verbatim from 703. Each merged chart
(`interchangeOpenImmersion`, `rightInterchangeOpenImmersion`, `bothInterchangeOpenImmersion`) is an
open immersion, hence a **mono**, and each `…_inv_fac` law of 738/739 says that the coproduct chart
factors through it. So a summand inclusion is the *unique* morphism whose composite with the merged
chart is the corresponding one-summand chart, and identifying it with an explicitly constructed
affine morphism reduces to checking that same equation for the candidate.

*The functoriality argument*, which is what makes the check trivial here. All three merged charts
are already known to be `CompletedTensorProduct.mapSpf` of localization maps
(`interchangeOpenImmersion_eq_mapSpf`, `rightInterchangeOpenImmersion_eq_mapSpf`,
`bothInterchangeOpenImmersion_eq_mapSpf`), so the required equation is `mapSpf_comp` together with
the *ring-level* statement that the splitting's projection is a map **under `A`** — which is 703's
`annulusOverlapProjX_comp_awayCompletionHom`. No point-set argument, and in particular **no ring
splitting of `A{1/(x+y)}^ ⊗̂_R A` is claimed or needed**: the splitting is used on the un-tensored
factor only.

## One wrinkle: two spellings of the annulus ideal of definition

671/703 are stated with `annulusIdealOfDefinition R I q`, while the generic interchange machinery —
and hence 738/739 — is stated with `I.map (algebraMap R (annulusAlgebra R I q))`. The two ideals are
equal (`annulus_map_eq`) but **not** definitionally so, hence the generic transport
`FormalSpectrum.awayCompletionCongrₐ` below, which is `subst`-and-`rfl` and is used exactly twice,
to conjugate 703's projection into the spelling 738/739 use.

## Main definitions and results

* `FormalSpectrum.awayCompletionCongrₐ`: transport of an away completion along an equality of
  ideals of definition, with its "under `A`" law `awayCompletionCongrₐ_comp`.
* `AlgebraicGeometry.annulusOverlapProjXₐ` / `annulusOverlapProjYₐ`: 703's two projections as
  `R`-algebra homomorphisms, and `AlgebraicGeometry.annulusTensorProjXₐ` / `annulusTensorProjYₐ`:
  the same in the tensored spelling, each with its "under `A`" law.
* `AlgebraicGeometry.tensorOverlapSummandXFirst` and its three siblings (`Y` × `First`/`Second`):
  the one-sided summand inclusions as `mapSpf`. The four both-factor summands are in
  `FormalSchemes.TateTensorOverlapSummandAffineBoth`, split off for build cost.
* `AlgebraicGeometry.coprod_inl_comp_tensorOverlapChartIsoFirst_inv` and its siblings: **the
  headline** — the coproduct summand inclusions of each tensored overlap are these affine
  morphisms; with the `hom` forms and the packaged `coprod.desc … = …inv` forms that 705c consumes.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8, §10.15.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits FormalSpectrum
open CompletedTensorProduct CompletedTensorAwayInterchange

universe u

namespace FormalSpectrum

variable (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]

/-! ### Transport of an away completion along an equality of ideals of definition -/

/-- **Transport an away completion along an equality of ideals of definition.** `awayCompletion K f`
depends on `K` only through `K.map (algebraMap A A_f)`, so equal ideals give canonically isomorphic
completions; the isomorphism is the identity after `subst`. -/
def awayCompletionCongrₐ {K₁ K₂ : Ideal A} (h : K₁ = K₂) (f : A) :
    awayCompletion K₁ f ≃ₐ[R] awayCompletion K₂ f := by
  subst h; exact AlgEquiv.refl

/-- **The transport is a map under `A`**: it fixes the structural image of `A`. This is the only
property of `awayCompletionCongrₐ` used below, and it is what lets a "map under `A`" statement be
carried between the two spellings of the annulus ideal of definition. -/
theorem awayCompletionCongrₐ_comp {K₁ K₂ : Ideal A} (h : K₁ = K₂) (f : A) :
    ((awayCompletionCongrₐ R h f).toAlgHom).comp
        (IsScalarTower.toAlgHom R A (awayCompletion K₁ f)) =
      IsScalarTower.toAlgHom R A (awayCompletion K₂ f) := by
  subst h; rfl

end FormalSpectrum

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-! ### The two projections of the splitting, as `R`-algebra homomorphisms

703 ships them as `RingHom`s; `CompletedTensorProduct.mapSpf` consumes `AlgHom`s, and 644's
splitting is already an `R`-algebra equivalence, so the upgrade is definitional. -/

/-- The first projection `A{1/(x+y)}^ →ₐ[R] A{1/x}^` of 644's splitting. Its coercion is `rfl`-equal
to 703's `annulusOverlapProjX`. -/
def annulusOverlapProjXₐ (hq : q ∈ I) :
    awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q + overlapY R I q) →ₐ[R]
      awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q) :=
  (AlgHom.fst R _ _).comp (TateAwaySplit.awaySplitAlgEquiv R I q hq).toAlgHom

/-- The second projection `A{1/(x+y)}^ →ₐ[R] A{1/y}^` of 644's splitting. -/
def annulusOverlapProjYₐ (hq : q ∈ I) :
    awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q + overlapY R I q) →ₐ[R]
      awayCompletion (annulusIdealOfDefinition R I q) (overlapY R I q) :=
  (AlgHom.snd R _ _).comp (TateAwaySplit.awaySplitAlgEquiv R I q hq).toAlgHom

/-- **The first projection is a map under `A`**, in the `AlgHom` spelling: 703's
`annulusOverlapProjX_comp_awayCompletionHom` read through the (definitional) identification of
`awayCompletionHom` with the structural algebra map. -/
theorem annulusOverlapProjXₐ_comp (hq : q ∈ I) :
    (annulusOverlapProjXₐ R I q hq).comp
        (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
          (awayCompletion (annulusIdealOfDefinition R I q)
            (overlapX R I q + overlapY R I q))) =
      IsScalarTower.toAlgHom R (annulusAlgebra R I q)
        (awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q)) := by
  refine AlgHom.ext fun a => ?_
  exact DFunLike.congr_fun (annulusOverlapProjX_comp_awayCompletionHom R I q hq) a

/-- **The second projection is a map under `A`**, in the `AlgHom` spelling. -/
theorem annulusOverlapProjYₐ_comp (hq : q ∈ I) :
    (annulusOverlapProjYₐ R I q hq).comp
        (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
          (awayCompletion (annulusIdealOfDefinition R I q)
            (overlapX R I q + overlapY R I q))) =
      IsScalarTower.toAlgHom R (annulusAlgebra R I q)
        (awayCompletion (annulusIdealOfDefinition R I q) (overlapY R I q)) := by
  refine AlgHom.ext fun a => ?_
  exact DFunLike.congr_fun (annulusOverlapProjY_comp_awayCompletionHom R I q hq) a

/-! ### The same projections in the spelling the tensored charts use

The generic interchange machinery writes the annulus ideal of definition as
`I·A = I.map (algebraMap R A)`, which is equal to but not definitionally the same as
`annulusIdealOfDefinition R I q`. Conjugating by `awayCompletionCongrₐ` moves 703's projections
across, and the "under `A`" laws survive because all three factors are maps under `A`. -/

/-- The first projection of the splitting, in the `I·A` spelling of the annulus ideal of
definition — the spelling `interchangeOpenImmersion` and 738/739 use. -/
def annulusTensorProjXₐ (hq : q ∈ I) :
    awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapX R I q + overlapY R I q) →ₐ[R]
      awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q) :=
  ((awayCompletionCongrₐ R (annulus_map_eq R I q).symm (overlapX R I q)).toAlgHom).comp
    ((annulusOverlapProjXₐ R I q hq).comp
      ((awayCompletionCongrₐ R (annulus_map_eq R I q)
        (overlapX R I q + overlapY R I q)).toAlgHom))

/-- The second projection of the splitting, in the `I·A` spelling. -/
def annulusTensorProjYₐ (hq : q ∈ I) :
    awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapX R I q + overlapY R I q) →ₐ[R]
      awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q) :=
  ((awayCompletionCongrₐ R (annulus_map_eq R I q).symm (overlapY R I q)).toAlgHom).comp
    ((annulusOverlapProjYₐ R I q hq).comp
      ((awayCompletionCongrₐ R (annulus_map_eq R I q)
        (overlapX R I q + overlapY R I q)).toAlgHom))

/-- **The first projection is a map under `A`**, in the tensored spelling. This is the single
ring-theoretic input of every geometric statement below. -/
theorem annulusTensorProjXₐ_comp (hq : q ∈ I) :
    (annulusTensorProjXₐ R I q hq).comp
        (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapX R I q + overlapY R I q))) =
      IsScalarTower.toAlgHom R (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)) := by
  rw [annulusTensorProjXₐ, AlgHom.comp_assoc, AlgHom.comp_assoc, awayCompletionCongrₐ_comp,
    annulusOverlapProjXₐ_comp, awayCompletionCongrₐ_comp]

/-- **The second projection is a map under `A`**, in the tensored spelling. -/
theorem annulusTensorProjYₐ_comp (hq : q ∈ I) :
    (annulusTensorProjYₐ R I q hq).comp
        (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapX R I q + overlapY R I q))) =
      IsScalarTower.toAlgHom R (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)) := by
  rw [annulusTensorProjYₐ, AlgHom.comp_assoc, AlgHom.comp_assoc, awayCompletionCongrₐ_comp,
    annulusOverlapProjYₐ_comp, awayCompletionCongrₐ_comp]

/-! ### The first-factor overlap: the two summand inclusions

`tensorOverlapChartIsoFirst` identifies `Spf(A{1/(x+y)}^ ⊗̂_R A)` with
`Spf(A{1/x}^ ⊗̂_R A) ⨿ Spf(A{1/y}^ ⊗̂_R A)`. The two summand inclusions are `mapSpf` of the
splitting's projections, tensored with the identity of the second factor. -/

/-- **The `x`-summand of the tensored first-factor overlap, as an affine morphism**: `mapSpf` of the
splitting's first projection against the identity of the second factor. -/
def tensorOverlapSummandXFirst (hq : q ∈ I) (hI : I.FG) :
    locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
        (annulusAlgebra R I q)) ⟶
      locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q + overlapY R I q)) (annulusAlgebra R I q)) :=
  CompletedTensorProduct.mapSpf hI (annulusTensorProjXₐ R I q hq)
    (AlgHom.id R (annulusAlgebra R I q))

/-- **The `y`-summand of the tensored first-factor overlap, as an affine morphism.** -/
def tensorOverlapSummandYFirst (hq : q ∈ I) (hI : I.FG) :
    locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
        (annulusAlgebra R I q)) ⟶
      locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q + overlapY R I q)) (annulusAlgebra R I q)) :=
  CompletedTensorProduct.mapSpf hI (annulusTensorProjYₐ R I q hq)
    (AlgHom.id R (annulusAlgebra R I q))

/-- **The `x`-summand lies over the merged chart at `x + y`**: `mapSpf`-functoriality plus the fact
that the projection is a map under `A`. -/
@[reassoc]
theorem tensorOverlapSummandXFirst_comp (hq : q ∈ I) (hI : I.FG) :
    tensorOverlapSummandXFirst R I q hq hI ≫
        interchangeOpenImmersion (B := annulusAlgebra R I q) I
          (overlapX R I q + overlapY R I q) hI =
      interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapX R I q) hI := by
  rw [tensorOverlapSummandXFirst, interchangeOpenImmersion_eq_mapSpf,
    interchangeOpenImmersion_eq_mapSpf, ← CompletedTensorProduct.mapSpf_comp,
    annulusTensorProjXₐ_comp, AlgHom.id_comp]

/-- **The `y`-summand lies over the merged chart at `x + y`.** -/
@[reassoc]
theorem tensorOverlapSummandYFirst_comp (hq : q ∈ I) (hI : I.FG) :
    tensorOverlapSummandYFirst R I q hq hI ≫
        interchangeOpenImmersion (B := annulusAlgebra R I q) I
          (overlapX R I q + overlapY R I q) hI =
      interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapY R I q) hI := by
  rw [tensorOverlapSummandYFirst, interchangeOpenImmersion_eq_mapSpf,
    interchangeOpenImmersion_eq_mapSpf, ← CompletedTensorProduct.mapSpf_comp,
    annulusTensorProjYₐ_comp, AlgHom.id_comp]

/-- **The first summand inclusion of the tensored first-factor overlap is `mapSpf` of the
splitting's first projection.** Both sides are morphisms into `Spf(A{1/(x+y)}^ ⊗̂_R A)` whose
composite with the mono `interchangeOpenImmersion … (x + y)` is the merged chart at `x`. -/
@[reassoc (attr := simp)]
theorem coprod_inl_comp_tensorOverlapChartIsoFirst_inv (hq : q ∈ I) (hI : I.FG) :
    coprod.inl ≫ (tensorOverlapChartIsoFirst R I q hq hI).inv =
      tensorOverlapSummandXFirst R I q hq hI := by
  haveI := isOpenImmersion_interchangeOpenImmersion (B := annulusAlgebra R I q) I
    (overlapX R I q + overlapY R I q) hI
  rw [← cancel_mono (interchangeOpenImmersion (B := annulusAlgebra R I q) I
    (overlapX R I q + overlapY R I q) hI), Category.assoc,
    tensorOverlapChartIsoFirst_inv_fac, firstFactorOverlapChart, coprod.inl_desc,
    tensorOverlapSummandXFirst_comp]

/-- **The second summand inclusion of the tensored first-factor overlap.** -/
@[reassoc (attr := simp)]
theorem coprod_inr_comp_tensorOverlapChartIsoFirst_inv (hq : q ∈ I) (hI : I.FG) :
    coprod.inr ≫ (tensorOverlapChartIsoFirst R I q hq hI).inv =
      tensorOverlapSummandYFirst R I q hq hI := by
  haveI := isOpenImmersion_interchangeOpenImmersion (B := annulusAlgebra R I q) I
    (overlapX R I q + overlapY R I q) hI
  rw [← cancel_mono (interchangeOpenImmersion (B := annulusAlgebra R I q) I
    (overlapX R I q + overlapY R I q) hI), Category.assoc,
    tensorOverlapChartIsoFirst_inv_fac, firstFactorOverlapChart, coprod.inr_desc,
    tensorOverlapSummandYFirst_comp]

/-- The `hom` form of `coprod_inl_comp_tensorOverlapChartIsoFirst_inv`. -/
@[reassoc (attr := simp)]
theorem tensorOverlapSummandXFirst_comp_tensorOverlapChartIsoFirst_hom (hq : q ∈ I) (hI : I.FG) :
    tensorOverlapSummandXFirst R I q hq hI ≫ (tensorOverlapChartIsoFirst R I q hq hI).hom =
      coprod.inl := by
  rw [← coprod_inl_comp_tensorOverlapChartIsoFirst_inv R I q hq hI, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- The `hom` form of `coprod_inr_comp_tensorOverlapChartIsoFirst_inv`. -/
@[reassoc (attr := simp)]
theorem tensorOverlapSummandYFirst_comp_tensorOverlapChartIsoFirst_hom (hq : q ∈ I) (hI : I.FG) :
    tensorOverlapSummandYFirst R I q hq hI ≫ (tensorOverlapChartIsoFirst R I q hq hI).hom =
      coprod.inr := by
  rw [← coprod_inr_comp_tensorOverlapChartIsoFirst_inv R I q hq hI, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- **The packaged form**: the inverse of the tensored first-factor identification is the coproduct
of the two affine summand maps. This is the shape 705c's `coprod.hom_ext` consumes. -/
@[reassoc]
theorem coprod_desc_tensorOverlapSummandFirst (hq : q ∈ I) (hI : I.FG) :
    coprod.desc (tensorOverlapSummandXFirst R I q hq hI)
        (tensorOverlapSummandYFirst R I q hq hI) =
      (tensorOverlapChartIsoFirst R I q hq hI).inv := by
  refine coprod.hom_ext ?_ ?_
  · rw [coprod.inl_desc, coprod_inl_comp_tensorOverlapChartIsoFirst_inv]
  · rw [coprod.inr_desc, coprod_inr_comp_tensorOverlapChartIsoFirst_inv]

/-! ### The second-factor overlap: the two summand inclusions

The mirror of the previous section, with the identity in the *first* slot of `mapSpf`. -/

/-- **The `x`-summand of the tensored second-factor overlap, as an affine morphism.** -/
def tensorOverlapSummandXSecond (hq : q ∈ I) (hI : I.FG) :
    locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) ⟶
      locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q + overlapY R I q))) :=
  CompletedTensorProduct.mapSpf hI (AlgHom.id R (annulusAlgebra R I q))
    (annulusTensorProjXₐ R I q hq)

/-- **The `y`-summand of the tensored second-factor overlap, as an affine morphism.** -/
def tensorOverlapSummandYSecond (hq : q ∈ I) (hI : I.FG) :
    locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) ⟶
      locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q + overlapY R I q))) :=
  CompletedTensorProduct.mapSpf hI (AlgHom.id R (annulusAlgebra R I q))
    (annulusTensorProjYₐ R I q hq)

/-- **The `x`-summand lies over the merged second-factor chart at `x + y`.** -/
@[reassoc]
theorem tensorOverlapSummandXSecond_comp (hq : q ∈ I) (hI : I.FG) :
    tensorOverlapSummandXSecond R I q hq hI ≫
        rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I
          (overlapX R I q + overlapY R I q) hI =
      rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapX R I q) hI := by
  rw [tensorOverlapSummandXSecond, rightInterchangeOpenImmersion_eq_mapSpf,
    rightInterchangeOpenImmersion_eq_mapSpf, ← CompletedTensorProduct.mapSpf_comp,
    annulusTensorProjXₐ_comp, AlgHom.id_comp]

/-- **The `y`-summand lies over the merged second-factor chart at `x + y`.** -/
@[reassoc]
theorem tensorOverlapSummandYSecond_comp (hq : q ∈ I) (hI : I.FG) :
    tensorOverlapSummandYSecond R I q hq hI ≫
        rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I
          (overlapX R I q + overlapY R I q) hI =
      rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapY R I q) hI := by
  rw [tensorOverlapSummandYSecond, rightInterchangeOpenImmersion_eq_mapSpf,
    rightInterchangeOpenImmersion_eq_mapSpf, ← CompletedTensorProduct.mapSpf_comp,
    annulusTensorProjYₐ_comp, AlgHom.id_comp]

/-- **The first summand inclusion of the tensored second-factor overlap.** -/
@[reassoc (attr := simp)]
theorem coprod_inl_comp_tensorOverlapChartIsoSecond_inv (hq : q ∈ I) (hI : I.FG) :
    coprod.inl ≫ (tensorOverlapChartIsoSecond R I q hq hI).inv =
      tensorOverlapSummandXSecond R I q hq hI := by
  haveI := isOpenImmersion_rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I
    (overlapX R I q + overlapY R I q) hI
  rw [← cancel_mono (rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I
    (overlapX R I q + overlapY R I q) hI), Category.assoc,
    tensorOverlapChartIsoSecond_inv_fac, secondFactorOverlapChart, coprod.inl_desc,
    tensorOverlapSummandXSecond_comp]

/-- **The second summand inclusion of the tensored second-factor overlap.** -/
@[reassoc (attr := simp)]
theorem coprod_inr_comp_tensorOverlapChartIsoSecond_inv (hq : q ∈ I) (hI : I.FG) :
    coprod.inr ≫ (tensorOverlapChartIsoSecond R I q hq hI).inv =
      tensorOverlapSummandYSecond R I q hq hI := by
  haveI := isOpenImmersion_rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I
    (overlapX R I q + overlapY R I q) hI
  rw [← cancel_mono (rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I
    (overlapX R I q + overlapY R I q) hI), Category.assoc,
    tensorOverlapChartIsoSecond_inv_fac, secondFactorOverlapChart, coprod.inr_desc,
    tensorOverlapSummandYSecond_comp]

/-- The `hom` form of `coprod_inl_comp_tensorOverlapChartIsoSecond_inv`. -/
@[reassoc (attr := simp)]
theorem tensorOverlapSummandXSecond_comp_tensorOverlapChartIsoSecond_hom (hq : q ∈ I) (hI : I.FG) :
    tensorOverlapSummandXSecond R I q hq hI ≫ (tensorOverlapChartIsoSecond R I q hq hI).hom =
      coprod.inl := by
  rw [← coprod_inl_comp_tensorOverlapChartIsoSecond_inv R I q hq hI, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- The `hom` form of `coprod_inr_comp_tensorOverlapChartIsoSecond_inv`. -/
@[reassoc (attr := simp)]
theorem tensorOverlapSummandYSecond_comp_tensorOverlapChartIsoSecond_hom (hq : q ∈ I) (hI : I.FG) :
    tensorOverlapSummandYSecond R I q hq hI ≫ (tensorOverlapChartIsoSecond R I q hq hI).hom =
      coprod.inr := by
  rw [← coprod_inr_comp_tensorOverlapChartIsoSecond_inv R I q hq hI, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- **The packaged form** for the second-factor overlap. -/
@[reassoc]
theorem coprod_desc_tensorOverlapSummandSecond (hq : q ∈ I) (hI : I.FG) :
    coprod.desc (tensorOverlapSummandXSecond R I q hq hI)
        (tensorOverlapSummandYSecond R I q hq hI) =
      (tensorOverlapChartIsoSecond R I q hq hI).inv := by
  refine coprod.hom_ext ?_ ?_
  · rw [coprod.inl_desc, coprod_inl_comp_tensorOverlapChartIsoSecond_inv]
  · rw [coprod.inr_desc, coprod_inr_comp_tensorOverlapChartIsoSecond_inv]

end AlgebraicGeometry

end
