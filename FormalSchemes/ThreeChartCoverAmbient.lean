import FormalSchemes.ThreeChartCoverSeparated

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The three-chart open cover lives over its ambient affine `Spf A`

`FormalSchemes.ThreeChartCoverDatum` presents the union `D(f₀) ∪ D(f₁) ∪ D(f₂)` of three basic
opens of `Spf A` as an `AffineChartedFibreDatumX`, and `ThreeChartCover.gluedX` is the formal
scheme it glues. Everything proved about that object so far — separatedness
(`FormalSchemes.ThreeChartCoverSeparatedScheme`, issue 852) and topological finite type
(`FormalSchemes.ThreeChartCoverTopFiniteType`, issue 858) — is a statement about the glued object
of a *presentation*, and both files say so in a docstring section: the cover has no construction
independent of its charts, so its structural morphism can only be named as
`(datumX I f B hI).xStructMap`.

This file supplies the first thing that points the other way: the **canonical morphism from the
glued object down to the ambient affine**,

```
coverMap : gluedX ⟶ Spf A
```

glued from the three chart inclusions `Spf(A{1/f_i}) ⟶ Spf A`, together with the identity saying
it is a morphism **over** `Spf R`:

```
coverMap ≫ (Spf A ⟶ Spf R)  =  xStructMap.
```

## What this is not

`coverMap` is **not** claimed to be an open immersion here, and its image is **not** identified
with `D(f₀) ∪ D(f₁) ∪ D(f₂) ⊆ Spf A`. Those are the two remaining bricks of the open-subscheme
identification, and they carry the geometric content; this file carries none of it. What it does
is put the object in the frame where those claims can be *stated*: before it, there was no morphism
`gluedX ⟶ Spf A` at all, so "the glued object is an open formal subscheme of `Spf A`" was not a
sentence one could write down.

Consequently nothing here makes the separatedness or finite-type statements chart-free. That still
needs the immersion.

## The crux, and where it came from

Gluing the chart inclusions needs the double-overlap square
`chartInclusion_naturality`, and its whole content is that the chart transition `τ i j` fixes the
image of **`A`** — not merely of the base `R`. That is exactly
`ThreeChartCover.tau_symm_algebraMap` (`FormalSchemes.ThreeChartCoverSeparated`, issue 779), which
was proved for the separatedness argument and is reused verbatim here rather than rebuilt. The
comparison with `AffineChartedFibreDatumX.xStructMap_naturality`
(`FormalSchemes.GeneralFibreProductExposeXStructMap`) is exact: that proof has the same shape and
closes with `AlgEquiv.commutes`, the `R`-algebra statement. The `A`-algebra statement is strictly
stronger and is what makes a morphism to `Spf A` exist at all — a general affine-charted datum has
no such morphism, because its charts have no common ambient algebra.

## Nothing here is specific to three charts

The index type `ULift (Fin 3)` is never used: no proof below case-splits on it, and none uses the
cardinality. The construction would lift verbatim to any `AffineChartedFibreDatumX` whose chart
algebras are completed localizations `A{1/f_i}` of one ambient `A` with `τ` fixing `A`. It is
*not* lifted, because the three-chart cover is the only such datum on the board and this tree has
repeatedly paid for generic layers with no second consumer. If a second one appears, the lift is
mechanical: replace `chartAlgebra`/`overlapElt`/`tau` by the datum's fields and carry an
`A`-algebra refinement of `τ_symm` as a hypothesis.

## `A` is not assumed adic (except where it must be)

`FormalSpectrum.locallyRingedSpaceObj` needs only a `CommRing` and an ideal, so `coverMap` is a
morphism of locally ringed spaces with no hypothesis on `A` — matching
`FormalSchemes.ThreeChartCoverCharts`, which deliberately does not require `A` to be adic (only the
charts `A{1/f_i}` are, for free). `xStructMap` is an LRS morphism for the same reason.

For `Spf A` to be a *formal scheme*, and hence for the cover map to be a morphism in
`FormalScheme`, `A` must be adic for `I·A`. That is the extra hypothesis carried by the final
section, and it is not restrictive where it matters: over a Noetherian base a topologically
finite type `A` is automatically a complete adic ring
(`IsTopologicallyFiniteType.isAdicRing_of_noetherian`), which is precisely the hypothesis under
which `FormalSchemes.ThreeChartCoverTopFiniteType` states its results.

## Main definitions and results

* `AlgebraicGeometry.ThreeChartCover.chartInclusion`: the chart inclusion `Spf(A{1/f_i}) ⟶ Spf A`.
* `AlgebraicGeometry.ThreeChartCover.chartInclusion_naturality`: the double-overlap square.
* `AlgebraicGeometry.ThreeChartCover.coverMap`: the glued morphism `gluedX ⟶ Spf A`.
* `AlgebraicGeometry.ThreeChartCover.ι_coverMap`: it restricts to `chartInclusion i` on each chart.
* `AlgebraicGeometry.ThreeChartCover.coverMap_comp_ambientStructMap`: it is a morphism over
  `Spf R`, i.e. composing with `Spf A ⟶ Spf R` gives back `xStructMap`.
* `AlgebraicGeometry.ThreeChartCover.coverHom`, `coverHom_comp_ambientStructHom`: the same two
  facts in the category of formal schemes, for adic `A`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.13, §10.15.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7, §9.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum
open CompletedTensorAwayInterchange

universe u

namespace AlgebraicGeometry

/-- Continuity of a composite ring homomorphism, in the `comap` spelling: the composite carries `I`
into `K` as soon as the two legs carry `I` into `J` and `J` into `K`. Needed to supply the combined
`hIK` when collapsing a composite `locallyRingedSpaceMap` via `locallyRingedSpaceMap_comp`.

This is the **fifth** private copy of this two-line helper on master: the others are
`le_comap_comp'` in `FormalSchemes.GeneralFibreProductExposeXStructMap` and in
`FormalSchemes.GeneralFibreProductBothCone`, `le_comap_comp''` in
`FormalSchemes.GeneralFibreProductBothProjectionLeft`, and `le_comap_comp'''` in
`FormalSchemes.GeneralFibreProductBothProjectionRight`. Each is `private`, so none can be reused,
and each new consumer of `locallyRingedSpaceMap_comp` adds one. Copying again rather than
de-duplicating keeps this branch purely additive; **consolidating all five into one public lemma in
an early module is a standing cleanup**, and it is now large enough to be worth filing. -/
private theorem le_comap_comp₃ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    {I : Ideal A} {J : Ideal B} {K : Ideal C} (φ : A →+* B) (ψ : B →+* C)
    (hIJ : I ≤ J.comap φ) (hJK : J ≤ K.comap ψ) : I ≤ K.comap (ψ.comp φ) :=
  fun _ hx => hJK (hIJ hx)

namespace ThreeChartCover

variable {R : Type u} [CommRing R] (I : Ideal R) [TopologicalSpace R] [IsAdicRing I]
variable {A : Type u} [CommRing A] [Algebra R A]
variable (f : ULift.{u} (Fin 3) → A)

/-! ### The chart inclusions and their overlap compatibility -/

/-- **The `i`-th chart inclusion** `Spf(A{1/f_i}) ⟶ Spf A`, the map of formal spectra induced by
the structural completion map `A → A{1/f_i}`, phrased at the datum's ideal convention
`I·(A{1/f_i}) = I.map (algebraMap R (A{1/f_i}))` on the source.

Staying in that convention rather than reusing `FormalSpectrum.basicOpenChart` — which presents the
same morphism at `awayCompletionIdeal (I·A) (f i)` — is deliberate: the datum's charts and its
`chartIsAdicRing` field are built at the `Ideal.map` spelling, and the two are equal but not
definitionally so (`idealOfDef_base_eq`). The `le_comap` witness is
`le_comap_awayCompletionHom_base`, which is already stated in the convention wanted here. -/
def chartInclusion (i : ULift.{u} (Fin 3)) :
    locallyRingedSpaceObj (I.map (algebraMap R (chartAlgebra I f i))) ⟶
      locallyRingedSpaceObj (I.map (algebraMap R A)) :=
  locallyRingedSpaceMap (I.map (algebraMap R A))
    (I.map (algebraMap R (chartAlgebra I f i)))
    (awayCompletionHom (I.map (algebraMap R A)) (f i))
    (le_comap_awayCompletionHom_base I (f i))

/-- **The double-overlap compatibility square of the chart inclusions**, the obligation
`glueMorphisms` consumes: restricting the `i`-th chart to its overlap with the `j`-th and then
including into `Spf A` agrees with crossing to the `j`-th chart-local presentation of that overlap
first.

Both sides collapse to a single `locallyRingedSpaceMap` out of `Spf(A{1/f_i}{1/g_ij})`, and the two
underlying ring homs `A → A{1/f_i}{1/g_ij}` agree by `tau_symm_algebraMap`: the transition fixes the
image of `A`. This is the one place where the cover map differs from
`AffineChartedFibreDatumX.xStructMap`, whose corresponding square only needs the transition to fix
the image of the base `R` (`AlgEquiv.commutes`). -/
theorem chartInclusion_naturality (hI : I.FG) (i j : ULift.{u} (Fin 3)) :
    basicOpenChart (I.map (algebraMap R (chartAlgebra I f i))) (overlapElt I f i j) ≫
        chartInclusion I f i =
      awayCompletionTransition (overlapElt I f i j) (overlapElt I f j i) (tau I f hI i j) ≫
        basicOpenChart (I.map (algebraMap R (chartAlgebra I f j))) (overlapElt I f j i) ≫
          chartInclusion I f j := by
  rw [chartInclusion, chartInclusion, basicOpenChart, basicOpenChart, awayCompletionTransition,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (hIK := le_comap_comp₃ (awayCompletionHom (I.map (algebraMap R A)) (f i))
        (awayCompletionHom (I.map (algebraMap R (chartAlgebra I f i))) (overlapElt I f i j))
        (le_comap_awayCompletionHom_base I (f i)) (le_comap_awayCompletionHom _ _)),
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (hIK := le_comap_comp₃ (awayCompletionHom (I.map (algebraMap R A)) (f j))
        (awayCompletionHom (I.map (algebraMap R (chartAlgebra I f j))) (overlapElt I f j i))
        (le_comap_awayCompletionHom_base I (f j)) (le_comap_awayCompletionHom _ _)),
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (hIK := le_comap_comp₃
        ((awayCompletionHom (I.map (algebraMap R (chartAlgebra I f j))) (overlapElt I f j i)).comp
          (awayCompletionHom (I.map (algebraMap R A)) (f j)))
        (tau I f hI i j).symm.toRingHom
        (le_comap_comp₃ (awayCompletionHom (I.map (algebraMap R A)) (f j))
          (awayCompletionHom (I.map (algebraMap R (chartAlgebra I f j))) (overlapElt I f j i))
          (le_comap_awayCompletionHom_base I (f j)) (le_comap_awayCompletionHom _ _))
        (awayCompletionTransition_le_comap (overlapElt I f i j) (overlapElt I f j i)
          (tau I f hI i j)))]
  refine FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _ ?_
  exact RingHom.ext fun a => (tau_symm_algebraMap I f hI i j a).symm

/-! ### The ambient affine and its structural morphism -/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The ambient affine's structural morphism** `Spf A ⟶ Spf R`. Named because both statements
below mention it; it is `Spf` of `algebraMap R A`, the same shape as
`AffineChartedFibreDatumX.xStructMapChart` one level up. -/
def ambientStructMap :
    locallyRingedSpaceObj (I.map (algebraMap R A)) ⟶ locallyRingedSpaceObj I :=
  locallyRingedSpaceMap I (I.map (algebraMap R A)) (algebraMap R A) Ideal.le_comap_map

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Each chart inclusion is a morphism over `Spf R`**: including the `i`-th chart into `Spf A` and
then mapping to `Spf R` is the chart's own structural morphism — which is
`(datumX I f B hI).xStructMapChart i` for the three-chart datum, by definitional unfolding of the
datum's chart algebras. The ring-level content is
`awayCompletionHom_comp_algebraMap_base : (A → A{1/f_i}) ∘ (R → A) = (R → A{1/f_i})`. -/
theorem chartInclusion_comp_ambientStructMap (i : ULift.{u} (Fin 3)) :
    chartInclusion I f i ≫ ambientStructMap I =
      locallyRingedSpaceMap I (I.map (algebraMap R (chartAlgebra I f i)))
        (algebraMap R (chartAlgebra I f i)) Ideal.le_comap_map := by
  rw [chartInclusion, ambientStructMap, ← FormalSpectrum.locallyRingedSpaceMap_comp
    (hIK := by rw [awayCompletionHom_comp_algebraMap_base]; exact Ideal.le_comap_map)]
  refine FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _ ?_
  exact awayCompletionHom_comp_algebraMap_base I (f i)

/-! ### The glued cover map -/

variable (B : Type u) [CommRing B] [Algebra R B]

/-- **The canonical morphism from the glued three-chart cover to its ambient affine**
`gluedX ⟶ Spf A`, assembled from the chart inclusions `Spf(A{1/f_i}) ⟶ Spf A` by
`FormalScheme.GlueData.glueMorphisms`. Off the diagonal the overlap obligation is
`chartInclusion_naturality`; on the diagonal it collapses through `GlueData.t_id`.

The `eqToHom` left over from `GlueData.ofGlueData'` after the `dif_neg` unfolding is cancelled with
`cancel_epi` rather than rewritten away. Restating the naturality square in the datum's own
`(datumX …).A i` / `.g i j` spelling so that `rw` matches syntactically is possible and costs about
five minutes of elaboration — the chart algebras here are completed localizations and writing their
`Ideal.map` spelling into a fresh `have` forces exactly the kernel work that
`FormalSchemes.ThreeChartCoverCharts`'s cost note warns about. Cancelling the epi instead never
elaborates a new type and the whole module builds in seconds. -/
def coverMap (hI : I.FG) :
    (datumX I f B hI).xGlued.toLocallyRingedSpace ⟶
      locallyRingedSpaceObj (I.map (algebraMap R A)) :=
  (datumX I f B hI).xFormalGlueData.glueMorphisms (fun i => chartInclusion I f i) (by
    intro i j
    by_cases hij : i = j
    · -- diagonal: `t i i = 𝟙`, so both sides collapse to the same composite.
      subst hij
      simp only [CategoryTheory.GlueData.t_id, Category.id_comp]
    · -- off-diagonal: unfold the `ofGlueData'` `if`-forms; the `dite` conditions are on `= : J`,
      -- so re-type the disequalities in `¬ Eq` form before rewriting.
      have hij' : ¬ @Eq (datumX I f B hI).J i j := hij
      have hji' : ¬ @Eq (datumX I f B hI).J j i := fun heq => hij heq.symm
      simp only [AffineChartedFibreDatumX.xFormalGlueData, AffineChartedFibreDatumX.xLrsGlueData,
        AffineChartedFibreDatumX.xGlueData', CategoryTheory.GlueData.ofGlueData',
        CategoryTheory.GlueData'.f', dif_neg hij', dif_neg hji', Category.assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      exact (cancel_epi _).mpr (chartInclusion_naturality I f hI i j))

/-- **The cover map restricts to the `i`-th chart inclusion** along each glue inclusion. -/
@[reassoc (attr := simp)]
theorem ι_coverMap (hI : I.FG) (i : ULift.{u} (Fin 3)) :
    (datumX I f B hI).xFormalGlueData.ι i ≫ coverMap I f B hI = chartInclusion I f i :=
  (datumX I f B hI).xFormalGlueData.ι_glueMorphisms _ _ i

/-- **The cover map is a morphism over `Spf R`**: composing `gluedX ⟶ Spf A` with `Spf A ⟶ Spf R`
recovers the datum's own structural morphism. Together with `ι_coverMap` this is what makes the
three-chart cover an object *over `Spf A`* over `Spf R`, which is the frame in which "`gluedX` is an
open formal subscheme of `Spf A`" is to be stated.

Proved by uniqueness of morphisms out of the canonical open cover of the glued object
(`FormalScheme.OpenCover.hom_ext`), reduced chartwise to `chartInclusion_comp_ambientStructMap`. The
final step cancels the cover map's isomorphism `epi`-wise instead of rewriting: `rw` fails there
with *"Did not find an occurrence of the pattern"* and a `Full error:` tail reporting the target is
not type-correct at `instances` transparency, because the open cover indexes by
`xFormalGlueData.openCover.J` while `ι` indexes by
`xFormalGlueData.toLocallyRingedSpaceGlueData.J`. Term-mode `(cancel_epi _).mpr` elaborates at
default transparency and the mismatch never arises — the same wall, and the same fix, that issue
858 recorded for `Category.id_comp`. -/
theorem coverMap_comp_ambientStructMap (hI : I.FG) :
    coverMap I f B hI ≫ ambientStructMap I = (datumX I f B hI).xStructMap := by
  refine ((datumX I f B hI).xFormalGlueData.openCover).hom_ext _ _ fun i => ?_
  have key : (datumX I f B hI).xFormalGlueData.ι i ≫ coverMap I f B hI ≫ ambientStructMap I =
      (datumX I f B hI).xFormalGlueData.ι i ≫ (datumX I f B hI).xStructMap := by
    rw [ι_coverMap_assoc, (datumX I f B hI).ι_xStructMap i]
    exact chartInclusion_comp_ambientStructMap I f i
  simp only [FormalScheme.GlueData.openCover, FormalScheme.Hom.toLRSHom, Category.assoc]
  exact (cancel_epi _).mpr key

/-! ### In the category of formal schemes, for adic `A` -/

section Adic

variable [TopologicalSpace A] [IsAdicRing (I.map (algebraMap R A))]

/-- **The ambient affine's structural morphism as a morphism of formal schemes** `Spf A ⟶ Spf R`,
available once `A` is a complete adic ring for `I·A` — the hypothesis under which `Spf A` is a
formal scheme at all. -/
def ambientStructHom : FormalScheme.Spf (I.map (algebraMap R A)) ⟶ FormalScheme.Spf I :=
  FormalScheme.Hom.mk (ambientStructMap I)

/-- **The cover map as a morphism of formal schemes** `gluedX ⟶ Spf A`. -/
def coverHom (hI : I.FG) : gluedX I f B hI ⟶ FormalScheme.Spf (I.map (algebraMap R A)) :=
  FormalScheme.Hom.mk (coverMap I f B hI)

/-- **`coverHom` is a morphism over `Spf R`**, the formal-scheme form of
`coverMap_comp_ambientStructMap`. Composition in `FormalScheme` is `Hom.mk` of the composition of
the underlying morphisms, so this is that identity under `Hom.ext'`. -/
theorem coverHom_comp_ambientStructHom (hI : I.FG) :
    coverHom I f B hI ≫ ambientStructHom I =
      FormalScheme.Hom.mk (datumX I f B hI).xStructMap :=
  FormalScheme.Hom.ext' (coverMap_comp_ambientStructMap I f B hI)

end Adic

end ThreeChartCover

end AlgebraicGeometry

end
