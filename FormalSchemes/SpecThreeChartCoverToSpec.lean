import FormalSchemes.ChartedSchemeDatumDesc
import FormalSchemes.SpecThreeChartCover

set_option linter.style.header false

/-!
# The three-chart cover is an open subscheme of `Spec A`, and is `Spec A` when the charts cover

`FormalSchemes.SpecThreeChartCover` assembles `Spec A` presented by three basic opens `D(f_i)` as a
`ChartedSchemeDatum`, and glues it to `SpecThreeChartCover.glued`. Identifying that `glued` with
`Spec A`, when `D(f₀) ∪ D(f₁) ∪ D(f₂) = Spec A`, takes exactly three things: the descent of the
chart inclusions `Spec A_{f_i} ⟶ Spec A` through the colimit, an open-immersion statement for the
resulting map, and surjectivity from `Ideal.span {f₀, f₁, f₂} = ⊤`.

This file supplies all three. The descent is
`AlgebraicGeometry.ChartedSchemeDatum.desc` (`FormalSchemes.ChartedSchemeDatumDesc`); what is done
here is its input and its two geometric consequences. That predecessor file used to list those
three under its own "What is *not* proved"; it now carries a forward pointer here instead, so
there is no quotation of it left in this docstring to fall out of step.

## The two inputs, and where the content is

**The compatibility** `toSpec_compat` is not about gluing at all: both sides are `Spec` of a ring
homomorphism `A ⟶ (A_{f_i})_{g_ij}`, and they agree because `tauAlg` is an `A`-algebra
isomorphism, so `τ⁻¹` fixes the image of `A`. That is `AlgEquiv.commutes`, and no fraction is
computed — the same reason `FormalSchemes.SpecThreeChartCover`'s own laws are short.

**The overlap condition** `range_specAwayMap_overlapElt_comp` is where the geometry sits: the two
charts meet in `Spec A` exactly along their glue overlap,
```
D(f_i) ∩ D(f_j) = range (specAwayMap (g_ij) ≫ specAwayMap (f_i)).
```
It is the basic-open identity `D(f_i) ∩ D(f_j) = D(f_i · f_j)` together with the fact that
`(A_{f_i})_{g_ij}` **is** `A` away from `f_i · f_j` (Mathlib's `IsLocalization.Away.mul'`), so the
composite chart inclusion has range `D(f_i · f_j)` on the nose. Without such a hypothesis the
open-immersion criterion is false — the line with two origins is the counterexample — so this is
the statement carrying the content, exactly as `ThreeChartCover.range_overlapChart_comp_chartToBase`
is on the completion side.

## Main definitions and results

* `AlgebraicGeometry.SpecThreeChartCover.toSpec`: the cover map `glued I f ⟶ Spec A`, with
  `specι_toSpec` its computation rule on each chart.
* `AlgebraicGeometry.SpecThreeChartCover.range_toSpec`: its range is `D(f₀) ∪ D(f₁) ∪ D(f₂)`.
* `AlgebraicGeometry.SpecThreeChartCover.isOpenImmersion_toSpec`: **it is an open immersion**, so
  `glued` is the open subscheme `D(f₀) ∪ D(f₁) ∪ D(f₂)` of `Spec A`.
* `AlgebraicGeometry.SpecThreeChartCover.isIso_toSpec` and
  `AlgebraicGeometry.SpecThreeChartCover.gluedIsoSpec`: when `Ideal.span (Set.range f) = ⊤` it is
  an isomorphism, so `glued I f ≅ Spec A`. This is the `Spec`-side twin of
  `AlgebraicGeometry.ThreeChartCover.gluedXIsoSpf`.
* `AlgebraicGeometry.SpecThreeChartCover.gluedIsoSpec_intCover`: the isomorphism exhibited at
  `Spec ℤ` covered by `D(2)`, `D(3)`, `D(5)` — so the capstone is not a statement about an empty
  cover.

## What is *not* proved

Nothing here is stated at `AlgebraicGeometry.Scheme`; see the scope note in
`FormalSchemes.SpecAwayOverlap`. Everything below is about `glued` as a locally ringed space,
isomorphic to `Spec A` under the covering hypothesis.

`glued` **is** a scheme, and that is proved one layer out rather than here:
`FormalSchemes.SpecThreeChartCoverScheme` promotes it to
`AlgebraicGeometry.SpecThreeChartCover.gluedScheme` and lifts `gluedIsoSpec` and
`gluedIsoSpec_intCover` to isomorphisms of schemes, giving
`AlgebraicGeometry.SpecThreeChartCover.isAffine_gluedScheme`. The lift is not a transport —
`Scheme.forgetToLocallyRingedSpace` is fully faithful, so `isIso_toSpec` below *is* the scheme
statement — which is why it costs no restatement of anything in this file.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace SpecThreeChartCover

variable {A : Type u} [CommRing A] (I : Ideal A) (f : ULift.{u} (Fin 3) → A)

/-! ### The overlap chart, as a chart of `Spec A` -/

/-- **The overlap chart of the `i`-th chart is the chart of `Spec A` at `f_i · f_j`**, as a ring
map: the structure map of `(A_{f_i})_{g_ij}` over `A` factors the two localization maps. -/
theorem algebraMap_overlapElt_comp (i j : ULift.{u} (Fin 3)) :
    (algebraMap (chartRing f i) (Localization.Away (overlapElt f i j))).comp
        (algebraMap A (chartRing f i)) =
      algebraMap A (Localization.Away (overlapElt f i j)) :=
  (IsScalarTower.algebraMap_eq A (chartRing f i) (Localization.Away (overlapElt f i j))).symm

/-- **The composite chart inclusion `Spec ((A_{f_i})_{g_ij}) ⟶ Spec A` is `Spec` of the structure
map.** -/
theorem specAwayMap_overlapElt_comp (i j : ULift.{u} (Fin 3)) :
    specAwayMap (overlapElt f i j) ≫ specAwayMap (f i) =
      Spec.locallyRingedSpaceMap
        (CommRingCat.ofHom (algebraMap A (Localization.Away (overlapElt f i j)))) := by
  rw [← Spec.locallyRingedSpaceMap_comp, ← CommRingCat.ofHom_comp,
    algebraMap_overlapElt_comp f i j]

/-- **The double overlap is `A` away from `f_i · f_j`**, so the composite chart inclusion has range
the basic open `D(f_i · f_j)`. -/
theorem range_specAwayMap_overlapElt_comp (i j : ULift.{u} (Fin 3)) :
    Set.range (specAwayMap (overlapElt f i j) ≫ specAwayMap (f i)).base =
      (PrimeSpectrum.basicOpen (f i * f j) : Set (PrimeSpectrum A)) := by
  rw [specAwayMap_overlapElt_comp f i j]
  exact PrimeSpectrum.localization_away_comap_range
    (Localization.Away (overlapElt f i j)) (f i * f j)

/-- **The two charts meet in `Spec A` exactly along their glue overlap.** This is the geometric
input of the open-immersion criterion, and it is `D(f_i) ∩ D(f_j) = D(f_i · f_j)` in disguise. -/
theorem range_specAwayMap_inter_eq (i j : ULift.{u} (Fin 3)) :
    Set.range (specAwayMap (f i)).base ∩ Set.range (specAwayMap (f j)).base =
      Set.range (specAwayMap (overlapElt f i j) ≫ specAwayMap (f i)).base := by
  rw [range_specAwayMap_inter, range_specAwayMap_overlapElt_comp f i j,
    range_specAwayMap (f i * f j)]

/-! ### The cover map -/

/-- **The compatibility of the three chart inclusions on the overlaps.** Both sides are `Spec` of a
ring homomorphism `A ⟶ (A_{f_i})_{g_ij}`; the transition `tauAlg` is an `A`-algebra isomorphism, so
its inverse fixes the image of `A` and the two ring maps agree. -/
theorem toSpec_compat (i j : ULift.{u} (Fin 3)) :
    specAwayMap (overlapElt f i j) ≫ specAwayMap (f i) =
      (specGlueIso (overlapElt f i j) (overlapElt f j i) (tauAlg f i j).toRingEquiv).hom ≫
        specAwayMap (overlapElt f j i) ≫ specAwayMap (f j) := by
  have hring : ((tauAlg f i j).toRingEquiv.symm.toRingHom).comp
      (algebraMap A (Localization.Away (overlapElt f j i))) =
      algebraMap A (Localization.Away (overlapElt f i j)) :=
    RingHom.ext fun a => (tauAlg f i j).symm.commutes a
  rw [specAwayMap_overlapElt_comp f i j, specAwayMap_overlapElt_comp f j i]
  change _ = Spec.locallyRingedSpaceMap _ ≫ Spec.locallyRingedSpaceMap _
  rw [← Spec.locallyRingedSpaceMap_comp, ← CommRingCat.ofHom_comp, hring]

/-- **The cover map `glued I f ⟶ Spec A`**, descended from the three affine chart inclusions
`Spec A_{f_i} ⟶ Spec A` through the colimit. -/
def toSpec : glued I f ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of A) :=
  (datum I f).desc (fun i => specAwayMap (f i)) fun i j _ => toSpec_compat f i j

@[reassoc (attr := simp)]
theorem specι_toSpec (i : ULift.{u} (Fin 3)) :
    (datum I f).specι i ≫ toSpec I f = specAwayMap (f i) :=
  (datum I f).specι_desc _ _ i

/-- **The range of the cover map is `D(f₀) ∪ D(f₁) ∪ D(f₂)`.** -/
theorem range_toSpec :
    Set.range (toSpec I f).base = ⋃ i, (PrimeSpectrum.basicOpen (f i) : Set (PrimeSpectrum A)) :=
  ((datum I f).range_desc _ _).trans (Set.iUnion_congr fun i => range_specAwayMap (f i))

/-- **The cover map is an open immersion**, so `glued I f` is the open subscheme
`D(f₀) ∪ D(f₁) ∪ D(f₂)` of `Spec A`. The charts are open immersions and they meet only along their
overlaps (`range_specAwayMap_inter_eq`); the general criterion supplies the rest. -/
theorem isOpenImmersion_toSpec : LocallyRingedSpace.IsOpenImmersion (toSpec I f) :=
  (datum I f).isOpenImmersion_desc _ _ (fun i => isOpenImmersion_specAwayMap (f i))
    fun i j _ => (range_specAwayMap_inter_eq f i j).le

/-! ### When the three basic opens cover -/

/-- **If the three basic opens cover `Spec A`, the cover map is an isomorphism.** -/
theorem isIso_toSpec (hcov : Ideal.span (Set.range f) = ⊤) : IsIso (toSpec I f) := by
  refine (datum I f).isIso_desc _ _ (fun i => isOpenImmersion_specAwayMap (f i))
    (fun i j _ => (range_specAwayMap_inter_eq f i j).le) ?_
  have htop : (⨆ i, PrimeSpectrum.basicOpen (f i)) = (⊤ : Opens (PrimeSpectrum A)) :=
    PrimeSpectrum.iSup_basicOpen_eq_top_iff.2 hcov
  have := congrArg (fun U : Opens (PrimeSpectrum A) => (U : Set (PrimeSpectrum A))) htop
  rw [Opens.coe_iSup, Opens.coe_top] at this
  refine Eq.trans (Set.iUnion_congr fun i => range_specAwayMap (f i)) this

/-- **If the three basic opens cover `Spec A`, then `glued I f ≅ Spec A`.** This is the `Spec`-side
twin of `AlgebraicGeometry.ThreeChartCover.gluedXIsoSpf`
(`FormalSchemes.ThreeChartCoverOpenImmersion`), and it is what makes the `ChartedSchemeDatum` line
load-bearing: until it exists, nothing says `specGlued` glues the right object. -/
def gluedIsoSpec (hcov : Ideal.span (Set.range f) = ⊤) :
    glued I f ≅ Spec.locallyRingedSpaceObj (CommRingCat.of A) :=
  letI := isIso_toSpec I f hcov
  asIso (toSpec I f)

@[simp]
theorem gluedIsoSpec_hom (hcov : Ideal.span (Set.range f) = ⊤) :
    (gluedIsoSpec I f hcov).hom = toSpec I f :=
  rfl

/-! ### Non-vacuity: `Spec ℤ` covered by `D(2)`, `D(3)`, `D(5)` -/

/-- **`2`, `3` and `5` generate the unit ideal of `ℤ`**, since `3 - 2 = 1`. -/
theorem span_range_intCover : Ideal.span (Set.range intCover) = ⊤ := by
  refine Ideal.eq_top_of_isUnit_mem _ (?_ : (1 : ℤ) ∈ _) isUnit_one
  have h2 : (2 : ℤ) ∈ Ideal.span (Set.range intCover) :=
    Ideal.subset_span ⟨⟨0⟩, rfl⟩
  have h3 : (3 : ℤ) ∈ Ideal.span (Set.range intCover) :=
    Ideal.subset_span ⟨⟨1⟩, rfl⟩
  simpa using Ideal.sub_mem _ h3 h2

/-- **The capstone, exhibited.** `Spec ℤ` glued from `D(2)`, `D(3)` and `D(5)` really is `Spec ℤ`:
the datum's triple-overlap field is evaluated at the inhabited triple `0, 1, 2`
(`datum_t'_zero_one_two`) over a non-empty double overlap (`intCover_overlap_nonempty`), so this is
not the isomorphism of an empty cover with an empty space. -/
def gluedIsoSpec_intCover (I : Ideal ℤ) :
    glued I intCover ≅ Spec.locallyRingedSpaceObj (CommRingCat.of ℤ) :=
  gluedIsoSpec I intCover span_range_intCover

end SpecThreeChartCover

end AlgebraicGeometry

end
