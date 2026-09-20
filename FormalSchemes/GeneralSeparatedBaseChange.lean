import FormalSchemes.GeneralSeparatedRange
import FormalSchemes.GeneralFibreProductBaseChange
import FormalSchemes.GeneralFibreProductExposeXIdealCongr
import FormalSchemes.GeneralFibreProductLiftUniqueAdic

set_option linter.style.header false
-- This file carries six per-declaration `set_option`s, three `maxHeartbeats 800000` and three
-- `backward.isDefEq.respectTransparency false`, on
-- `AlgebraicGeometry.BothChartedFibreDatumXY.baseChange_comp_pr₁`, on
-- `AlgebraicGeometry.BothChartedFibreDatumXY.baseChange_comp_pr₂` and on
-- `AlgebraicGeometry.BothChartedFibreDatumXY.diagonal'_comp_baseChange`; the measurement behind
-- them is commented at each. The line below is what keeps the style linter quiet about those six,
-- and it is named here so that disabling the linter is itself visible rather than silent.
set_option linter.style.setOption false

/-!
# Separatedness descends along the base change of the diagonal (EGA I §10.15)

`FormalSchemes.GeneralSeparatedRange` proves that separatedness of a datum-presented `X` over
`Spf R` is *exactly* closedness of one subset of one space:
`AlgebraicGeometry.BothChartedFibreDatumXY.isSeparated_iff_isClosed_range_diagonal_base`. The
diagonal is a section of the first projection
(`AlgebraicGeometry.BothChartedFibreDatumXY.diagonal'_comp_pr₁`), so both the stalk half and the
embedding half of the closed-immersion predicate are free and only the range is at issue.

This file draws the consequence for a **base change of the adic base**. If the same charts are read
over `(R, I)` and over `(R', I')`, the glued factor `X` is literally the same formal scheme
(`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr`), the two fibre products
are related by the glued comparison of `FormalSchemes.GeneralFibreProductBaseChange`, and
separatedness over the first base gives separatedness over the second. The triangle relating the
two diagonals to that comparison — the one thing the cancellation needs beyond injectivity — is
proved here and is no longer a hypothesis; it is the subject of the third step below. Neither are
the comparison's own two hypotheses, the overlap square and the overlap saturation: both are
theorems at the diagonal and are discharged here too. **So the implication below asks nothing at
all about the glue**, and what a caller supplies is only that the two sets of algebra data agree.

## The argument, in three steps

All three steps are re-derived here and none is taken from a summary.

1. **Separatedness is closedness of a range.** Quoted from the tree rather than from a description:
   `AlgebraicGeometry.BothChartedFibreDatumXY.isSeparated_iff_isClosed_range_diagonal_base` is an
   `Iff` between `AlgebraicGeometry.BothChartedFibreDatumXY.IsSeparated` and closedness of the
   range of the base map of
   `AlgebraicGeometry.BothChartedFibreDatumXY.schemeDiagonal'`.
   So there is **no stalk obligation anywhere in this file**, at either base.

2. **The cancellation is a preimage.** Write `Δ'` for the diagonal over `(R', I')`, `Δ` for the one
   over `(R, I)` and `ι` for the comparison, and suppose `Δ' ≫ ι = Δ` after the identification of
   the two sources. `AlgebraicGeometry.LocallyRingedSpace.range_base_eq_preimage_range_comp_base`
   says that for **injective** `ι` the range of `Δ'` is the `ι`-preimage of the range of `Δ' ≫ ι`;
   a preimage of a closed set under a continuous map is closed, and the base map of a morphism of
   locally ringed spaces is continuous by construction. **Injectivity is all that is asked of
   `ι`**, and `AlgebraicGeometry.DoubleChartGlue.injective_baseChange_base` supplies it for the
   glued base change against its two hypotheses — both of which are discharged here, so a caller
   of this file supplies neither.

3. **The triangle is a uniqueness argument, not a chartwise check.**
   `AlgebraicGeometry.BothChartedFibreDatumXY.diagonal'` is
   `AlgebraicGeometry.BothChartedFibreDatumXY.fibreLiftOf` of the identity pair over a refined
   chart family chosen by `Classical.choice`
   (`AlgebraicGeometry.BothChartedFibreDatumXY.adicDiagonalCharts`), so nothing about how it
   restricts to a chart of the glued source is available and no lemma of that shape can be
   written. What characterises it is its two projection triangles together with
   `AlgebraicGeometry.BothChartedFibreDatumXY.fibreLift_unique_adicOverBase`, and that is how
   `AlgebraicGeometry.BothChartedFibreDatumXY.diagonal'_comp_baseChange` is proved. The same-base
   precedent is `AlgebraicGeometry.BothChartedFibreDatumXY.diagonal'_transport`
   (`FormalSchemes.GeneralSeparatedPresentation`), which consumes
   `AlgebraicGeometry.BothChartedFibreDatumXY.compareIso_hom_comp_pr₁`; the two statements this
   file supplies in its place are
   `AlgebraicGeometry.BothChartedFibreDatumXY.baseChange_comp_pr₁` and
   `AlgebraicGeometry.BothChartedFibreDatumXY.baseChange_comp_pr₂`. Unlike the precedent, the two
   competing morphisms here do **not** share a source, and carrying that source equality is the
   one piece of plumbing the precedent does not supply.

## What the chartwise half costs, and the third statement it needs

The two projection squares are proved chartwise, and each chart square is one
`FormalSpectrum.locallyRingedSpaceMap_comp` merging the composite into a single map, one
`FormalSpectrum.locallyRingedSpaceMap_congr` at a ring identity, and one transport of the source
ideal. The ring identities are `CompletedTensorProduct.baseChangeHom_inl` and
`CompletedTensorProduct.baseChangeHom_inr`, both already on the tree; the two squares are
`AlgebraicGeometry.DoubleChartGlue.chartBaseChange_comp_inl` and
`AlgebraicGeometry.DoubleChartGlue.chartBaseChange_comp_inr`.

It is **not** enough. A chartwise argument also has to move the glue inclusions of the *target*
across the identification of the two glued factors, and nothing on the tree said that either:
`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr` identifies the two glued
`X`s and says nothing about their chart inclusions.
`AlgebraicGeometry.AffineChartedFibreDatumX.ι_xGluedOfIdeals_congr` is that statement, proved by
the same `subst` chain as the congruence it accompanies and finished by proof irrelevance.

One more thing is needed and it is not mathematics. A base change is stated at
`AlgebraicGeometry.DoubleChartGlue`, whose chart family is a parameter; a projection is stated at
`AlgebraicGeometry.BothChartedFibreDatumXY`, whose chart family is a field. The two glued objects
agree by `AlgebraicGeometry.BothChartedFibreDatum.generalFibreProduct_eq`, which is `rfl`, but at
a literal `AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData` pair that `rfl` is a defeq
check between two large terms, and it is what the raised heartbeat limits below pay for.
`AlgebraicGeometry.BothChartedFibreDatumXY.ι_carried_comp_pr₁` and
`AlgebraicGeometry.BothChartedFibreDatumXY.ι_carried_comp_pr₂` move the check to a datum that is a
variable wherever it can be moved; what is left is one such check per statement that composes the
two vocabularies, and there is no way to state those without one.

## Is the implication an `Iff`?

**No, and not for a bookkeeping reason.** The converse asks for closedness of
`Set.range ⇑Δ.base`, which is `⇑ι.base '' Set.range ⇑Δ'.base`, so it needs the image of a closed
set under `ι` to be closed — a *closed-map* property of the glued comparison, not an injectivity
one. `FormalSchemes.GeneralFibreProductBaseChange` records that this is unavailable: its chart legs
are closed immersions (`AlgebraicGeometry.DoubleChartGlue.chartBaseChange_eq_schemeBaseChange` and
`CompletedTensorProduct.schemeBaseChange_isClosedImmersion`), but the range of the glued morphism
is a union of chart images and closedness of such a union is a question about the target's glue
that neither of that morphism's hypotheses answers. So the `Iff` is not free, and the implication
is what is stated.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.range_base_eq_preimage_range_comp_base` and
  `AlgebraicGeometry.LocallyRingedSpace.isClosed_range_base_of_isClosed_range_comp`: **left
  cancellation of a range against an injective postcomposition**, and its consequence for
  closedness. Nothing about rings, ideals or formal schemes enters either.
* `AlgebraicGeometry.BothChartedFibreDatumXY.isSeparated_of_isSeparated_of_diagonal_factorization`:
  **the implication, with the comparison abstract** — any morphism of the two fibre products that
  is injective on points and receives the two diagonals.
* `AlgebraicGeometry.BothChartedFibreDatumXY.diagonalDoubleChartGlue` and
  `AlgebraicGeometry.BothChartedFibreDatumXY.xGlued_diagonalDatum_ofAlgebraData_congr`: the glue
  carried by the diagonal datum of a factor presented by algebra data, and the identification of
  the two glued factors that the theorem below needs as its source equality.
* `FormalSpectrum.locallyRingedSpaceMap_eq_comp_eqToHom` and
  `AlgebraicGeometry.AffineChartedFibreDatumX.ι_xGluedOfIdeals_congr`: **two transports**, one for
  the source ideal of a map of formal spectra and one for the chart inclusions of a glued `X`
  under a change of ideal family.
* `AlgebraicGeometry.BothChartedFibreDatumXY.ι_carried_comp_pr₁` and
  `AlgebraicGeometry.BothChartedFibreDatumXY.ι_carried_comp_pr₂`: **the two projections read
  against the carried glue**, `rfl` at a datum that is a variable and the bridge between the two
  vocabularies everything below is stated in.
* `AlgebraicGeometry.DoubleChartGlue.chartBaseChange_comp_inl` and
  `AlgebraicGeometry.DoubleChartGlue.chartBaseChange_comp_inr`: **the chart-level base change
  against the two chart projections**, whose content is two ring identities of
  `FormalSchemes.CompletedTensorBaseChange`.
* `AlgebraicGeometry.BothChartedFibreDatumXY.baseChange_comp_pr₁` and
  `AlgebraicGeometry.BothChartedFibreDatumXY.baseChange_comp_pr₂`: **the glued base change against
  the two projections**, the base-change analogue of
  `AlgebraicGeometry.BothChartedFibreDatumXY.compareIso_hom_comp_pr₁`.
* `AlgebraicGeometry.BothChartedFibreDatumXY.diagonal'_comp_baseChange`: **the triangle**, `Δ' ≫ ι
  = Δ` at the `AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData` pair.
* `AlgebraicGeometry.BothChartedFibreDatumXY.isChartTransitionBaseChange_diagonal`: **the
  transition agreement at the diagonal is the `HEq` of transitions a caller already holds**, since
  `AlgebraicGeometry.IsChartTransitionBaseChange` has one field per chart family and the diagonal
  supplies the same family twice.
* `AlgebraicGeometry.BothChartedFibreDatumXY.isBaseChangeOverlapCompatible_diagonalDoubleChartGlue`
  and
  `AlgebraicGeometry.BothChartedFibreDatumXY.isBaseChangeOverlapSaturated_diagonalDoubleChartGlue`:
  **the glued comparison's two hypotheses, discharged at the diagonal** — the square over the
  transition agreement, and the saturation over nothing at all.
* `AlgebraicGeometry.BothChartedFibreDatumXY.isSeparated_of_isSeparated_baseChange`: **the
  implication at the glued base change**, where the comparison is
  `AlgebraicGeometry.DoubleChartGlue.baseChange`, injectivity is discharged from its overlap
  square and its overlap saturation, and the triangle is discharged by
  `AlgebraicGeometry.BothChartedFibreDatumXY.diagonal'_comp_baseChange`. It has **no** triangle
  hypothesis, **no** square hypothesis and **no** saturation hypothesis: all three are theorems
  above, and what is left is `hK`, `hτ`, `hσ` — the two data agree — and the separatedness being
  descended.

The hypothesised form is kept only where the hypothesis is not the same statement:
`AlgebraicGeometry.BothChartedFibreDatumXY.isSeparated_of_isSeparated_of_diagonal_factorization`
asks for an *arbitrary* injective comparison receiving the two diagonals, and nothing here
discharges that for a comparison other than
`AlgebraicGeometry.DoubleChartGlue.baseChange`. Re-stating the specialisation below with the
triangle still hypothesised would be a second copy of one theorem, not a second theorem, so there
is no such variant.

## Placement

A leaf over `FormalSchemes.GeneralSeparatedRange`, `FormalSchemes.GeneralFibreProductBaseChange`,
`FormalSchemes.GeneralFibreProductExposeXIdealCongr` and
`FormalSchemes.GeneralFibreProductLiftUniqueAdic`: forward closure **185** project modules besides
itself (186 counted with itself), reverse closure **0**. None of the four imports is implied by
the others: each of them contributes modules that none of the other three reaches.

The fourth import is the uniqueness statement the triangle runs on, and it is the reason
everything above is here rather than in `FormalSchemes.GeneralFibreProductBaseChange`, which is
where a reader would look for a statement about
`AlgebraicGeometry.DoubleChartGlue.chartBaseChange`. The forward closure of
`FormalSchemes.GeneralFibreProductBaseChange` is **93**, and it contains neither
`FormalSchemes.GeneralFibreProductBothProjectionLeft`, which states
`AlgebraicGeometry.BothChartedFibreDatumXY.pr₁`, nor
`FormalSchemes.GeneralFibreProductLiftUniqueAdic`, which states the uniqueness — so the projection
squares cannot be written there without two new import edges, and the reverse closure of
`FormalSchemes.GeneralFibreProductBaseChange` is **3** against this file's **0**. Here the fourth
import adds only itself: `FormalSchemes.GeneralFibreProductLiftUniqueAdic` has forward closure
**143**, and every one of those modules was reached already.

The two locally-ringed-space lemmas are here and **not** in
`FormalSchemes.LocallyRingedSpaceRange`, which is this tree's home for range statements about base
maps, for two measured reasons. That module's subject, stated in its own title, is that an
`eqToHom` **prefix** is invisible to a base map — a fact about precomposition with an isomorphism,
whose proof is surjectivity of that isomorphism's base map. Left cancellation against an injective
**postcomposition** is the other side of a composite and shares no step with it. And
`FormalSchemes.LocallyRingedSpaceRange` has reverse closure **262**: putting a lemma with one
consumer there adds it to the environment of that many modules and re-elaborates all of them,
against this file's **0**. If a second consumer appears at a module this one cannot reach, the move
is cheap and that file is where it goes.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
* [The Stacks Project, Tag 01KJ](https://stacks.math.columbia.edu/tag/01KJ).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum Topology
open CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace FormalSpectrum

/-- **A `FormalSpectrum.locallyRingedSpaceMap` transports along an equality of its source ideal.**
The two maps have the same underlying ring homomorphism and the same target; only the ideal of the
*source* formal spectrum moves, and the transport is the `eqToHom` of that equality.

`FormalSpectrum.locallyRingedSpaceMap_congr` is the companion statement in the other argument —
same ideals, equal ring homomorphisms — and neither implies the other. -/
theorem locallyRingedSpaceMap_eq_comp_eqToHom {S T : Type u} [CommRing S] [CommRing T]
    {K L : Ideal S} (h : L = K) (M : Ideal T) (φ : S →+* T) (hK : K ≤ M.comap φ)
    (hL : L ≤ M.comap φ) :
    locallyRingedSpaceMap K M φ hK =
      locallyRingedSpaceMap L M φ hL ≫ eqToHom (congrArg locallyRingedSpaceObj h) := by
  subst h
  simp

end FormalSpectrum

namespace AlgebraicGeometry

namespace LocallyRingedSpace

/-- **A range cancels on the left against an injective postcomposition.** For `g : X ⟶ Y` and
`f : Y ⟶ Z` with `f` injective on points, the range of `g` is the `f`-preimage of the range of
`g ≫ f`.

The `⊆` holds for any `f`; injectivity is what gives `⊇`, and it is the only thing asked of `f`. -/
theorem range_base_eq_preimage_range_comp_base {X Y Z : LocallyRingedSpace.{u}}
    (g : X ⟶ Y) (f : Y ⟶ Z) (hf : Function.Injective ⇑f.base) :
    Set.range ⇑g.base = ⇑f.base ⁻¹' Set.range ⇑(g ≫ f).base := by
  have himg : Set.range ⇑(g ≫ f).base = ⇑f.base '' Set.range ⇑g.base := by
    rw [← Set.range_comp]
    refine congrArg Set.range ?_
    funext x
    rw [LocallyRingedSpace.comp_base]
    simp
  rw [himg, Set.preimage_image_eq _ hf]

/-- **Closedness of a range descends along an injective postcomposition.** The range of `g` is a
preimage of the range of `g ≫ f` by `range_base_eq_preimage_range_comp_base`, and the base map of a
morphism of locally ringed spaces is continuous, so a closed range upstairs gives a closed range
downstairs.

Continuity costs nothing here: the base map of a morphism of locally ringed spaces is itself a
morphism of topological spaces. -/
theorem isClosed_range_base_of_isClosed_range_comp {X Y Z : LocallyRingedSpace.{u}}
    (g : X ⟶ Y) (f : Y ⟶ Z) (hf : Function.Injective ⇑f.base)
    (h : IsClosed (Set.range ⇑(g ≫ f).base)) :
    IsClosed (Set.range ⇑g.base) := by
  rw [range_base_eq_preimage_range_comp_base g f hf]
  exact h.preimage f.base.hom.continuous

end LocallyRingedSpace

namespace AffineChartedFibreDatumX

/-! ### The chart inclusions of a glued `X` transport with its ideal family -/

section IdealCongr

variable {J : Type u} {A : J → Type u} [∀ i, CommRing (A i)]
variable [topology : ∀ i : J, TopologicalSpace (A i)] {g : ∀ (i : J), J → A i}

/-- **The chart inclusions transport along
`AlgebraicGeometry.AffineChartedFibreDatumX.xGluedOfIdeals_congr`.** That congruence identifies the
two glued formal schemes; this says the identification is compatible with the `i`-th chart
inclusion, the chart objects themselves being identified by the ideal family equation.

Without this, the congruence is unusable against anything built chartwise: a morphism out of the
glued `X` is determined by its restrictions, and the restrictions live over chart objects that the
congruence moves. The proof is the same `subst` chain as the congruence itself, finished by proof
irrelevance on the five `Prop`-valued arguments the two glue data do not share. -/
theorem ι_xGluedOfIdeals_congr {K K' : ∀ i : J, Ideal (A i)} (hK : K = K')
    {hKfg : ∀ i : J, (K i).FG} {hK'fg : ∀ i : J, (K' i).FG}
    [adic : ∀ i : J, IsAdicRing (K i)] [adic' : ∀ i : J, IsAdicRing (K' i)]
    {t : ∀ (i j : J), i ≠ j →
      (locallyRingedSpaceObj (awayCompletionIdeal (K i) (g i j)) ⟶
        locallyRingedSpaceObj (awayCompletionIdeal (K j) (g j i)))}
    {t_inv} {t'} {t_fac} {cocycle}
    {u : ∀ (i j : J), i ≠ j →
      (locallyRingedSpaceObj (awayCompletionIdeal (K' i) (g i j)) ⟶
        locallyRingedSpaceObj (awayCompletionIdeal (K' j) (g j i)))}
    {u_inv} {u'} {u_fac} {ucocycle}
    (ht : ∀ (i j : J) (h : i ≠ j), HEq (t i j h) (u i j h))
    (ht' : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      HEq (t' i j k hij hik hjk) (u' i j k hij hik hjk))
    (i : J) :
    (xFormalGlueDataOfIdeals g K hKfg t t_inv t' t_fac cocycle).ι i ≫
        eqToHom (congrArg FormalScheme.toLocallyRingedSpace
          (xGluedOfIdeals_congr hK ht ht')) =
      eqToHom (congrArg locallyRingedSpaceObj (congrFun hK i)) ≫
        (xFormalGlueDataOfIdeals g K' hK'fg u u_inv u' u_fac ucocycle).ι i := by
  subst hK
  have hteq : t = u := by
    funext i j h
    exact eq_of_heq (ht i j h)
  subst hteq
  have ht'eq : t' = u' := by
    funext i j k hij hik hjk
    exact eq_of_heq (ht' i j k hij hik hjk)
  subst ht'eq
  obtain rfl : hK'fg = hKfg := rfl
  obtain rfl : adic' = adic := rfl
  obtain rfl : u_inv = t_inv := rfl
  obtain rfl : u_fac = t_fac := rfl
  obtain rfl : ucocycle = cocycle := rfl
  exact Category.comp_id _

end IdealCongr

end AffineChartedFibreDatumX

namespace DoubleChartGlue

/-! ### The chart-level base change against the two chart projections -/

section ChartProjection

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {R' : Type u} [CommRing R'] [Algebra R R'] {I' : Ideal R'}
variable {JX JY : Type u} {A : JX → Type u} {B : JY → Type u}
variable [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] [∀ i, Algebra R' (A i)]
variable [∀ i, IsScalarTower R R' (A i)]
variable [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)] [∀ j, Algebra R' (B j)]
variable [∀ j, IsScalarTower R R' (B j)]

/-- **The chart comparison commutes with the first chart projection.** Both
`AlgebraicGeometry.DoubleChartGlue.chartBaseChange` and
`AlgebraicGeometry.BothChartedFibreDatumXY.pr₁ChartSelf` are
`FormalSpectrum.locallyRingedSpaceMap` — of `CompletedTensorProduct.baseChangeHom` and of
`CompletedTensorProduct.inl` respectively — so `FormalSpectrum.locallyRingedSpaceMap_comp` merges
the composite into one map and the whole content is the ring identity
`CompletedTensorProduct.baseChangeHom_inl`.

The `eqToHom` is the only thing the two sides do not share: the projections land in
`Spf (A_{p.1})` over *different* ideals of definition, `I'·A_{p.1}` and `I·A_{p.1}`, which the
caller's ideal-family hypothesis identifies. -/
theorem chartBaseChange_comp_inl (hI : I.FG) (hII' : I.map (algebraMap R R') = I')
    (p : JX × JY) (hKp : I'.map (algebraMap R' (A p.1)) = I.map (algebraMap R (A p.1))) :
    chartBaseChange (A := A) (B := B) hI hII' p ≫
        locallyRingedSpaceMap (I.map (algebraMap R (A p.1)))
          (CompletedTensorProduct.idealOfDefinition R I (A p.1) (B p.2))
          (CompletedTensorProduct.inl R I (A p.1) (B p.2)).toRingHom
          CompletedTensorProduct.inl_isAdicHom.le_comap =
      locallyRingedSpaceMap (I'.map (algebraMap R' (A p.1)))
          (CompletedTensorProduct.idealOfDefinition R' I' (A p.1) (B p.2))
          (CompletedTensorProduct.inl R' I' (A p.1) (B p.2)).toRingHom
          CompletedTensorProduct.inl_isAdicHom.le_comap ≫
        eqToHom (congrArg locallyRingedSpaceObj hKp) := by
  have hcomp : (CompletedTensorProduct.baseChangeHom (A := A p.1) (B := B p.2) hI hII').comp
      (CompletedTensorProduct.inl R I (A p.1) (B p.2)).toRingHom =
      (CompletedTensorProduct.inl R' I' (A p.1) (B p.2)).toRingHom :=
    RingHom.ext fun a => CompletedTensorProduct.baseChangeHom_inl hI hII' a
  have hle : I.map (algebraMap R (A p.1)) ≤
      (CompletedTensorProduct.idealOfDefinition R' I' (A p.1) (B p.2)).comap
        (CompletedTensorProduct.inl R' I' (A p.1) (B p.2)).toRingHom := by
    rw [← hKp]
    exact CompletedTensorProduct.inl_isAdicHom.le_comap
  have key : chartBaseChange (A := A) (B := B) hI hII' p ≫
      locallyRingedSpaceMap (I.map (algebraMap R (A p.1)))
        (CompletedTensorProduct.idealOfDefinition R I (A p.1) (B p.2))
        (CompletedTensorProduct.inl R I (A p.1) (B p.2)).toRingHom
        CompletedTensorProduct.inl_isAdicHom.le_comap =
      locallyRingedSpaceMap (I.map (algebraMap R (A p.1)))
        (CompletedTensorProduct.idealOfDefinition R' I' (A p.1) (B p.2))
        (CompletedTensorProduct.inl R' I' (A p.1) (B p.2)).toRingHom hle := by
    rw [chartBaseChange, ← locallyRingedSpaceMap_comp (hIK := by rw [hcomp]; exact hle)]
    exact locallyRingedSpaceMap_congr _ _ _ _ _ _ hcomp
  rw [key]
  exact locallyRingedSpaceMap_eq_comp_eqToHom hKp _ _ hle
    CompletedTensorProduct.inl_isAdicHom.le_comap

/-- **The chart comparison commutes with the second chart projection**, by the same computation as
`AlgebraicGeometry.DoubleChartGlue.chartBaseChange_comp_inl` on the other side of the tensor, over
`CompletedTensorProduct.baseChangeHom_inr`. -/
theorem chartBaseChange_comp_inr (hI : I.FG) (hII' : I.map (algebraMap R R') = I')
    (p : JX × JY) (hKp : I'.map (algebraMap R' (B p.2)) = I.map (algebraMap R (B p.2))) :
    chartBaseChange (A := A) (B := B) hI hII' p ≫
        locallyRingedSpaceMap (I.map (algebraMap R (B p.2)))
          (CompletedTensorProduct.idealOfDefinition R I (A p.1) (B p.2))
          (CompletedTensorProduct.inr R I (A p.1) (B p.2)).toRingHom
          CompletedTensorProduct.inr_isAdicHom.le_comap =
      locallyRingedSpaceMap (I'.map (algebraMap R' (B p.2)))
          (CompletedTensorProduct.idealOfDefinition R' I' (A p.1) (B p.2))
          (CompletedTensorProduct.inr R' I' (A p.1) (B p.2)).toRingHom
          CompletedTensorProduct.inr_isAdicHom.le_comap ≫
        eqToHom (congrArg locallyRingedSpaceObj hKp) := by
  have hcomp : (CompletedTensorProduct.baseChangeHom (A := A p.1) (B := B p.2) hI hII').comp
      (CompletedTensorProduct.inr R I (A p.1) (B p.2)).toRingHom =
      (CompletedTensorProduct.inr R' I' (A p.1) (B p.2)).toRingHom :=
    RingHom.ext fun a => CompletedTensorProduct.baseChangeHom_inr hI hII' a
  have hle : I.map (algebraMap R (B p.2)) ≤
      (CompletedTensorProduct.idealOfDefinition R' I' (A p.1) (B p.2)).comap
        (CompletedTensorProduct.inr R' I' (A p.1) (B p.2)).toRingHom := by
    rw [← hKp]
    exact CompletedTensorProduct.inr_isAdicHom.le_comap
  have key : chartBaseChange (A := A) (B := B) hI hII' p ≫
      locallyRingedSpaceMap (I.map (algebraMap R (B p.2)))
        (CompletedTensorProduct.idealOfDefinition R I (A p.1) (B p.2))
        (CompletedTensorProduct.inr R I (A p.1) (B p.2)).toRingHom
        CompletedTensorProduct.inr_isAdicHom.le_comap =
      locallyRingedSpaceMap (I.map (algebraMap R (B p.2)))
        (CompletedTensorProduct.idealOfDefinition R' I' (A p.1) (B p.2))
        (CompletedTensorProduct.inr R' I' (A p.1) (B p.2)).toRingHom hle := by
    rw [chartBaseChange, ← locallyRingedSpaceMap_comp (hIK := by rw [hcomp]; exact hle)]
    exact locallyRingedSpaceMap_congr _ _ _ _ _ _ hcomp
  rw [key]
  exact locallyRingedSpaceMap_eq_comp_eqToHom hKp _ _ hle
    CompletedTensorProduct.inr_isAdicHom.le_comap

end ChartProjection

end DoubleChartGlue


namespace BothChartedFibreDatumXY

/-! ### The projections read against the carried glue -/

section CarriedGlue

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable (D : BothChartedFibreDatumXY R I hI)

/-- **The first projection restricts to `pr₁ChartSelf p ≫ ι p.1` along each chart inclusion of the
*carried* glue.** This is `AlgebraicGeometry.BothChartedFibreDatumXY.ι_pr₁` with its glue inclusion
spelled in the `AlgebraicGeometry.DoubleChartGlue` vocabulary, and `rfl` is the whole difference:
`AlgebraicGeometry.BothChartedFibreDatum.generalFibreProduct_eq`.

It is stated separately because the identification is **not free at a concrete datum**. At a
literal `AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData` pair the two sides of that
`rfl` are large terms; here the datum is a variable, so the check is done on small ones and every
instantiation is free. Written inline at the concrete pair instead, the same `have` did not
elaborate inside the default heartbeat limit. -/
theorem ι_carried_comp_pr₁
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm)
    (p : D.JX × D.JY) :
    letI := D.commRingA
    letI := D.algebraA
    letI := D.commRingB
    letI := D.algebraB
    letI := D.topologyA
    letI := D.isAdicA
    (D.toBothChartedFibreDatum.toDoubleChartGlue.formalGlueData hI).ι p ≫ D.pr₁ hV hf ht =
      D.pr₁ChartSelf p ≫ D.xFormalGlueData.ι p.1 :=
  D.ι_pr₁ hV hf ht p

/-- **The second projection restricts to `pr₂ChartSelf p ≫ ι p.2` along each chart inclusion of the
carried glue**, the companion of
`AlgebraicGeometry.BothChartedFibreDatumXY.ι_carried_comp_pr₁`, `rfl` for the same reason and
stated at a variable datum for the same one. -/
theorem ι_carried_comp_pr₂
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm)
    (p : D.JX × D.JY) :
    letI := D.commRingA
    letI := D.algebraA
    letI := D.commRingB
    letI := D.algebraB
    letI := D.topologyB
    letI := D.isAdicB
    (D.toBothChartedFibreDatum.toDoubleChartGlue.formalGlueData hI).ι p ≫ D.pr₂ hV hf ht =
      D.pr₂ChartSelf p ≫ D.yFormalGlueData.ι p.2 :=
  D.ι_pr₂ hV hf ht p

end CarriedGlue

/-! ### The implication, with the comparison abstract -/

section Abstract

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable [TopologicalSpace R] [IsAdicRing I]
variable {BX : Type u} [CommRing BX] [Algebra R BX]
variable {R' : Type u} [CommRing R'] {I' : Ideal R'} {hI' : I'.FG}
variable [TopologicalSpace R'] [IsAdicRing I']
variable {BX' : Type u} [CommRing BX'] [Algebra R' BX']
variable (DX : AffineChartedFibreDatumX R I hI BX)
variable
  (σX : letI := DX.commRing; letI := DX.algebra;
    ∀ (i i' i'' : DX.J), i ≠ i' → i ≠ i'' → i' ≠ i'' →
    (awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i i' * DX.g i i'') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (DX.A i'))) (DX.g i' i'' * DX.g i' i)))
  (hστX : letI := DX.commRing; letI := DX.algebra;
    ∀ (i i' i'' : DX.J) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
    (σX i i' i'' h1 h2 h3).symm.toAlgHom.comp (furtherLocSnd I (DX.g i' i'') (DX.g i' i) hI) =
      (furtherLocFst I (DX.g i i') (DX.g i i'') hI).comp (DX.τ i i' h1).symm.toAlgHom)
  (hσcX : letI := DX.commRing; letI := DX.algebra;
    ∀ (i i' i'' : DX.J) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
    (σX i i' i'' h1 h2 h3).trans ((σX i' i'' i h3 h1.symm h2.symm).trans
      (σX i'' i i' h2.symm h3.symm h1)) =
      AlgEquiv.refl (R := R)
        (A₁ := awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i i' * DX.g i i'')))
variable (DX' : AffineChartedFibreDatumX R' I' hI' BX')
variable
  (σX' : letI := DX'.commRing; letI := DX'.algebra;
    ∀ (i i' i'' : DX'.J), i ≠ i' → i ≠ i'' → i' ≠ i'' →
    (awayCompletion (I'.map (algebraMap R' (DX'.A i))) (DX'.g i i' * DX'.g i i'') ≃ₐ[R']
      awayCompletion (I'.map (algebraMap R' (DX'.A i'))) (DX'.g i' i'' * DX'.g i' i)))
  (hστX' : letI := DX'.commRing; letI := DX'.algebra;
    ∀ (i i' i'' : DX'.J) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
    (σX' i i' i'' h1 h2 h3).symm.toAlgHom.comp (furtherLocSnd I' (DX'.g i' i'') (DX'.g i' i) hI') =
      (furtherLocFst I' (DX'.g i i') (DX'.g i i'') hI').comp (DX'.τ i i' h1).symm.toAlgHom)
  (hσcX' : letI := DX'.commRing; letI := DX'.algebra;
    ∀ (i i' i'' : DX'.J) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
    (σX' i i' i'' h1 h2 h3).trans ((σX' i' i'' i h3 h1.symm h2.symm).trans
      (σX' i'' i i' h2.symm h3.symm h1)) =
      AlgEquiv.refl (R := R')
        (A₁ := awayCompletion (I'.map (algebraMap R' (DX'.A i))) (DX'.g i i' * DX'.g i i'')))

/-- **Separatedness descends along a comparison of the two fibre products that receives the two
diagonals.** The two data present the *same* glued factor `X` — that is the source hypothesis, an
equality of locally ringed spaces and not merely an isomorphism — and `ι` compares the fibre
products over the two bases.

Only two things are asked of `ι`: that it be injective on points, and that the two diagonals be
related by it. Continuity is free, and closedness of `ι`'s own range is never used. The triangle
stays a hypothesis **here** because `ι` is arbitrary: it is a theorem for
`AlgebraicGeometry.DoubleChartGlue.baseChange`, by
`AlgebraicGeometry.BothChartedFibreDatumXY.diagonal'_comp_baseChange` below, and nothing discharges
it for any other comparison. See this file's *The argument, in three steps*, step 3. -/
theorem isSeparated_of_isSeparated_of_diagonal_factorization
    (hsrc : (diagonalDatum DX' σX' hστX' hσcX').xGlued.toLocallyRingedSpace =
      (diagonalDatum DX σX hστX hσcX).xGlued.toLocallyRingedSpace)
    (ι : (diagonalDatum DX' σX' hστX' hσcX').generalFibreProduct.toLocallyRingedSpace ⟶
      (diagonalDatum DX σX hστX hσcX).generalFibreProduct.toLocallyRingedSpace)
    (hinj : Function.Injective ⇑ι.base)
    (htri : diagonal' DX' σX' hστX' hσcX' ≫ ι = eqToHom hsrc ≫ diagonal' DX σX hστX hσcX)
    (hsep : IsSeparated DX σX hστX hσcX) :
    IsSeparated DX' σX' hστX' hσcX' := by
  rw [isSeparated_iff_isClosed_range_diagonal_base] at hsep ⊢
  refine LocallyRingedSpace.isClosed_range_base_of_isClosed_range_comp _ ι hinj ?_
  change IsClosed (Set.range ⇑(diagonal' DX' σX' hστX' hσcX' ≫ ι).base)
  rw [htri, LocallyRingedSpace.range_eqToHom_comp_base]
  exact hsep

end Abstract

/-! ### The diagonal glue of a factor presented by algebra data -/

section Glue

variable {R : Type u} [CommRing R] {I : Ideal R} (hI : I.FG)
variable [TopologicalSpace R] [IsAdicRing I]
variable {J : Type u} (A : J → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable (g : ∀ i : J, J → A i)
variable [∀ i : J, TopologicalSpace (A i)]
variable [∀ i : J, IsAdicRing (I.map (algebraMap R (A i)))]

/-- **The geometric glue of the diagonal fibre product** `X ×_{Spf I} X` of a factor presented by
algebra data, read at the fixed chart family `A` rather than at the datum's own.

`AlgebraicGeometry.BothChartedFibreDatum.generalFibreProduct_eq` says by `rfl` that the datum's
fibre product is this glue's glued object, and the point of the restatement is that
`AlgebraicGeometry.DoubleChartGlue` takes its chart family as a **parameter**: two data over
different bases share nothing a statement can quantify over until the family is one. -/
abbrev diagonalDoubleChartGlue
    (τ : ∀ (i j : J), i ≠ j →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j i)))
    (τ_symm : ∀ (i j : J) (h : i ≠ j), τ j i h.symm = (τ i j h).symm)
    (σ : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j k * g j i)))
    (hστ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ i j k hij hik hjk).symm.toAlgHom.comp (furtherLocSnd I (g j k) (g j i) hI) =
        (furtherLocFst I (g i j) (g i k) hI).comp (τ i j hij).symm.toAlgHom)
    (hσc : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ i j k hij hik hjk).trans ((σ j k i hjk hij.symm hik.symm).trans
        (σ k i j hik.symm hjk.symm hij)) =
        AlgEquiv.refl (R := R)
          (A₁ := awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k)))
    (BX : Type u) [CommRing BX] [Algebra R BX] :
    DoubleChartGlue R I A A :=
  (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX) hI A g τ τ_symm σ hστ hσc)
    σ hστ hσc).toBothChartedFibreDatum.toDoubleChartGlue

end Glue

/-! ### The implication at the glued base change -/

section OfAlgebraData

variable {R : Type u} [CommRing R] {I : Ideal R} (hI : I.FG)
variable [TopologicalSpace R] [IsAdicRing I]
variable {R' : Type u} [CommRing R'] [Algebra R R'] {I' : Ideal R'} (hI' : I'.FG)
variable [TopologicalSpace R'] [IsAdicRing I']
variable {J : Type u} (A : J → Type u) [∀ i, CommRing (A i)]
variable [∀ i, Algebra R (A i)] [∀ i, Algebra R' (A i)] [∀ i, IsScalarTower R R' (A i)]
variable (g : ∀ i : J, J → A i)
variable [∀ i : J, TopologicalSpace (A i)]
variable [∀ i : J, IsAdicRing (I.map (algebraMap R (A i)))]
variable [∀ i : J, IsAdicRing (I'.map (algebraMap R' (A i)))]
variable
  (τ : ∀ (i j : J), i ≠ j →
    (awayCompletion (I.map (algebraMap R (A i))) (g i j) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (A j))) (g j i)))
  (τ_symm : ∀ (i j : J) (h : i ≠ j), τ j i h.symm = (τ i j h).symm)
  (σ : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
    (awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (A j))) (g j k * g j i)))
  (hστ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
    (σ i j k hij hik hjk).symm.toAlgHom.comp (furtherLocSnd I (g j k) (g j i) hI) =
      (furtherLocFst I (g i j) (g i k) hI).comp (τ i j hij).symm.toAlgHom)
  (hσc : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
    (σ i j k hij hik hjk).trans ((σ j k i hjk hij.symm hik.symm).trans
      (σ k i j hik.symm hjk.symm hij)) =
      AlgEquiv.refl (R := R)
        (A₁ := awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k)))
  (τ' : ∀ (i j : J), i ≠ j →
    (awayCompletion (I'.map (algebraMap R' (A i))) (g i j) ≃ₐ[R']
      awayCompletion (I'.map (algebraMap R' (A j))) (g j i)))
  (τ'_symm : ∀ (i j : J) (h : i ≠ j), τ' j i h.symm = (τ' i j h).symm)
  (σ' : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
    (awayCompletion (I'.map (algebraMap R' (A i))) (g i j * g i k) ≃ₐ[R']
      awayCompletion (I'.map (algebraMap R' (A j))) (g j k * g j i)))
  (hστ' : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
    (σ' i j k hij hik hjk).symm.toAlgHom.comp (furtherLocSnd I' (g j k) (g j i) hI') =
      (furtherLocFst I' (g i j) (g i k) hI').comp (τ' i j hij).symm.toAlgHom)
  (hσc' : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
    (σ' i j k hij hik hjk).trans ((σ' j k i hjk hij.symm hik.symm).trans
      (σ' k i j hik.symm hjk.symm hij)) =
      AlgEquiv.refl (R := R')
        (A₁ := awayCompletion (I'.map (algebraMap R' (A i))) (g i j * g i k)))
variable {BX : Type u} [CommRing BX] [Algebra R BX]
variable {BX' : Type u} [CommRing BX'] [Algebra R' BX']

omit [TopologicalSpace R] [IsAdicRing I] [Algebra R R'] [∀ i, IsScalarTower R R' (A i)]
  [TopologicalSpace R'] [IsAdicRing I'] in
/-- **The two diagonal data present the same glued factor.** This is
`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr` read at the diagonal datum,
whose exposed factor is definitionally the factor it was built from, and pushed onto underlying
locally ringed spaces.

The three inputs are the ones that file asks for: the two induced ideal families agree, and the
single- and double-overlap transitions agree *as functions*. Nothing else about the two bases is
used. -/
theorem xGlued_diagonalDatum_ofAlgebraData_congr
    (hK : (fun i => I'.map (algebraMap R' (A i))) = fun i => I.map (algebraMap R (A i)))
    (hτ : ∀ (i j : J) (h : i ≠ j), HEq (⇑(τ' i j h)) (⇑(τ i j h)))
    (hσ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      HEq (⇑(σ' i j k hij hik hjk)) (⇑(σ i j k hij hik hjk))) :
    (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX') hI' A g τ' τ'_symm σ'
        hστ' hσc') σ' hστ' hσc').xGlued.toLocallyRingedSpace =
      (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX) hI A g τ τ_symm σ hστ hσc)
        σ hστ hσc).xGlued.toLocallyRingedSpace :=
  congrArg FormalScheme.toLocallyRingedSpace
    (AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr (B := BX) (B' := BX') hI hI' A g
      τ τ_symm σ hστ hσc τ' τ'_symm σ' hστ' hσc' hK hτ hσ)

omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace R'] [IsAdicRing I'] in
set_option maxHeartbeats 800000 in
-- A raised limit, and the measurement behind it. The statements below compose a morphism written
-- at `AlgebraicGeometry.DoubleChartGlue` with one written at
-- `AlgebraicGeometry.BothChartedFibreDatumXY`; the two objects agree by
-- `AlgebraicGeometry.BothChartedFibreDatum.generalFibreProduct_eq`, which is `rfl`, but at a
-- literal `AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData` pair the two sides of that
-- `rfl` are large terms and the defeq check that bridges them is what runs out. All three fail at
-- the default 200000; the two projection squares pass at 400000 and the triangle at 800000, so the
-- bound is set uniformly at 800000. The route that would remove it is to ascribe the comparison
-- once, in a `def` whose type is written in the datum vocabulary, and state everything against
-- that; it is a separate change and is not attempted here.
set_option backward.isDefEq.respectTransparency false in
/-- **The glued base change commutes with the first projection.** At one chart family `A`, one away
family `g` and two adic bases whose induced ideal families agree, the comparison
`AlgebraicGeometry.DoubleChartGlue.baseChange` followed by the first projection of the `(R, I)`
fibre product is the first projection of the `(R', I')` one followed by the identification of the
two glued factors.

This is the base-change analogue of
`AlgebraicGeometry.BothChartedFibreDatumXY.compareIso_hom_comp_pr₁`, and it is what the triangle
below runs on. The proof is chartwise — `AlgebraicGeometry.FormalScheme.GlueData.hom_ext` on the
*source* glue — and each chart square is
`AlgebraicGeometry.DoubleChartGlue.chartBaseChange_comp_inl` against
`AlgebraicGeometry.AffineChartedFibreDatumX.ι_xGluedOfIdeals_congr`, the first for the chart
objects and the second for the glue inclusions of the target.

The chart index is bound at `J × J` rather than at the glue datum's own index type: unfolding that
type is what the `instances` transparency level will not do, and every `rw` below needs it. -/
theorem baseChange_comp_pr₁ (hII' : I.map (algebraMap R R') = I')
    (hK : (fun i => I'.map (algebraMap R' (A i))) = fun i => I.map (algebraMap R (A i)))
    (hτ : ∀ (i j : J) (h : i ≠ j), HEq (⇑(τ' i j h)) (⇑(τ i j h)))
    (hσ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      HEq (⇑(σ' i j k hij hik hjk)) (⇑(σ i j k hij hik hjk)))
    (hsq : DoubleChartGlue.IsBaseChangeOverlapCompatible
      (diagonalDoubleChartGlue hI' A g τ' τ'_symm σ' hστ' hσc' BX')
      (diagonalDoubleChartGlue hI A g τ τ_symm σ hστ hσc BX) hI hII') :
    (diagonalDoubleChartGlue hI' A g τ' τ'_symm σ' hστ' hσc' BX').baseChange
        (diagonalDoubleChartGlue hI A g τ τ_symm σ hστ hσc BX) hI' hI hII' hsq ≫
      (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX) hI A g τ τ_symm σ hστ hσc)
        σ hστ hσc).pr₁ (ofFactors_hV _ _ _ _ _ _ _ _) (ofFactors_hf _ _ _ _ _ _ _ _)
        (ofFactors_ht _ _ _ _ _ _ _ _) =
      (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX') hI' A g τ' τ'_symm σ'
        hστ' hσc') σ' hστ' hσc').pr₁ (ofFactors_hV _ _ _ _ _ _ _ _)
        (ofFactors_hf _ _ _ _ _ _ _ _) (ofFactors_ht _ _ _ _ _ _ _ _) ≫
      eqToHom (xGlued_diagonalDatum_ofAlgebraData_congr hI hI' A g τ τ_symm σ hστ hσc τ' τ'_symm
        σ' hστ' hσc' (BX := BX) (BX' := BX') hK hτ hσ) := by
  letI := (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX) hI A g τ τ_symm σ hστ
    hσc) σ hστ hσc).commRingA
  letI := (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX) hI A g τ τ_symm σ hστ
    hσc) σ hστ hσc).algebraA
  letI := (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX') hI' A g τ' τ'_symm σ'
    hστ' hσc') σ' hστ' hσc').commRingA
  letI := (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX') hI' A g τ' τ'_symm σ'
    hστ' hσc') σ' hστ' hσc').algebraA
  refine ((diagonalDoubleChartGlue hI' A g τ' τ'_symm σ' hστ' hσc' BX').formalGlueData
    hI').hom_ext (fun p : J × J => ?_)
  rw [DoubleChartGlue.ι_baseChange_assoc,
    (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX) hI A g τ τ_symm σ hστ hσc)
      σ hστ hσc).ι_carried_comp_pr₁ (ofFactors_hV _ _ _ _ _ _ _ _)
      (ofFactors_hf _ _ _ _ _ _ _ _) (ofFactors_ht _ _ _ _ _ _ _ _) p]
  conv_rhs =>
    rw [← Category.assoc,
      (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX') hI' A g τ' τ'_symm σ'
        hστ' hσc') σ' hστ' hσc').ι_carried_comp_pr₁ (ofFactors_hV _ _ _ _ _ _ _ _)
        (ofFactors_hf _ _ _ _ _ _ _ _) (ofFactors_ht _ _ _ _ _ _ _ _) p, Category.assoc]
  have hchart : DoubleChartGlue.chartBaseChange (A := A) (B := A) hI hII' p ≫
      (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX) hI A g τ τ_symm σ hστ hσc)
        σ hστ hσc).pr₁ChartSelf p =
      (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX') hI' A g τ' τ'_symm σ'
        hστ' hσc') σ' hστ' hσc').pr₁ChartSelf p ≫
      eqToHom (congrArg locallyRingedSpaceObj (congrFun hK p.1)) :=
    DoubleChartGlue.chartBaseChange_comp_inl hI hII' p (congrFun hK p.1)
  have hxι : (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX') hI' A g τ' τ'_symm
        σ' hστ' hσc') σ' hστ' hσc').xFormalGlueData.ι p.1 ≫
      eqToHom (xGlued_diagonalDatum_ofAlgebraData_congr hI hI' A g τ τ_symm σ hστ hσc τ' τ'_symm
        σ' hστ' hσc' (BX := BX) (BX' := BX') hK hτ hσ) =
      eqToHom (congrArg locallyRingedSpaceObj (congrFun hK p.1)) ≫
      (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX) hI A g τ τ_symm σ hστ hσc)
        σ hστ hσc).xFormalGlueData.ι p.1 :=
    AffineChartedFibreDatumX.ι_xGluedOfIdeals_congr (hKfg := fun _ => hI'.map _)
      (hK'fg := fun _ => hI.map _) hK
      (AffineChartedFibreDatumX.awayCompletionTransition_heq A g hK hτ)
      (AffineChartedFibreDatumX.xAlgDataT'_heq hI hI' A g hK hσ) p.1
  rw [← Category.assoc, hchart, Category.assoc, hxι]

omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace R'] [IsAdicRing I'] in
set_option maxHeartbeats 800000 in
-- A raised limit, and the measurement behind it. The statements below compose a morphism written
-- at `AlgebraicGeometry.DoubleChartGlue` with one written at
-- `AlgebraicGeometry.BothChartedFibreDatumXY`; the two objects agree by
-- `AlgebraicGeometry.BothChartedFibreDatum.generalFibreProduct_eq`, which is `rfl`, but at a
-- literal `AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData` pair the two sides of that
-- `rfl` are large terms and the defeq check that bridges them is what runs out. All three fail at
-- the default 200000; the two projection squares pass at 400000 and the triangle at 800000, so the
-- bound is set uniformly at 800000. The route that would remove it is to ascribe the comparison
-- once, in a `def` whose type is written in the datum vocabulary, and state everything against
-- that; it is a separate change and is not attempted here.
set_option backward.isDefEq.respectTransparency false in
/-- **The glued base change commutes with the second projection**, by the same chartwise argument
as `AlgebraicGeometry.BothChartedFibreDatumXY.baseChange_comp_pr₁` on the other side of the tensor,
over `AlgebraicGeometry.DoubleChartGlue.chartBaseChange_comp_inr`.

The target is the *exposed second* factor, which for a diagonal datum is the same glued `X`, so the
identification on the right is the same one. -/
theorem baseChange_comp_pr₂ (hII' : I.map (algebraMap R R') = I')
    (hK : (fun i => I'.map (algebraMap R' (A i))) = fun i => I.map (algebraMap R (A i)))
    (hτ : ∀ (i j : J) (h : i ≠ j), HEq (⇑(τ' i j h)) (⇑(τ i j h)))
    (hσ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      HEq (⇑(σ' i j k hij hik hjk)) (⇑(σ i j k hij hik hjk)))
    (hsq : DoubleChartGlue.IsBaseChangeOverlapCompatible
      (diagonalDoubleChartGlue hI' A g τ' τ'_symm σ' hστ' hσc' BX')
      (diagonalDoubleChartGlue hI A g τ τ_symm σ hστ hσc BX) hI hII') :
    (diagonalDoubleChartGlue hI' A g τ' τ'_symm σ' hστ' hσc' BX').baseChange
        (diagonalDoubleChartGlue hI A g τ τ_symm σ hστ hσc BX) hI' hI hII' hsq ≫
      (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX) hI A g τ τ_symm σ hστ hσc)
        σ hστ hσc).pr₂ (ofFactors_hV _ _ _ _ _ _ _ _) (ofFactors_hf _ _ _ _ _ _ _ _)
        (ofFactors_ht _ _ _ _ _ _ _ _) =
      (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX') hI' A g τ' τ'_symm σ'
        hστ' hσc') σ' hστ' hσc').pr₂ (ofFactors_hV _ _ _ _ _ _ _ _)
        (ofFactors_hf _ _ _ _ _ _ _ _) (ofFactors_ht _ _ _ _ _ _ _ _) ≫
      eqToHom (xGlued_diagonalDatum_ofAlgebraData_congr hI hI' A g τ τ_symm σ hστ hσc τ' τ'_symm
        σ' hστ' hσc' (BX := BX) (BX' := BX') hK hτ hσ) := by
  letI := (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX) hI A g τ τ_symm σ hστ
    hσc) σ hστ hσc).commRingB
  letI := (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX) hI A g τ τ_symm σ hστ
    hσc) σ hστ hσc).algebraB
  letI := (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX') hI' A g τ' τ'_symm σ'
    hστ' hσc') σ' hστ' hσc').commRingB
  letI := (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX') hI' A g τ' τ'_symm σ'
    hστ' hσc') σ' hστ' hσc').algebraB
  refine ((diagonalDoubleChartGlue hI' A g τ' τ'_symm σ' hστ' hσc' BX').formalGlueData
    hI').hom_ext (fun p : J × J => ?_)
  rw [DoubleChartGlue.ι_baseChange_assoc,
    (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX) hI A g τ τ_symm σ hστ hσc)
      σ hστ hσc).ι_carried_comp_pr₂ (ofFactors_hV _ _ _ _ _ _ _ _)
      (ofFactors_hf _ _ _ _ _ _ _ _) (ofFactors_ht _ _ _ _ _ _ _ _) p]
  conv_rhs =>
    rw [← Category.assoc,
      (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX') hI' A g τ' τ'_symm σ'
        hστ' hσc') σ' hστ' hσc').ι_carried_comp_pr₂ (ofFactors_hV _ _ _ _ _ _ _ _)
        (ofFactors_hf _ _ _ _ _ _ _ _) (ofFactors_ht _ _ _ _ _ _ _ _) p, Category.assoc]
  have hchart : DoubleChartGlue.chartBaseChange (A := A) (B := A) hI hII' p ≫
      (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX) hI A g τ τ_symm σ hστ hσc)
        σ hστ hσc).pr₂ChartSelf p =
      (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX') hI' A g τ' τ'_symm σ'
        hστ' hσc') σ' hστ' hσc').pr₂ChartSelf p ≫
      eqToHom (congrArg locallyRingedSpaceObj (congrFun hK p.2)) :=
    DoubleChartGlue.chartBaseChange_comp_inr hI hII' p (congrFun hK p.2)
  have hxι : (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX') hI' A g τ' τ'_symm
        σ' hστ' hσc') σ' hστ' hσc').yFormalGlueData.ι p.2 ≫
      eqToHom (xGlued_diagonalDatum_ofAlgebraData_congr hI hI' A g τ τ_symm σ hστ hσc τ' τ'_symm
        σ' hστ' hσc' (BX := BX) (BX' := BX') hK hτ hσ) =
      eqToHom (congrArg locallyRingedSpaceObj (congrFun hK p.2)) ≫
      (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX) hI A g τ τ_symm σ hστ hσc)
        σ hστ hσc).yFormalGlueData.ι p.2 :=
    AffineChartedFibreDatumX.ι_xGluedOfIdeals_congr (hKfg := fun _ => hI'.map _)
      (hK'fg := fun _ => hI.map _) hK
      (AffineChartedFibreDatumX.awayCompletionTransition_heq A g hK hτ)
      (AffineChartedFibreDatumX.xAlgDataT'_heq hI hI' A g hK hσ) p.2
  rw [← Category.assoc, hchart, Category.assoc, hxι]

set_option maxHeartbeats 800000 in
-- A raised limit, and the measurement behind it. The statements below compose a morphism written
-- at `AlgebraicGeometry.DoubleChartGlue` with one written at
-- `AlgebraicGeometry.BothChartedFibreDatumXY`; the two objects agree by
-- `AlgebraicGeometry.BothChartedFibreDatum.generalFibreProduct_eq`, which is `rfl`, but at a
-- literal `AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData` pair the two sides of that
-- `rfl` are large terms and the defeq check that bridges them is what runs out. All three fail at
-- the default 200000; the two projection squares pass at 400000 and the triangle at 800000, so the
-- bound is set uniformly at 800000. The route that would remove it is to ascribe the comparison
-- once, in a `def` whose type is written in the datum vocabulary, and state everything against
-- that; it is a separate change and is not attempted here.
set_option backward.isDefEq.respectTransparency false in
/-- **The two diagonals are related by the glued base change.** The triangle `Δ' ≫ ι = Δ` at the
`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData` pair, with `ι` the glued base change and
the two sources identified by
`AlgebraicGeometry.BothChartedFibreDatumXY.xGlued_diagonalDatum_ofAlgebraData_congr`.

**It cannot be checked chartwise, and that is an absence of the object rather than a difficulty.**
`AlgebraicGeometry.BothChartedFibreDatumXY.diagonal'` is
`AlgebraicGeometry.BothChartedFibreDatumXY.fibreLiftOf` of the identity pair over
`AlgebraicGeometry.BothChartedFibreDatumXY.adicDiagonalCharts`, a refined chart family produced by
`Classical.choice`, so there is no lemma describing its restriction to a chart of the glued source
and no way to state one. What characterises it is its two projection triangles together with
`AlgebraicGeometry.BothChartedFibreDatumXY.fibreLift_unique_adicOverBase`, and that is how this is
proved — at the `(R, I)`-side datum, against
`AlgebraicGeometry.BothChartedFibreDatumXY.baseChange_comp_pr₁` and
`AlgebraicGeometry.BothChartedFibreDatumXY.baseChange_comp_pr₂`.

`AlgebraicGeometry.BothChartedFibreDatumXY.diagonal'_transport`
(`FormalSchemes.GeneralSeparatedPresentation`) is the same-base precedent and has the same shape.
It needs no transport, because its two competing morphisms share a source; these do not, and
carrying the source equality is the one piece of plumbing that precedent does not supply. The
uniqueness is therefore applied to `eqToHom hsrc.symm ≫ Δ' ≫ ι` against `Δ`, both out of the
`(R, I)`-side glued factor, and the stated form is recovered by cancelling the transport. -/
theorem diagonal'_comp_baseChange (hII' : I.map (algebraMap R R') = I')
    (hK : (fun i => I'.map (algebraMap R' (A i))) = fun i => I.map (algebraMap R (A i)))
    (hτ : ∀ (i j : J) (h : i ≠ j), HEq (⇑(τ' i j h)) (⇑(τ i j h)))
    (hσ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      HEq (⇑(σ' i j k hij hik hjk)) (⇑(σ i j k hij hik hjk)))
    (hsq : DoubleChartGlue.IsBaseChangeOverlapCompatible
      (diagonalDoubleChartGlue hI' A g τ' τ'_symm σ' hστ' hσc' BX')
      (diagonalDoubleChartGlue hI A g τ τ_symm σ hστ hσc BX) hI hII') :
    diagonal' (AffineChartedFibreDatumX.ofAlgebraData (B := BX') hI' A g τ' τ'_symm σ' hστ' hσc')
        σ' hστ' hσc' ≫
      (diagonalDoubleChartGlue hI' A g τ' τ'_symm σ' hστ' hσc' BX').baseChange
        (diagonalDoubleChartGlue hI A g τ τ_symm σ hστ hσc BX) hI' hI hII' hsq =
      eqToHom (xGlued_diagonalDatum_ofAlgebraData_congr hI hI' A g τ τ_symm σ hστ hσc τ' τ'_symm
        σ' hστ' hσc' (BX := BX) (BX' := BX') hK hτ hσ) ≫
      diagonal' (AffineChartedFibreDatumX.ofAlgebraData (B := BX) hI A g τ τ_symm σ hστ hσc)
        σ hστ hσc := by
  have hsrc : (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX') hI' A g τ' τ'_symm
        σ' hστ' hσc') σ' hστ' hσc').xGlued.toLocallyRingedSpace =
      (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX) hI A g τ τ_symm σ hστ hσc)
        σ hστ hσc).xGlued.toLocallyRingedSpace :=
    xGlued_diagonalDatum_ofAlgebraData_congr hI hI' A g τ τ_symm σ hστ hσc τ' τ'_symm σ' hστ'
      hσc' (BX := BX) (BX' := BX') hK hτ hσ
  have hbc1 := baseChange_comp_pr₁ hI hI' A g τ τ_symm σ hστ hσc τ' τ'_symm σ' hστ' hσc' hII'
    hK hτ hσ hsq
  have hbc2 := baseChange_comp_pr₂ hI hI' A g τ τ_symm σ hστ hσc τ' τ'_symm σ' hστ' hσc' hII'
    hK hτ hσ hsq
  have hkey : eqToHom hsrc.symm ≫ diagonal' (AffineChartedFibreDatumX.ofAlgebraData (B := BX')
        hI' A g τ' τ'_symm σ' hστ' hσc') σ' hστ' hσc' ≫
      (diagonalDoubleChartGlue hI' A g τ' τ'_symm σ' hστ' hσc' BX').baseChange
        (diagonalDoubleChartGlue hI A g τ τ_symm σ hστ hσc BX) hI' hI hII' hsq =
      diagonal' (AffineChartedFibreDatumX.ofAlgebraData (B := BX) hI A g τ τ_symm σ hστ hσc)
        σ hστ hσc := by
    refine (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX) hI A g τ τ_symm σ hστ
      hσc) σ hστ hσc).fibreLift_unique_adicOverBase (ofFactors_hV _ _ _ _ _ _ _ _)
      (ofFactors_hf _ _ _ _ _ _ _ _) (ofFactors_ht _ _ _ _ _ _ _ _) _ _
      (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX) hI A g τ τ_symm σ hστ hσc)
        σ hστ hσc).xStructMap
      (adicOverBase_xStructMap (diagonalDatum (AffineChartedFibreDatumX.ofAlgebraData (B := BX) hI
        A g τ τ_symm σ hστ hσc) σ hστ hσc)) ?_ ?_ ?_
    · simp only [Category.assoc]
      rw [hbc1, reassoc_of% (diagonal'_comp_pr₁ (AffineChartedFibreDatumX.ofAlgebraData
        (B := BX') hI' A g τ' τ'_symm σ' hστ' hσc') σ' hστ' hσc'), diagonal'_comp_pr₁]
      simp
    · simp only [Category.assoc]
      rw [hbc2, reassoc_of% (diagonal'_comp_pr₂ (AffineChartedFibreDatumX.ofAlgebraData
        (B := BX') hI' A g τ' τ'_symm σ' hστ' hσc') σ' hστ' hσc'), diagonal'_comp_pr₂]
      simp
    · simp only [Category.assoc]
      rw [reassoc_of% hbc1, reassoc_of% (diagonal'_comp_pr₁ (AffineChartedFibreDatumX.ofAlgebraData
        (B := BX') hI' A g τ' τ'_symm σ' hστ' hσc') σ' hστ' hσc')]
      simp
  rw [← hkey, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

/-! ### The two glue hypotheses, discharged at the diagonal -/

omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace R'] [IsAdicRing I']
  [Algebra R R'] [∀ i, IsScalarTower R R' (A i)] [∀ i : J, TopologicalSpace (A i)]
  [∀ i : J, IsAdicRing (I.map (algebraMap R (A i)))]
  [∀ i : J, IsAdicRing (I'.map (algebraMap R' (A i)))] in
/-- **At the diagonal the two-family transition condition is the one-family one, taken twice.**
`AlgebraicGeometry.IsChartTransitionBaseChange` is a structure with exactly two fields, one per
chart family; the diagonal supplies the same family on both sides, so both fields are the single
`HEq` of underlying functions that
`AlgebraicGeometry.BothChartedFibreDatumXY.xGlued_diagonalDatum_ofAlgebraData_congr` already asks
for under the name `hτ`.

That is why the two hypotheses discharged below cost a caller *nothing*: the input they need is
one a caller of
`AlgebraicGeometry.BothChartedFibreDatumXY.isSeparated_of_isSeparated_baseChange` was already
supplying for the congruence. The `σ`-half of that congruence, `hσ`, is **not** part of this
condition and is not part of either discharge — the double-overlap transitions are used to
identify the two glued factors and never to compare the two overlap glues. -/
theorem isChartTransitionBaseChange_diagonal
    (hτ : ∀ (i j : J) (h : i ≠ j), HEq (⇑(τ' i j h)) (⇑(τ i j h))) :
    IsChartTransitionBaseChange τ τ τ' τ' :=
  ⟨hτ, hτ⟩

omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace R'] [IsAdicRing I'] in
/-- **The overlap square at the diagonal glue is a theorem, not a hypothesis.** *Reach for this
one* instead of carrying `AlgebraicGeometry.DoubleChartGlue.IsBaseChangeOverlapCompatible` as an
assumption: it is
`AlgebraicGeometry.DoubleChartGlue.isBaseChangeOverlapCompatible_of_bothAlgData` with all six of
its identifications filled in.

`AlgebraicGeometry.BothChartedFibreDatumXY.diagonalDoubleChartGlue` is
`AlgebraicGeometry.BothChartedFibreDatum.ofAlgebraData`'s glue of one factor taken twice —
`AlgebraicGeometry.BothChartedFibreDatumXY.toBothChartedFibreDatum` of
`AlgebraicGeometry.BothChartedFibreDatumXY.ofFactors` *is* that smart constructor — and it already
reads the result at the ambient chart family. So its `V`, `f` and `t` are the dispatched
`AlgebraicGeometry.bothAlgDataV` / `..bothAlgDataF` / `..bothAlgDataT` by `rfl`, and the six
hypotheses are three proofs used twice: `rfl`, `Category.id_comp` read backwards, and — for the
transition, which carries an `eqToHom` at **each** end — `Category.id_comp` and `Category.comp_id`
together.

The transition agreement is the only genuine input, and
`AlgebraicGeometry.BothChartedFibreDatumXY.isChartTransitionBaseChange_diagonal` builds it from a
hypothesis the diagonal's callers already hold. -/
theorem isBaseChangeOverlapCompatible_diagonalDoubleChartGlue
    (hII' : I.map (algebraMap R R') = I')
    (hτbc : IsChartTransitionBaseChange τ τ τ' τ') :
    DoubleChartGlue.IsBaseChangeOverlapCompatible
      (diagonalDoubleChartGlue hI' A g τ' τ'_symm σ' hστ' hσc' BX')
      (diagonalDoubleChartGlue hI A g τ τ_symm σ hστ hσc BX) hI hII' :=
  DoubleChartGlue.isBaseChangeOverlapCompatible_of_bothAlgData _ _ hI hII' τ τ τ' τ' hτbc
    (fun _ _ _ => rfl) (fun _ _ _ => (Category.id_comp _).symm)
    (fun _ _ _ => ((Category.id_comp _).trans (Category.comp_id _)).symm)
    (fun _ _ _ => rfl) (fun _ _ _ => (Category.id_comp _).symm)
    (fun _ _ _ => ((Category.id_comp _).trans (Category.comp_id _)).symm)

omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace R'] [IsAdicRing I'] in
/-- **The saturation at the diagonal glue is a theorem over no input at all.** *Reach for this
one*: unlike the square it needs neither the transition agreement nor anything else about how the
primed datum was chosen.

`AlgebraicGeometry.DoubleChartGlue.isBaseChangeOverlapSaturated_of_range_eq_bothAlgDataF` asks only
that the two glues carry the dispatched overlap immersions, and at
`AlgebraicGeometry.BothChartedFibreDatumXY.diagonalDoubleChartGlue` each side is `rfl`. The two
hypotheses are the same one away family `g` on both sides of the tower, which is what makes the
diagonal a diagonal. -/
theorem isBaseChangeOverlapSaturated_diagonalDoubleChartGlue
    (hII' : I.map (algebraMap R R') = I') :
    DoubleChartGlue.IsBaseChangeOverlapSaturated
      (diagonalDoubleChartGlue hI' A g τ' τ'_symm σ' hστ' hσc' BX')
      (diagonalDoubleChartGlue hI A g τ τ_symm σ hστ hσc BX) hI hII' :=
  DoubleChartGlue.isBaseChangeOverlapSaturated_of_range_eq_bothAlgDataF _ _ hI' hI hII' g g
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)

/-- **Separatedness descends along the glued base change.** One chart family `A`, one away family
`g`, two adic bases `(R, I)` and `(R', I')` with `I' = I·R'`, and two sets of algebra data whose
induced ideal families and transitions agree: if the factor is separated over `Spf R` then it is
separated over `Spf R'`.

The comparison is `AlgebraicGeometry.DoubleChartGlue.baseChange` and its injectivity is
`AlgebraicGeometry.DoubleChartGlue.injective_baseChange_base`, whose two hypotheses — the overlap
square and the overlap saturation — are **not** hypotheses here either: they are
`AlgebraicGeometry.BothChartedFibreDatumXY.isBaseChangeOverlapCompatible_diagonalDoubleChartGlue`
and
`AlgebraicGeometry.BothChartedFibreDatumXY.isBaseChangeOverlapSaturated_diagonalDoubleChartGlue`,
and the only input either needs is the transition agreement, which
`AlgebraicGeometry.BothChartedFibreDatumXY.isChartTransitionBaseChange_diagonal` assembles from
`hτ` below. The triangle is **not** a hypothesis either: it is
`AlgebraicGeometry.BothChartedFibreDatumXY.diagonal'_comp_baseChange`, proved above and supplied at
the call site. See this file's *The argument, in three steps*, step 3. **So this statement asks
nothing at all about the glue**: what is left is that the two sets of algebra data agree, and the
separatedness being descended.

The conclusion is about a **datum**, `AlgebraicGeometry.BothChartedFibreDatumXY.IsSeparated`. It is
not `AlgebraicGeometry.FormalScheme.IsSeparatedOverSpf`, which quantifies existentially over a
presentation, and it says nothing about a datum whose charts are not shared between the two
bases. -/
theorem isSeparated_of_isSeparated_baseChange
    (hII' : I.map (algebraMap R R') = I')
    (hK : (fun i => I'.map (algebraMap R' (A i))) = fun i => I.map (algebraMap R (A i)))
    (hτ : ∀ (i j : J) (h : i ≠ j), HEq (⇑(τ' i j h)) (⇑(τ i j h)))
    (hσ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      HEq (⇑(σ' i j k hij hik hjk)) (⇑(σ i j k hij hik hjk)))
    (hsep : IsSeparated
      (AffineChartedFibreDatumX.ofAlgebraData (B := BX) hI A g τ τ_symm σ hστ hσc) σ hστ hσc) :
    IsSeparated (AffineChartedFibreDatumX.ofAlgebraData (B := BX') hI' A g τ' τ'_symm σ' hστ' hσc')
      σ' hστ' hσc' := by
  haveI : ∀ p : J × J, IsAdicRing (idealOfDefinition R I (A p.1) (A p.2)) := fun p =>
    CompletedTensorProduct.isAdicRing R I (A p.1) (A p.2) hI
  haveI : ∀ p : J × J, IsAdicRing (idealOfDefinition R' I' (A p.1) (A p.2)) := fun p =>
    CompletedTensorProduct.isAdicRing R' I' (A p.1) (A p.2) hI'
  have hsq := isBaseChangeOverlapCompatible_diagonalDoubleChartGlue hI hI' A g τ τ_symm σ hστ hσc
    τ' τ'_symm σ' hστ' hσc' (BX := BX) (BX' := BX') hII'
    (isChartTransitionBaseChange_diagonal A g τ τ' hτ)
  have hsat := isBaseChangeOverlapSaturated_diagonalDoubleChartGlue hI hI' A g τ τ_symm σ hστ hσc
    τ' τ'_symm σ' hστ' hσc' (BX := BX) (BX' := BX') hII'
  refine isSeparated_of_isSeparated_of_diagonal_factorization
    (AffineChartedFibreDatumX.ofAlgebraData (B := BX) hI A g τ τ_symm σ hστ hσc) σ hστ hσc
    (AffineChartedFibreDatumX.ofAlgebraData (B := BX') hI' A g τ' τ'_symm σ' hστ' hσc')
    σ' hστ' hσc'
    (xGlued_diagonalDatum_ofAlgebraData_congr hI hI' A g τ τ_symm σ hστ hσc τ' τ'_symm σ' hστ'
      hσc' (BX := BX) (BX' := BX') hK hτ hσ)
    ((diagonalDoubleChartGlue hI' A g τ' τ'_symm σ' hστ' hσc' BX').baseChange
      (diagonalDoubleChartGlue hI A g τ τ_symm σ hστ hσc BX) hI' hI hII' hsq) ?_
    (diagonal'_comp_baseChange hI hI' A g τ τ_symm σ hστ hσc τ' τ'_symm σ' hστ' hσc' hII' hK hτ
      hσ hsq) hsep
  exact DoubleChartGlue.injective_baseChange_base _ _ hI' hI hII' hsq hsat

end OfAlgebraData

end BothChartedFibreDatumXY

end AlgebraicGeometry

end
