import FormalSchemes.ThickeningBasicOpenRefinement
import FormalSchemes.FormalLineWitness
import Mathlib.Geometry.RingedSpace.OpenImmersion

set_option linter.style.header false

/-!
# Restricting a compatible family to a chart (EGA I, 10.6.10)

The three landed slices of the colimit property for a **non-affine** target are topological:
`FormalSchemes/ThickeningCommonBase.lean` gives a compatible family
`f n : Spec (R ⧸ I ^ (n + 1)) ⟶ X` a single base map `commonBase I f : |Spf R| ⟶ |X|`;
`FormalSchemes/ThickeningCoverPullback.lean` pulls an open cover of `X` back along it;
`FormalSchemes/ThickeningBasicOpenRefinement.lean` refines that cover by basic opens, finitely
many of which suffice. None of them moves a structure sheaf.

This file takes the first step that does. Given an open `U ⊆ X`, it cuts the whole family down to
`U`: the `n`-th thickening is restricted to the open `f n ⁻¹ U` lying over `U`, the target is
restricted to `U`, and the resulting morphisms **again form a compatible family over the tower**.
That last statement is the deliverable; the rest is setup.

## `LocallyRingedSpace` or `Scheme`? — neither, as it turns out

Restricting a morphism to an open of its target is spelled `f ∣_ U` in Mathlib
(`AlgebraicGeometry.morphismRestrict`), and that API exists **only for `Scheme`** — there is no
counterpart anywhere under `Mathlib/Geometry/RingedSpace/`. So the obvious readings of this step
are to specialise the whole `Thickening*` layer to a scheme target (cheap, since
`Scheme.forgetToLocallyRingedSpace` is full and faithful, but it narrows every statement above),
or to build `morphismRestrict` for `LocallyRingedSpace` (a Mathlib-shaped contribution in its own
right).

**Neither is necessary.** What this step actually needs is not the general `f ∣_ U` API but a
single universal property, and that one *does* exist for locally ringed spaces:
`LocallyRingedSpace.IsOpenImmersion.lift` builds `Y ⟶ X` from `g : Y ⟶ Z` and an open immersion
`X ⟶ Z` whose range contains that of `g`, together with `lift_fac` and `lift_uniq`. Since
`X.ofRestrict U.isOpenEmbedding` is an open immersion with range exactly `U`, every morphism of
this file is a `lift`, every factorisation is `lift_fac`, and the compatibility is `lift_uniq`
applied to a composite whose factorisation is already known. The target stays an **arbitrary
locally ringed space**, exactly as in the three slices above, and no new layer is introduced.

The one thing paid for this is an import of `Mathlib.Geometry.RingedSpace.OpenImmersion`, which
was not previously in this subtree's closure.

## Main definitions and results

* `FormalSpectrum.thickeningChart`: the open `f n ⁻¹ U` of the `n`-th thickening lying over `U`,
  and `map_commonBase_obj_eq_thickeningChart` identifying it with the pulled-back open of
  `ThickeningCoverPullback.lean` transported along `thickeningTopIso`.
* `FormalSpectrum.chartRestrict`: the restricted morphism
  `Spec (R ⧸ I ^ (n + 1))|_{f n ⁻¹ U} ⟶ X|_U`, with `chartRestrict_comp_ofRestrict` its
  factorisation and `chartRestrict_uniq` its uniqueness.
* `FormalSpectrum.stepChartRestrict`: the restriction of the tower's own transition map to the
  charts — this is what makes "the restricted family" a family over the *same* tower.
* `FormalSpectrum.stepChartRestrict_comp_chartRestrict`: **the restricted family is again
  compatible.** This is the theorem.
* `AlgebraicGeometry.LocallyRingedSpace.range_ofRestrict`: the range of `Y|_V ⟶ Y` is `V`, in
  the spelling the `lift` hypotheses take. Everything else in the file is an application of it.

This is also the first file on umbrella 59 whose witness is **not** degenerate: the chart it cuts
out of each thickening is a proper, non-empty open, which the one-point `|Spf ℤ^|` cannot
exhibit. See the witness section.

## Implementation notes

**Where a helper lemma goes.** Every module in this cluster opens with `namespace FormalSpectrum`,
so a general lemma written at the top of a file silently acquires that namespace. Three consecutive
pull requests did exactly that and each was flagged for it in review; the rule the sweep left
behind is:

> A declaration whose *statement* mentions no ring, no ideal and no spectrum does not belong in
> `FormalSpectrum`. Put it where its own subject lives — `AlgebraicGeometry.LocallyRingedSpace`,
> `AlgebraicGeometry.Scheme`, `TopologicalSpace.Opens`, `Int` — and it will be found by the next
> person who needs it instead of being rewritten.

`range_ofRestrict` above is the instance from this file. The test is mechanical enough to apply
while writing: read the statement, not the motivation. `range_ofRestrict` exists *because* of the
thickening charts, and says nothing about them.

Three pieces of friction, all of the same kind: a term is definitionally what a lemma wants but
not syntactically, so `rw` refuses while `exact` does not. None of them needs a transparency
bump, and this file sets no option beyond the header linter.

`Opens.set_range_inclusion'` is stated about `Opens.inclusion' V`, while the goals here are about
`(Y.ofRestrict V.isOpenEmbedding).base`. Leaving `V` as a metavariable makes the `rw` fail with a
type mismatch on the `Set.range` argument; naming it once in `range_ofRestrict` and rewriting with
that instead avoids the problem at both call sites.

In `range_ofRestrict_comp_step_subset` the goal's argument is the *composite* base map
`(ofRestrict ≫ step).base y`, inside which `rw` cannot see the step map. Stating the split form as
a `have` and closing with `exact` — which unfolds `LocallyRingedSpace.comp_base` — costs two lines
and no options. The pointwise compatibility `base_step_apply` it uses is proved by the
`conv_rhs => rw [← hf n]` idiom of `ThickeningCommonBase.lean`, for the reason recorded there:
rewriting forwards with a `congrArg` over a lambda in the morphism forces the motive's type, which
mentions the underlying space of `Spec` of a quotient ring, to be unfolded in the kernel.

Finally, the carriers `↑(TopCat.of (FormalSpectrum I))`, `↑(locallyRingedSpaceObj I).toTopCat` and
`↑↑(locallyRingedSpaceObj I).toPresheafedSpace` are mutually definitionally equal but only at
default transparency. A hypothesis obtained through `mem_thickeningChart` arrives in the third
spelling, and `inv_hom_apply` will not rewrite in it; restating it with a `have` in the first
spelling — the restatement is by `exact` and therefore free — makes the rewrite syntactic. This
is why the witness lemma below takes its open as an `Opens (TopCat.of (FormalSpectrum _))`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.10).
* [The Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

/-- **The restriction of a locally ringed space to an open has that open as its range.** A
restatement of `Opens.set_range_inclusion'` in the spelling the `IsOpenImmersion.lift` hypotheses
below actually take.

It lives in `AlgebraicGeometry.LocallyRingedSpace` rather than in `FormalSpectrum`: its statement
mentions no ring, no ideal and no spectrum. See the implementation notes. -/
theorem range_ofRestrict (Y : LocallyRingedSpace.{u}) (V : Opens Y.toTopCat) :
    Set.range (Y.ofRestrict V.isOpenEmbedding).base = (V : Set Y.toTopCat) :=
  Opens.set_range_inclusion' V

end AlgebraicGeometry.LocallyRingedSpace

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable {X : LocallyRingedSpace.{u}}

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The open of the `n`-th infinitesimal thickening lying over `U`**, namely `f n ⁻¹ U`. For a
compatible family these are the same open of `|Spf R|` for every `n`, read through
`thickeningTopIso` — that is `map_commonBase_obj_eq_thickeningChart`. -/
def thickeningChart
    (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X)
    (U : Opens X.toTopCat) (n : ℕ) :
    Opens (Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).toTopCat :=
  (Opens.map (f n).base).obj U

omit [TopologicalSpace R] [IsAdicRing I] in
/-- Membership in `thickeningChart` is membership of the image in `U`, by definition. -/
theorem mem_thickeningChart
    (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X)
    (U : Opens X.toTopCat) (n : ℕ)
    (y : (Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).toTopCat) :
    y ∈ thickeningChart I f U n ↔ (f n).base y ∈ U :=
  Iff.rfl

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The charts of the thickenings are the pulled-back open of `ThickeningCoverPullback.lean`**,
transported along the identification of `|Spf R|` with the `n`-th thickening's space. This is what
makes the chart decomposition of this file level-independent, and it is exactly
`map_commonBase_obj_eq` restated in the vocabulary used here. -/
theorem map_commonBase_obj_eq_thickeningChart
    (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X)
    (hf : ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ f (n + 1) = f n)
    (n : ℕ) (U : Opens X.toTopCat) :
    (Opens.map (commonBase I f)).obj U =
      (Opens.map (thickeningTopIso I n).hom).obj (thickeningChart I f U n) :=
  map_commonBase_obj_eq I f hf n U

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The range condition for `IsOpenImmersion.lift`**: the `n`-th thickening, restricted to the
chart over `U` and pushed into `X`, lands inside `U`. This is the whole topological input to
`chartRestrict`, and it holds for an arbitrary — not necessarily compatible — family. -/
theorem range_ofRestrict_comp_subset
    (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X)
    (U : Opens X.toTopCat) (n : ℕ) :
    Set.range (((Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).ofRestrict
        (thickeningChart I f U n).isOpenEmbedding ≫ f n).base) ⊆
      Set.range (X.ofRestrict U.isOpenEmbedding).base := by
  rintro z ⟨y, rfl⟩
  rw [X.range_ofRestrict U]
  exact y.2

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The `n`-th member of the family, restricted to the chart over `U`.** Built by the universal
property of the open immersion `X|_U ⟶ X`, so it is the unique morphism compatible with the two
inclusions (`chartRestrict_comp_ofRestrict`, `chartRestrict_uniq`). -/
def chartRestrict
    (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X)
    (U : Opens X.toTopCat) (n : ℕ) :
    (Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).restrict
        (thickeningChart I f U n).isOpenEmbedding ⟶ X.restrict U.isOpenEmbedding :=
  LocallyRingedSpace.IsOpenImmersion.lift (X.ofRestrict U.isOpenEmbedding)
    ((Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).ofRestrict
      (thickeningChart I f U n).isOpenEmbedding ≫ f n)
    (range_ofRestrict_comp_subset I f U n)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The restricted morphism computes the original one on the chart.** -/
@[reassoc]
theorem chartRestrict_comp_ofRestrict
    (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X)
    (U : Opens X.toTopCat) (n : ℕ) :
    chartRestrict I f U n ≫ X.ofRestrict U.isOpenEmbedding =
      (Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).ofRestrict
        (thickeningChart I f U n).isOpenEmbedding ≫ f n :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **`chartRestrict` is the only morphism with that factorisation**, since `X|_U ⟶ X` is a
mono. -/
theorem chartRestrict_uniq
    (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X)
    (U : Opens X.toTopCat) (n : ℕ)
    (l : (Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).restrict
      (thickeningChart I f U n).isOpenEmbedding ⟶ X.restrict U.isOpenEmbedding)
    (hl : l ≫ X.ofRestrict U.isOpenEmbedding =
      (Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).ofRestrict
        (thickeningChart I f U n).isOpenEmbedding ≫ f n) :
    l = chartRestrict I f U n :=
  LocallyRingedSpace.IsOpenImmersion.lift_uniq _ _ _ _ hl

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The pointwise form of the compatibility hypothesis.** Stated separately because it is what
the range condition for the restricted transition map needs, and because the `conv_rhs` idiom it
uses is the one that avoids the kernel timeout documented in `ThickeningCommonBase.lean`. -/
theorem base_step_apply
    (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X)
    (hf : ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ f (n + 1) = f n) (n : ℕ)
    (w : (Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).toTopCat) :
    (f (n + 1)).base ((Spec.locallyRingedSpaceMap (stepRingHom I n)).base w) = (f n).base w := by
  conv_rhs => rw [← hf n]
  rfl

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The tower's transition map carries the chart at level `n` into the chart at level `n + 1`.**
This is where compatibility of the family is used, and it is what lets the restricted morphisms be
a family over the *same* tower rather than over a new one. -/
theorem range_ofRestrict_comp_step_subset
    (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X)
    (hf : ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ f (n + 1) = f n)
    (U : Opens X.toTopCat) (n : ℕ) :
    Set.range (((Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).ofRestrict
        (thickeningChart I f U n).isOpenEmbedding ≫
          Spec.locallyRingedSpaceMap (stepRingHom I n)).base) ⊆
      Set.range ((Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1 + 1)))).ofRestrict
        (thickeningChart I f U (n + 1)).isOpenEmbedding).base := by
  rintro z ⟨y, rfl⟩
  rw [LocallyRingedSpace.range_ofRestrict _ (thickeningChart I f U (n + 1))]
  refine (mem_thickeningChart I f U (n + 1) _).mpr ?_
  -- The goal's argument is the *composite* base map; `rw` cannot see the step map inside it, so
  -- state the split form and let `exact` close the gap definitionally.
  have h : (f (n + 1)).base ((Spec.locallyRingedSpaceMap (stepRingHom I n)).base
      (((Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).ofRestrict
        (thickeningChart I f U n).isOpenEmbedding).base y)) ∈ U := by
    rw [base_step_apply I f hf n]
    exact y.2
  exact h

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The tower's transition map, restricted to the charts.** -/
def stepChartRestrict
    (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X)
    (hf : ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ f (n + 1) = f n)
    (U : Opens X.toTopCat) (n : ℕ) :
    (Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).restrict
        (thickeningChart I f U n).isOpenEmbedding ⟶
      (Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1 + 1)))).restrict
        (thickeningChart I f U (n + 1)).isOpenEmbedding :=
  LocallyRingedSpace.IsOpenImmersion.lift
    ((Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1 + 1)))).ofRestrict
      (thickeningChart I f U (n + 1)).isOpenEmbedding)
    ((Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).ofRestrict
      (thickeningChart I f U n).isOpenEmbedding ≫ Spec.locallyRingedSpaceMap (stepRingHom I n))
    (range_ofRestrict_comp_step_subset I f hf U n)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The restricted transition map computes the original one on the charts.** -/
@[reassoc]
theorem stepChartRestrict_comp_ofRestrict
    (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X)
    (hf : ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ f (n + 1) = f n)
    (U : Opens X.toTopCat) (n : ℕ) :
    stepChartRestrict I f hf U n ≫
        (Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1 + 1)))).ofRestrict
          (thickeningChart I f U (n + 1)).isOpenEmbedding =
      (Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).ofRestrict
          (thickeningChart I f U n).isOpenEmbedding ≫
        Spec.locallyRingedSpaceMap (stepRingHom I n) :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The restricted family is again a compatible family over the tower.** The sheaf-theoretic
content of restricting a compatible family to an open of the target: the whole cocone comes down
to `U`, with no `eqToHom` anywhere, because the charts are *defined* as preimages and the
comparison is forced by the mono `X|_U ⟶ X` rather than transported. -/
theorem stepChartRestrict_comp_chartRestrict
    (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X)
    (hf : ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ f (n + 1) = f n)
    (U : Opens X.toTopCat) (n : ℕ) :
    stepChartRestrict I f hf U n ≫ chartRestrict I f U (n + 1) = chartRestrict I f U n := by
  refine chartRestrict_uniq I f U n _ ?_
  rw [Category.assoc, chartRestrict_comp_ofRestrict, ← Category.assoc,
    stepChartRestrict_comp_ofRestrict, Category.assoc, hf n]

section Witness

/-! ### A concrete witness — the first **proper** chart on this tree

Two degeneracies to rule out. `[IsAdicRing I]` holds at `I = ⊥`, where the tower is constant; and
`U = ⊤`, where `X|_U` is `X` and every statement above is a restatement of its own hypothesis. The
witness below removes the first because its ideal of definition is nonzero
(`FormalSpectrum.formalLineIdeal_ne_bot`, `FormalSchemes/FormalLineWitness.lean`); the rest of this
section is about the second, which is the harder one.

The predecessors of this file could only rule out the second one on the *target* side, because
`FormalSpectrum I` is `PrimeSpectrum (R ⧸ I)` and the tree's only adic witness was the `2`-adic
integers, whose `|Spf ℤ^|` is a **one-point space**: every open of it is `⊥` or `⊤`, so no chart
of it is proper (proved as `FormalSpectrum.twoAdic_exists_eq_top` in
`FormalSchemes/TwoAdicDegeneracy.lean`). `FormalSchemes/FormalLineWitness.lean` removed that
obstruction — for `ℤ⟦X⟧` the formal spectrum is `Spec ℤ`, with a two-piece cover `twoChart`
neither member of which is `⊤`.

So the witness here is the tautological family (the thickening morphisms, compatible by
`thickeningMap_comp`) at `U = twoChart b`, and the chart it cuts out of each thickening is a
**proper, non-empty** open — not `⊤` and not `⊥`. That is the first time a chart on this tree is
either.

Note what is deliberately absent: no second copy of the `Spec ℤ = D(2) ∪ D(3)` target witness. It
is already `private` in `ThickeningCoverPullback.lean` and `ThickeningBasicOpenRefinement.lean`,
and a third copy is the trigger those files name for extracting it into a shared module (issue
1038). Using `FormalLineWitness.lean` instead gives a strictly stronger witness and adds no copy.
-/

attribute [local instance] isAdicRing_formalLineIdeal

/-- **A chart over a proper open is proper**, for the tautological family: the thickening's base
map is the homeomorphism `thickeningTopIso` (`thickeningMap_base`), and a homeomorphism reflects
`⊤`.

Note the type of `U`. `thickeningChart` wants an `Opens (locallyRingedSpaceObj I).toTopCat`, and
`Opens (TopCat.of (FormalSpectrum I))` is *definitionally* that — but only at default
transparency, so a `rw` against a goal stated in the first spelling fails with an application type
mismatch on the `Membership` instance. Stating the hypothesis in the second spelling, which is
also the one `twoChart` is in, keeps every rewrite below syntactic. -/
private theorem thickeningChart_thickeningMap_ne_top
    (U : Opens (TopCat.of (FormalSpectrum formalLineIdeal))) (hU : U ≠ ⊤) (n : ℕ) :
    thickeningChart formalLineIdeal (thickeningMap formalLineIdeal) U n ≠ ⊤ := by
  intro h
  refine hU (eq_top_iff.mpr fun x _ => ?_)
  have hx : (thickeningTopIso formalLineIdeal n).hom x ∈
      thickeningChart formalLineIdeal (thickeningMap formalLineIdeal) U n := by
    rw [h]; trivial
  have hx2 := (mem_thickeningChart formalLineIdeal (thickeningMap formalLineIdeal) U n _).mp hx
  -- Restate `hx2` with the base map spelled as `thickeningTopIso.inv` (`thickeningMap_base` is
  -- `rfl`) *and* in the clean carrier type, so that `inv_hom_apply` matches syntactically.
  have hx3 : (thickeningTopIso formalLineIdeal n).inv
      ((thickeningTopIso formalLineIdeal n).hom x) ∈ U := hx2
  rwa [inv_hom_apply] at hx3

/-- The generic point of `Spec ℤ`, as a point of `|Spf ℤ⟦X⟧|`. It lies in both charts, since the
zero ideal contains neither `2` nor `3`. -/
private def genericPoint : FormalSpectrum formalLineIdeal :=
  ofPrimeInt ⟨⊥, Ideal.isPrime_bot⟩

/-- **Both charts are non-empty**, so the witness below is not the empty open in disguise. -/
private theorem mem_twoChart_genericPoint (b : Bool) : genericPoint ∈ twoChart b := by
  cases b with
  | true =>
    rw [twoChart, if_pos rfl, genericPoint, mem_basicOpen_ofPrimeInt, map_ofNat, map_ofNat]
    exact fun hmem => two_ne_zero (Ideal.mem_bot.mp hmem)
  | false =>
    rw [twoChart, if_neg (by simp), genericPoint, mem_basicOpen_ofPrimeInt, map_ofNat, map_ofNat]
    exact fun hmem => three_ne_zero (Ideal.mem_bot.mp hmem)

/-- **The chart cut out of a thickening of `Spf ℤ⟦X⟧` is a proper open**: not `⊤` … -/
example (b : Bool) (n : ℕ) :
    thickeningChart formalLineIdeal (thickeningMap formalLineIdeal) (twoChart b) n ≠ ⊤ :=
  thickeningChart_thickeningMap_ne_top (twoChart b) (twoChart_ne_top b) n

/-- … and not `⊥`, since the generic point of `Spec ℤ` lies in it. -/
example (b : Bool) (n : ℕ) :
    (thickeningTopIso formalLineIdeal n).hom genericPoint ∈
      thickeningChart formalLineIdeal (thickeningMap formalLineIdeal) (twoChart b) n :=
  (mem_thickeningChart formalLineIdeal (thickeningMap formalLineIdeal) (twoChart b) n _).mpr
    (by
      have h : (thickeningTopIso formalLineIdeal n).inv
          ((thickeningTopIso formalLineIdeal n).hom genericPoint) ∈ twoChart b := by
        rw [inv_hom_apply]
        exact mem_twoChart_genericPoint b
      exact h)

/-- **The restricted family is compatible, at a genuinely proper chart.** This is
`stepChartRestrict_comp_chartRestrict` with every hypothesis discharged by a concrete witness. -/
example (b : Bool) (n : ℕ) :
    stepChartRestrict formalLineIdeal (thickeningMap formalLineIdeal)
          (thickeningMap_comp formalLineIdeal) (twoChart b) n ≫
        chartRestrict formalLineIdeal (thickeningMap formalLineIdeal) (twoChart b) (n + 1) =
      chartRestrict formalLineIdeal (thickeningMap formalLineIdeal) (twoChart b) n :=
  stepChartRestrict_comp_chartRestrict formalLineIdeal (thickeningMap formalLineIdeal)
    (thickeningMap_comp formalLineIdeal) (twoChart b) n

end Witness

end FormalSpectrum

end
