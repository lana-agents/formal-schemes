import FormalSchemes.TateInvNodeChartBaseRegular

set_option linter.style.header false

/-!
# The node chart's forward legs at an arbitrary element of the annulus algebra

`FormalSchemes.TateInvNodeChartBaseRegular` computes the two forward legs of the node chart **on
the structural image of the base**: for `r : R`,

```
tateInvNodeChartTargetEquivX R I q hq hI (tateInvNodeChartAwayLegX R I q hq hI (algebraMap R _ r))
  = algebraMap R (A{1/x}{1/(x + y − 1)}) r
```

for `A = annulusAlgebra R I q = R{x, y}/(x·y − q)`. That is exactly what obstruction (b) of issue
1284 needed, and nothing more.

This file proves the same computation **at an arbitrary `a : A`**, and reads left-regularity off it
the same way. Every statement in `TateInvNodeChartBaseRegular` is the case `a = algebraMap R A r`
of a statement here, bridged by `awayCompletionHom_algebraMap_annulusAlgebra`; the base-image
versions are **not** re-proved and stay where they are, since they are what the principal-base
results cite.

The generality is not decoration. A consumer computing sections of the node chart over an open that
is not cut out by the base — issue 1223's equalizer over the model patch is the live example — has
elements of `A` in hand, not images of elements of `R`, and the base-image computation says nothing
about them.

## Contents

* `AlgebraicGeometry.tateInvNodeChartAmbientEquiv_symm_awayCompletionHom` — the ambient
  identification inverted on the structural image, which is what replaces
  `AlgebraicGeometry.tateInvNodeChartAmbientEquiv_sectionsOpenHom_algebraMap` once `r : R` is
  widened to `a : A`.
* `AlgebraicGeometry.tateInvNodeChartAwayLegX_awayCompletionHom` and its `Y` companion — the legs
  on the structural image, still in the presheaf spelling.
* `AlgebraicGeometry.tateInvNodeChartTargetEquivX_sectionsOpenHom` and its `Y` companion — the
  target identification evaluated at a section coming from the once-completed ring.
* `AlgebraicGeometry.tateInvNodeChartTargetEquivX_tateInvNodeChartAwayLegX` and its `Y` companion —
  **the general leg computation**: the leg carries the image of `a` in `A{1/(x + y − 1)}` to its
  image in `A{1/x}{1/(x + y − 1)}` under the two structural maps.
* `AlgebraicGeometry.isLeftRegular_tateInvNodeChartAwayLegX_iff` and its `Y` companion — the same,
  as an `↔` on `IsLeftRegular`, via `MulEquiv.isLeftRegular_apply_iff`.
* `AlgebraicGeometry.isLeftRegular_tateInvNodeChartAwayLegX` and its `Y` companion — a left-regular
  `a : A` has left-regular leg image, by `FormalSpectrum.isLeftRegular_algebraMap_awayCompletion`
  twice.
* `AlgebraicGeometry.awayCompletionHom_algebraMap_annulusAlgebra` — the bridge between the
  `awayCompletionHom _ _ a` spelling used here and the `algebraMap R _ r` spelling used by
  `FormalSchemes.TateInvNodeChartPrincipal` and by `TateInvNodeChartBaseRegular`. The base-image
  consequences themselves are **not** restated here; `TateInvNodeChartBaseRegular` already has
  them, and its docstring says how they compose.

## What is *not* proved

* **Nothing new about obstruction (b).** The principal-base results already carry their weakest
  hypothesis — `IsLeftRegular (algebraMap R (annulusAlgebra R I q) t)` — and this file does not
  weaken it further, does not exhibit an `(R, I, q, t)` with `t ≠ 0` satisfying it, and gives no
  counterexample. That question is unchanged and lives on issue 1319.
* **Nothing in the converse direction.** `isLeftRegular_tateInvNodeChartAwayLegX_iff` is an `↔`
  between the leg image and the twice-completed image, which is a change of spelling; the passage
  from `a` regular in `A` to its image regular in `A{1/x}{1/(x + y − 1)}` is one-way, since
  `overlapX` and `annulusNodeChartCoord` both become units.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum TopologicalSpace
open Opposite TopCat.Presheaf

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)

/-! ### The two forward legs on the structural image -/

section Legs

variable [IsAdicRing (annulusIdealOfDefinition R I q)]
variable [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))]
variable [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))]

omit [TopologicalSpace R] [IsAdicRing I]
  [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))]
  [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))] in
/-- **The node chart's ambient identification, inverted on the structural image.**
`AlgebraicGeometry.tateInvNodeChartAmbientEquiv` is `FormalSpectrum.sectionsEquivOfEqBasicOpen`,
which carries `FormalSpectrum.sectionsOpenHom` to `FormalSpectrum.awayCompletionHom`
(`FormalSpectrum.sectionsEquivOfEqBasicOpen_sectionsOpenHom`, in
`FormalSchemes.TateInvNodeChartAmbient`); this is that equation read backwards through the
isomorphism.

At `a = algebraMap R (annulusAlgebra R I q) r` this is
`AlgebraicGeometry.tateInvNodeChartAmbientEquiv_sectionsOpenHom_algebraMap` inverted, which is what
`FormalSchemes.TateInvNodeChartBaseRegular` uses; the point of stating it at `a` is that the
base-image lemma has no content at an `a` that is not a base image. -/
theorem tateInvNodeChartAmbientEquiv_symm_awayCompletionHom (a : annulusAlgebra R I q) :
    (tateInvNodeChartAmbientEquiv R I q hq hI).symm
        (awayCompletionHom (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) a) =
      sectionsOpenHom (annulusIdealOfDefinition R I q)
        (tateInvPatchSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q)) a := by
  apply (tateInvNodeChartAmbientEquiv R I q hq hI).injective
  rw [RingEquiv.apply_symm_apply, tateInvNodeChartAmbientEquiv,
    FormalSpectrum.sectionsEquivOfEqBasicOpen_sectionsOpenHom]

omit [TopologicalSpace R] [IsAdicRing I]
  [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))] in
/-- **The `x`-side forward leg on the structural image, still in the presheaf spelling.**
`AlgebraicGeometry.tateInvNodeChartAwayLegX` is `AlgebraicGeometry.tateInvChartLegX` precomposed
with the ambient identification, so this is the previous theorem followed by
`AlgebraicGeometry.tateInvChartLegX_sectionsOpenHom` (`FormalSchemes.TateInvChartBaseImage`). -/
theorem tateInvNodeChartAwayLegX_awayCompletionHom (a : annulusAlgebra R I q) :
    tateInvNodeChartAwayLegX R I q hq hI
        (awayCompletionHom (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) a) =
      sectionsOpenHom (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
        ((Opens.map (annulusOverlapChart R I q).base).obj
          (tateInvPatchSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q)))
        (tateInvGlobalLegX a) :=
  (congrArg (tateInvChartLegX (hq := hq) (hI := hI) (isOpen_tateInvNodeChartLocus R I q))
      (tateInvNodeChartAmbientEquiv_symm_awayCompletionHom R I q hq hI a)).trans
    (tateInvChartLegX_sectionsOpenHom (isOpen_tateInvNodeChartLocus R I q) a)

omit [TopologicalSpace R] [IsAdicRing I]
  [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))] in
/-- **The `y`-side forward leg on the structural image, still in the presheaf spelling.** The
mirror image of `tateInvNodeChartAwayLegX_awayCompletionHom`, along
`AlgebraicGeometry.tateInvChartLegY_sectionsOpenHom`. -/
theorem tateInvNodeChartAwayLegY_awayCompletionHom (a : annulusAlgebra R I q) :
    tateInvNodeChartAwayLegY R I q hq hI
        (awayCompletionHom (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) a) =
      sectionsOpenHom (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))
        ((Opens.map (annulusOverlapChartY R I q).base).obj
          (tateInvPatchSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q)))
        (tateInvGlobalLegY a) :=
  (congrArg (tateInvChartLegY (hq := hq) (hI := hI) (isOpen_tateInvNodeChartLocus R I q))
      (tateInvNodeChartAmbientEquiv_symm_awayCompletionHom R I q hq hI a)).trans
    (tateInvChartLegY_sectionsOpenHom (isOpen_tateInvNodeChartLocus R I q) a)

omit [TopologicalSpace R] [IsAdicRing I] [IsAdicRing (annulusIdealOfDefinition R I q)]
  [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))] in
/-- **The `x`-side target identification on the structural image.**
`AlgebraicGeometry.tateInvNodeChartTargetEquivX` is `FormalSpectrum.sectionsEquivOfEqBasicOpen` at
`AlgebraicGeometry.tateInvNodeChartTargetOpensX_eq_basicOpen`, so this is
`FormalSpectrum.sectionsEquivOfEqBasicOpen_sectionsOpenHom` at the once-completed ring `A{1/x}`. -/
theorem tateInvNodeChartTargetEquivX_sectionsOpenHom
    (b : awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q)) :
    tateInvNodeChartTargetEquivX R I q hq hI
        (sectionsOpenHom (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
          ((Opens.map (annulusOverlapChart R I q).base).obj
            (tateInvPatchSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q))) b) =
      awayCompletionHom (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
        (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)
          (annulusNodeChartCoord R I q)) b :=
  FormalSpectrum.sectionsEquivOfEqBasicOpen_sectionsOpenHom _
    (tateInvNodeChartTargetOpensX_eq_basicOpen R I q hq hI) b

omit [TopologicalSpace R] [IsAdicRing I] [IsAdicRing (annulusIdealOfDefinition R I q)]
  [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))] in
/-- **The `y`-side target identification on the structural image.** -/
theorem tateInvNodeChartTargetEquivY_sectionsOpenHom
    (b : awayCompletion (annulusIdealOfDefinition R I q) (overlapY R I q)) :
    tateInvNodeChartTargetEquivY R I q hq hI
        (sectionsOpenHom (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))
          ((Opens.map (annulusOverlapChartY R I q).base).obj
            (tateInvPatchSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q))) b) =
      awayCompletionHom (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))
        (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)
          (annulusNodeChartCoord R I q)) b :=
  FormalSpectrum.sectionsEquivOfEqBasicOpen_sectionsOpenHom _
    (tateInvNodeChartTargetOpensY_eq_basicOpen R I q hq hI) b

omit [TopologicalSpace R] [IsAdicRing I]
  [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))] in
/-- **The `x`-side forward leg on the structural image is a two-step completed localization.**
Read through `AlgebraicGeometry.tateInvNodeChartTargetEquivX`, the leg carries the image of
`a : A` in `A{1/(x + y − 1)}` to its image in `A{1/x}{1/(x + y − 1)}` under the two structural maps
`FormalSpectrum.awayCompletionHom`. The inner one is `AlgebraicGeometry.tateInvGlobalLegX`, which
is that map on the nose.

`AlgebraicGeometry.tateInvNodeChartTargetEquivX_tateInvNodeChartAwayLegX_algebraMap`
(`FormalSchemes.TateInvNodeChartBaseRegular`) is this at `a = algebraMap R _ r`, modulo the two
applications of `FormalSpectrum.awayCompletionHom_comp_algebraMap` that turn each structural image
of a base element back into an `algebraMap R _`. -/
theorem tateInvNodeChartTargetEquivX_tateInvNodeChartAwayLegX (a : annulusAlgebra R I q) :
    tateInvNodeChartTargetEquivX R I q hq hI
        (tateInvNodeChartAwayLegX R I q hq hI
          (awayCompletionHom (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) a)) =
      awayCompletionHom (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
        (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)
          (annulusNodeChartCoord R I q))
        (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q) a) :=
  (congrArg (tateInvNodeChartTargetEquivX R I q hq hI)
      (tateInvNodeChartAwayLegX_awayCompletionHom R I q hq hI a)).trans
    (tateInvNodeChartTargetEquivX_sectionsOpenHom R I q hq hI (tateInvGlobalLegX a))

omit [TopologicalSpace R] [IsAdicRing I]
  [IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))] in
/-- **The `y`-side forward leg on the structural image is a two-step completed localization**, with
`A{1/y}` in place of `A{1/x}`. -/
theorem tateInvNodeChartTargetEquivY_tateInvNodeChartAwayLegY (a : annulusAlgebra R I q) :
    tateInvNodeChartTargetEquivY R I q hq hI
        (tateInvNodeChartAwayLegY R I q hq hI
          (awayCompletionHom (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) a)) =
      awayCompletionHom (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))
        (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)
          (annulusNodeChartCoord R I q))
        (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q) a) :=
  (congrArg (tateInvNodeChartTargetEquivY R I q hq hI)
      (tateInvNodeChartAwayLegY_awayCompletionHom R I q hq hI a)).trans
    (tateInvNodeChartTargetEquivY_sectionsOpenHom R I q hq hI (tateInvGlobalLegY a))

end Legs

/-! ### Left-regularity at an arbitrary element -/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Left-regularity of the `x`-side leg image at `a` is left-regularity of the twice-completed
image of `a`.** `MulEquiv.isLeftRegular_apply_iff` at
`AlgebraicGeometry.tateInvNodeChartTargetEquivX`, rewritten by the general leg computation — the
same two moves as
`AlgebraicGeometry.isLeftRegular_tateInvNodeChartAwayLegX_algebraMap_iff`
(`FormalSchemes.TateInvNodeChartBaseRegular`), at an arbitrary `a` instead of a base image. -/
theorem isLeftRegular_tateInvNodeChartAwayLegX_iff (a : annulusAlgebra R I q) :
    IsLeftRegular (tateInvNodeChartAwayLegX R I q hq hI
        (awayCompletionHom (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) a)) ↔
      IsLeftRegular (awayCompletionHom
        (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
        (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)
          (annulusNodeChartCoord R I q))
        (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q) a)) := by
  haveI _hann : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI _hawX : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (overlapX R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  haveI _hawY : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (overlapY R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  exact ((tateInvNodeChartTargetEquivX R I q hq hI).toMulEquiv.isLeftRegular_apply_iff).symm.trans
    (iff_of_eq (congrArg IsLeftRegular
      (tateInvNodeChartTargetEquivX_tateInvNodeChartAwayLegX R I q hq hI a)))

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Left-regularity of the `y`-side leg image at `a` is left-regularity of the twice-completed
image of `a`.** -/
theorem isLeftRegular_tateInvNodeChartAwayLegY_iff (a : annulusAlgebra R I q) :
    IsLeftRegular (tateInvNodeChartAwayLegY R I q hq hI
        (awayCompletionHom (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) a)) ↔
      IsLeftRegular (awayCompletionHom
        (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))
        (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)
          (annulusNodeChartCoord R I q))
        (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q) a)) := by
  haveI _hann : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI _hawX : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (overlapX R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  haveI _hawY : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (overlapY R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  exact ((tateInvNodeChartTargetEquivY R I q hq hI).toMulEquiv.isLeftRegular_apply_iff).symm.trans
    (iff_of_eq (congrArg IsLeftRegular
      (tateInvNodeChartTargetEquivY_tateInvNodeChartAwayLegY R I q hq hI a)))

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **A left-regular element of `A` has left-regular image under the `x`-side forward leg.**
`FormalSpectrum.isLeftRegular_algebraMap_awayCompletion` twice, through the `↔` above.
`FormalSpectrum.awayCompletionHom L f` is `algebraMap _ (awayCompletion L f)` definitionally, so
nothing has to be transported between the two spellings.

`A` is Noetherian because `R` is, and `A{1/x}` is then Noetherian by
`FormalSpectrum.isNoetherianRing_awayCompletion`, which is an instance — that is what lets the
second application reuse the first one's lemma with nothing supplied by hand. -/
theorem isLeftRegular_tateInvNodeChartAwayLegX {a : annulusAlgebra R I q} (ha : IsLeftRegular a) :
    IsLeftRegular (tateInvNodeChartAwayLegX R I q hq hI
      (awayCompletionHom (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) a)) :=
  (isLeftRegular_tateInvNodeChartAwayLegX_iff R I q hq hI a).2
    (FormalSpectrum.isLeftRegular_algebraMap_awayCompletion _ _
      (FormalSpectrum.isLeftRegular_algebraMap_awayCompletion _ _ ha))

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **A left-regular element of `A` has left-regular image under the `y`-side forward leg.** -/
theorem isLeftRegular_tateInvNodeChartAwayLegY {a : annulusAlgebra R I q} (ha : IsLeftRegular a) :
    IsLeftRegular (tateInvNodeChartAwayLegY R I q hq hI
      (awayCompletionHom (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) a)) :=
  (isLeftRegular_tateInvNodeChartAwayLegY_iff R I q hq hI a).2
    (FormalSpectrum.isLeftRegular_algebraMap_awayCompletion _ _
      (FormalSpectrum.isLeftRegular_algebraMap_awayCompletion _ _ ha))

/-! ### The bridge to the base-image spelling -/

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- **The structural image of `r : R` in `A{1/(x + y − 1)}` is `algebraMap R _ r`.**
`FormalSpectrum.awayCompletionHom_comp_algebraMap`, applied at `r`.

The leg hypotheses of `FormalSchemes.TateInvNodeChartPrincipal` are spelled with `algebraMap R _`
and everything in this file with `FormalSpectrum.awayCompletionHom`; this is the bridge, and it is
what makes `isLeftRegular_tateInvNodeChartAwayLegX` applicable to them.

A consumer that only wants the **base image** does not need this file at all — the composition

```
(isLeftRegular_tateInvNodeChartAwayLegX_algebraMap_iff R I q hq hI r).2
  (isLeftRegular_algebraMap_awayCompletion_overlapX R I q r hr)
```

in `FormalSchemes.TateInvNodeChartBaseRegular` already produces the leg regularity from
`hr : IsLeftRegular (algebraMap R (annulusAlgebra R I q) r)`, and no restatement of it is added
here. -/
theorem awayCompletionHom_algebraMap_annulusAlgebra (r : R) :
    awayCompletionHom (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)
        (algebraMap R (annulusAlgebra R I q) r) =
      algebraMap R
        (awayCompletion (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)) r :=
  congrArg (fun φ : R →+* _ => φ r)
    (FormalSpectrum.awayCompletionHom_comp_algebraMap (R := R) (annulusNodeChartCoord R I q))

end AlgebraicGeometry
