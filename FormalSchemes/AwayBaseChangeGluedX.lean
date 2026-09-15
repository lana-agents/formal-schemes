import FormalSchemes.AwayCompletionUniversal
import FormalSchemes.GeneralFibreProductExposeXIdealCongr

set_option linter.style.header false

/-!
# The base change of a charted `X` along a tower, and along `R → R{1/f}`

`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr`
(`FormalSchemes.GeneralFibreProductExposeXIdealCongr`) compares two adic bases `(R, I)` and
`(R', I')` acting on one chart family and concludes that the two glued formal schemes are
**equal**. It takes the agreement of the induced ideal families as a hypothesis, in the
function-level spelling

```
(fun i => I'.map (algebraMap R' (A i))) = fun i => I.map (algebraMap R (A i))
```

and `Ideal.map_algebraMap_family_eq_of_tower` (`FormalSchemes.AwayCompletionUniversal`) proves
exactly that statement whenever `I'` is the extension of `I` and the chart algebras carry
`IsScalarTower R R' (A i)`. Neither module imports the other and neither names the other. This
file is the edge between them:

* `AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr_of_tower` is the
  congruence with that hypothesis discharged, at any `R'` over `R` and at `I' = I·R'`;
* `AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr_awayBase` is its
  specialisation to `R' = R{1/f}`, where the `R{1/f}`-algebra structure on each chart is the
  universal one, `FormalSpectrum.awayCompletionLift`.

## Why `I' = I·R'` and not an arbitrary `(R', I')`

Because at an arbitrary `(R', I')` the ideal families need not agree, and the statement that they
do is refuted on this tree rather than open: `FormalSchemes.AdicOnSections` records the refutation
of the general adicity statement (issue 460) and
`FormalSpectrum.cofinalSpfIso` (`FormalSchemes.CofinalSheafComparisonIso`) is its witness,
presenting one adic ring at two ideals of definition at once. `Ideal.IsCofinal` is what survives
there, and the transports it would need are not built. Under `I' = I·R'` the agreement is free and
is one application of the tower lemma — which is the whole content of the first result below.

## The shape of the `R{1/f}` case

`FormalSpectrum.awayCompletionLift` produces the ring map `R{1/f} →+* A` for any `R`-algebra `A`
that is `I·A`-adically complete and inverts `f`, and
`FormalSpectrum.isScalarTower_awayCompletionLift` makes `R → R{1/f} → A` a tower for the algebra
structure it defines. That instance is not synthesizable — it depends on the proof that `f` is a
unit — so it cannot be an instance binder in a statement that also mentions the primed transitions,
whose types depend on it. The result below takes the structure as an instance binder and the
identification of its structural map with the lift as an ordinary hypothesis, which keeps every
type in the statement elaborable while pinning the structure to the universal one.
`AlgebraicGeometry.AffineChartedFibreDatumX.isScalarTower_of_algebraMap_eq_awayCompletionLift`
turns that hypothesis into the tower.

## What is not proved here

**The primed transitions are inputs, not outputs.** `τ'`, `σ'` and their two identities are
hypotheses, as is the agreement of `τ'` with `τ` and of `σ'` with `σ` as functions. Constructing
them from `τ` and `σ` is two independent steps and only the first is available:

* *Enlarging the scalars* from `R` to `R{1/f}` is done, by
  `FormalSpectrum.awayCompletionChartAlgEquivBase` (`FormalSchemes.AwayCompletionUniversal`),
  which leaves the underlying function alone — `FormalSpectrum.awayCompletionAlgEquiv_apply` is
  `rfl`.
* *Moving the carriers* from `I·A_i` to `(I·R{1/f})·A_i` is a transport along the very equation
  the tower lemma supplies. It is reachable by the same `subst`-on-a-variable-ideal idiom as
  `FormalSpectrum.awayRingEquiv_heq_of_coe_heq`
  (`FormalSchemes.GeneralFibreProductExposeXIdealCongr`), and the heterogeneous equation it owes
  comes out by `HEq.rfl`; it is not written here because it has no consumer until the rest of the
  step is written.

What is missing is the rest: the symmetry of `τ'` and the two `σ'` identities are statements **over
`R{1/f}`** about maps the transport produces, and the second of them compares composites with the
further localization maps of `I·R{1/f}`, which are not the ones the unprimed identity names. A
transport for those is a separate statement of the same species as
`FormalSpectrum.basicOpenChartOverlapIso_conj_heq`.

**No separation statement.** Nothing here mentions
`AlgebraicGeometry.FormalScheme.IsSeparatedOverSpf`, fibre products or diagonals. The conclusion
is an equality of glued objects and stops there.

## Placement

A leaf over `FormalSchemes.AwayCompletionUniversal` and
`FormalSchemes.GeneralFibreProductExposeXIdealCongr`: forward closure **93**, reverse closure
**0**. The two parents are import-incomparable, so the statement costs either an import edge or a
new leaf, and the edge was rejected in both directions: each parent was itself a leaf, so an edge
either way puts one of them inside the other's subtree and makes every later consumer of that
parent pay for the other. A leaf keeps both parents at the cost they were landed at, and
`FormalSchemes.AwayBaseChangeGluedX`'s own reverse closure is **0**, so nothing pays for it.

`FormalSchemes.AwayCompletionUniversal`'s reverse closure becomes **1**, and
`FormalSchemes.GeneralFibreProductExposeXIdealCongr`'s reverse closure becomes **1**; the figures
recorded in the modules this one reaches move by one each, and every delta is measured in the pull
request that added this module (issue 2028).

## Main results

* `AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr_of_tower`: the glued `X`
  of a smart-constructor datum is unchanged by a change of base along `R → R'` carrying `I` to
  `I·R'`.
* `AlgebraicGeometry.AffineChartedFibreDatumX.isScalarTower_of_algebraMap_eq_awayCompletionLift`:
  an `R{1/f}`-algebra structure on a chart whose structural map is the universal lift is a tower
  over `R`.
* `AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr_awayBase`: the same
  congruence at `R' = R{1/f}`, `I' = I·R{1/f}`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.12.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum

universe u

namespace AlgebraicGeometry

namespace AffineChartedFibreDatumX

section Tower

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] {I : Ideal R} (hI : I.FG)
variable {B : Type u} [CommRing B] [Algebra R B]
variable {B' : Type u} [CommRing B'] [Algebra R' B']
variable {J : Type u} (A : J → Type u) [∀ i, CommRing (A i)]
variable [∀ i, Algebra R (A i)] [∀ i, Algebra R' (A i)] [∀ i, IsScalarTower R R' (A i)]
variable (g : ∀ (i : J), J → A i)
variable [topology : ∀ i : J, TopologicalSpace (A i)]
variable [isAdicA : ∀ i : J, IsAdicRing (I.map (algebraMap R (A i)))]
variable [isAdicA' : ∀ i : J,
  IsAdicRing ((I.map (algebraMap R R')).map (algebraMap R' (A i)))]

/-- **The glued `X` of a smart-constructor datum does not move along a tower.** For `R'` an
`R`-algebra, `I'` the extension `I·R'`, and a chart family that is an algebra over both compatibly,
the two glued formal schemes built by
`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData` are **equal**.

This is `AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr` with its
ideal-family hypothesis discharged by `Ideal.map_algebraMap_family_eq_of_tower`, whose conclusion
is that hypothesis verbatim. The transitions are still inputs on both sides: only the agreement of
the *ideals* is free under a tower, and the agreement of the *transitions* is not. -/
theorem ofAlgebraData_xGlued_congr_of_tower
    (τ : ∀ (i j : J), i ≠ j →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j i)))
    (τ_symm : ∀ (i j : J) (h : i ≠ j), τ j i h.symm = (τ i j h).symm)
    (σ : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j k * g j i)))
    (hστ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ i j k hij hik hjk).symm.toAlgHom.comp
          (CompletedTensorAwayInterchange.furtherLocSnd I (g j k) (g j i) hI) =
        (CompletedTensorAwayInterchange.furtherLocFst I (g i j) (g i k) hI).comp
          (τ i j hij).symm.toAlgHom)
    (hσc : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ i j k hij hik hjk).trans ((σ j k i hjk hij.symm hik.symm).trans
        (σ k i j hik.symm hjk.symm hij)) =
        AlgEquiv.refl (R := R)
          (A₁ := awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k)))
    (τ' : ∀ (i j : J), i ≠ j →
      (awayCompletion ((I.map (algebraMap R R')).map (algebraMap R' (A i))) (g i j) ≃ₐ[R']
        awayCompletion ((I.map (algebraMap R R')).map (algebraMap R' (A j))) (g j i)))
    (τ'_symm : ∀ (i j : J) (h : i ≠ j), τ' j i h.symm = (τ' i j h).symm)
    (σ' : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
      (awayCompletion ((I.map (algebraMap R R')).map (algebraMap R' (A i))) (g i j * g i k) ≃ₐ[R']
        awayCompletion ((I.map (algebraMap R R')).map (algebraMap R' (A j))) (g j k * g j i)))
    (hστ' : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ' i j k hij hik hjk).symm.toAlgHom.comp
          (CompletedTensorAwayInterchange.furtherLocSnd (I.map (algebraMap R R'))
            (g j k) (g j i) (hI.map _)) =
        (CompletedTensorAwayInterchange.furtherLocFst (I.map (algebraMap R R'))
            (g i j) (g i k) (hI.map _)).comp (τ' i j hij).symm.toAlgHom)
    (hσc' : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ' i j k hij hik hjk).trans ((σ' j k i hjk hij.symm hik.symm).trans
        (σ' k i j hik.symm hjk.symm hij)) =
        AlgEquiv.refl (R := R')
          (A₁ := awayCompletion ((I.map (algebraMap R R')).map (algebraMap R' (A i)))
            (g i j * g i k)))
    (hτ : ∀ (i j : J) (h : i ≠ j), HEq (⇑(τ' i j h)) (⇑(τ i j h)))
    (hσ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      HEq (⇑(σ' i j k hij hik hjk)) (⇑(σ i j k hij hik hjk))) :
    (AffineChartedFibreDatumX.ofAlgebraData (B := B') (hI.map (algebraMap R R'))
        A g τ' τ'_symm σ' hστ' hσc').xGlued =
      (AffineChartedFibreDatumX.ofAlgebraData (B := B) hI A g τ τ_symm σ hστ hσc).xGlued :=
  ofAlgebraData_xGlued_congr hI (hI.map (algebraMap R R')) A g τ τ_symm σ hστ hσc
    τ' τ'_symm σ' hστ' hσc' (Ideal.map_algebraMap_family_eq_of_tower A I) hτ hσ

end Tower


section AwayBase

variable {R : Type u} [CommRing R] {I : Ideal R} (hI : I.FG) (f : R)
variable {B : Type u} [CommRing B] [Algebra R B]
variable {B' : Type u} [CommRing B'] [Algebra (awayCompletion I f) B']
variable {J : Type u} (A : J → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable [topology : ∀ i : J, TopologicalSpace (A i)]
variable [isAdicA : ∀ i : J, IsAdicRing (I.map (algebraMap R (A i)))]
variable (hf : ∀ i, IsUnit (algebraMap R (A i) f))
variable [∀ i, Algebra (awayCompletion I f) (A i)]
variable (g : ∀ (i : J), J → A i)
variable [isAdicA' : ∀ i : J,
  IsAdicRing ((I.map (algebraMap R (awayCompletion I f))).map
    (algebraMap (awayCompletion I f) (A i)))]

omit isAdicA' in
/-- **A chart whose `R{1/f}`-structure is the universal lift is a tower over `R`.** The algebra
structure is an instance binder rather than `RingHom.toAlgebra` of
`FormalSpectrum.awayCompletionLift`, because the types of the primed transitions in
`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr_awayBase` depend on it and a
`letI` in the statement would put them out of reach of instance synthesis. The hypothesis
identifying the structural map with the lift is what ties it back to the universal one, and it is
all `FormalSpectrum.isScalarTower_awayCompletionLift` needs. -/
theorem isScalarTower_of_algebraMap_eq_awayCompletionLift
    (halg : ∀ i, letI := (isAdicA i).toIsAdicComplete
      algebraMap (awayCompletion I f) (A i) = awayCompletionLift I f (hf i)) (i : J) :
    IsScalarTower R (awayCompletion I f) (A i) :=
  letI := (isAdicA i).toIsAdicComplete
  IsScalarTower.of_algebraMap_eq fun r => by
    rw [halg i, ← awayCompletionHom_eq_algebraMap]
    exact (awayCompletionLift_awayCompletionHom I f (hf i) r).symm

/-- **The glued `X` of a smart-constructor datum does not move to a basic open of its base.** At
`R' = R{1/f}` and `I' = I·R{1/f}` — the case issue 2007 built every input for, and the only case in
which the ideal-family agreement is free rather than refuted — the two glued formal schemes are
**equal**.

Each chart carries the `R{1/f}`-algebra structure whose structural map is
`FormalSpectrum.awayCompletionLift`, which exists because the chart inverts `f` and is
`I·A_i`-adically complete; the completeness is read off the datum's own adicity witness and is not
a separate hypothesis. -/
theorem ofAlgebraData_xGlued_congr_awayBase
    (halg : ∀ i, letI := (isAdicA i).toIsAdicComplete
      algebraMap (awayCompletion I f) (A i) = awayCompletionLift I f (hf i))
    (τ : ∀ (i j : J), i ≠ j →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j i)))
    (τ_symm : ∀ (i j : J) (h : i ≠ j), τ j i h.symm = (τ i j h).symm)
    (σ : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
      (awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k) ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A j))) (g j k * g j i)))
    (hστ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ i j k hij hik hjk).symm.toAlgHom.comp
          (CompletedTensorAwayInterchange.furtherLocSnd I (g j k) (g j i) hI) =
        (CompletedTensorAwayInterchange.furtherLocFst I (g i j) (g i k) hI).comp
          (τ i j hij).symm.toAlgHom)
    (hσc : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ i j k hij hik hjk).trans ((σ j k i hjk hij.symm hik.symm).trans
        (σ k i j hik.symm hjk.symm hij)) =
        AlgEquiv.refl (R := R)
          (A₁ := awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k)))
    (τ' : ∀ (i j : J), i ≠ j →
      (awayCompletion ((I.map (algebraMap R (awayCompletion I f))).map
          (algebraMap (awayCompletion I f) (A i))) (g i j) ≃ₐ[awayCompletion I f]
        awayCompletion ((I.map (algebraMap R (awayCompletion I f))).map
          (algebraMap (awayCompletion I f) (A j))) (g j i)))
    (τ'_symm : ∀ (i j : J) (h : i ≠ j), τ' j i h.symm = (τ' i j h).symm)
    (σ' : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
      (awayCompletion ((I.map (algebraMap R (awayCompletion I f))).map
          (algebraMap (awayCompletion I f) (A i))) (g i j * g i k) ≃ₐ[awayCompletion I f]
        awayCompletion ((I.map (algebraMap R (awayCompletion I f))).map
          (algebraMap (awayCompletion I f) (A j))) (g j k * g j i)))
    (hστ' : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ' i j k hij hik hjk).symm.toAlgHom.comp
          (CompletedTensorAwayInterchange.furtherLocSnd (I.map (algebraMap R (awayCompletion I f)))
            (g j k) (g j i) (hI.map _)) =
        (CompletedTensorAwayInterchange.furtherLocFst (I.map (algebraMap R (awayCompletion I f)))
            (g i j) (g i k) (hI.map _)).comp (τ' i j hij).symm.toAlgHom)
    (hσc' : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      (σ' i j k hij hik hjk).trans ((σ' j k i hjk hij.symm hik.symm).trans
        (σ' k i j hik.symm hjk.symm hij)) =
        AlgEquiv.refl (R := awayCompletion I f)
          (A₁ := awayCompletion ((I.map (algebraMap R (awayCompletion I f))).map
            (algebraMap (awayCompletion I f) (A i))) (g i j * g i k)))
    (hτ : ∀ (i j : J) (h : i ≠ j), HEq (⇑(τ' i j h)) (⇑(τ i j h)))
    (hσ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      HEq (⇑(σ' i j k hij hik hjk)) (⇑(σ i j k hij hik hjk))) :
    (AffineChartedFibreDatumX.ofAlgebraData (B := B')
        (hI.map (algebraMap R (awayCompletion I f))) A g τ' τ'_symm σ' hστ' hσc').xGlued =
      (AffineChartedFibreDatumX.ofAlgebraData (B := B) hI A g τ τ_symm σ hστ hσc).xGlued :=
  haveI : ∀ i, IsScalarTower R (awayCompletion I f) (A i) :=
    isScalarTower_of_algebraMap_eq_awayCompletionLift f A hf halg
  ofAlgebraData_xGlued_congr_of_tower hI A g τ τ_symm σ hστ hσc τ' τ'_symm σ' hστ' hσc' hτ hσ

end AwayBase

end AffineChartedFibreDatumX

end AlgebraicGeometry
