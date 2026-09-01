import FormalSchemes.GeneralFibreProductExposeXAlgebraData
import FormalSchemes.TateOverlapTransitionAlg

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The Tate curve model as an `AffineChartedFibreDatumX`

Fix an adic base `(R, I)` with `I` finitely generated and Noetherian `R`, and a Tate parameter
`q ∈ I`. Let `A = R{x, y}/(x·y − q)` be the coordinate ring of the formal Tate annulus. The Tate
curve model `𝔈_q` (`FormalSchemes.TateCurveModel`) is two copies of `Spf A` glued along the
𝔾m-inversion, in the shape of a `LocallyRingedSpace` glue datum. This file re-presents that data in
the shape the general §10.15 machinery consumes, namely
`AlgebraicGeometry.AffineChartedFibreDatumX`, via the smart constructor
`AffineChartedFibreDatumX.ofAlgebraData` (`FormalSchemes.GeneralFibreProductExposeXAlgebraData`).

Three inputs make this possible, all of them recently landed:

* **601a** (`FormalSchemes.BasicOpenDisjointUnion`) — the two-chart overlap `D(x) ⊔ D(y)` is the
  *single* basic open `D(x + y)`. So the datum's away element is `g i j = x + y` for **both**
  ordered pairs, which is what lets a `ULift Bool`-indexed datum describe a *circular* gluing.
* **644** (`FormalSchemes.TateAwaySplit`) — the corresponding ring splitting
  `A{1/(x+y)}^ ≃ₐ[R] A{1/x}^ × A{1/y}^`.
* **672** (`FormalSchemes.TateOverlapTransitionAlg`) — the transition automorphism
  `tateOverlapTransitionAlg` of `A{1/(x+y)}^` (the twisted swap of the two summands, conjugated by
  the splitting) and its involution law.

## What is delivered, and what is *not* claimed

The datum below has, by construction, the charts, overlaps and transitions of `tateCurveGlueData'`.
It is **not** proved here that its glued object `xGlued` is isomorphic to `tateCurveModel` — that
comparison is a separate piece of work (601's brick 4), and it is where the *direction* of the
transition is finally pinned against the geometry. Nothing in this file should be read as asserting
`xGlued ≅ 𝔈_q`.

## The ideal-convention bridge

`AffineChartedFibreDatum.τ` is stated over the ideal `I.map (algebraMap R (A i))`, whereas 672's
transition is stated over `annulusIdealOfDefinition R I q`. The two ideals are equal
(`annulus_map_eq`) but not syntactically, so the completions are *different types*.
`annulusFibreChartBridgeXY` is the `AdicCompletion.congrIdealₐ` transport between them, exactly
mirroring `annulusFibreChartBridgeX`/`_Y` (`FormalSchemes.TwoPatchFibreProductObject`). Being
`subst`-built, it is composed and never projected at an element.

## Non-vacuity

On `ULift Bool` no triple of indices is pairwise distinct, so the double-overlap fields `σ`, `hστ`,
`hσc` — and hence both derived geometric triples `t'` and `xt'` — are `False.elim`s. The datum type
is therefore inhabited for trivial reasons, and *all* of the content sits in `g` and `τ`. Worse,
since `A i = A j` and `g i j = g j i`, the `τ` binder has the **same type** on both sides, so the
elaborator would have accepted the identity. `tateCurveExposeXDatum_τ` and
`tateCurveExposeXDatum_g` pin both down, and `annulusFibreOverlapTransitionAlg_apply` unwinds the
bridge, reducing the datum's `τ` to 672's `tateOverlapTransitionAlg` — which in turn has its own
computation rule `tateOverlapTransitionAlg_apply` exhibiting it as the twisted swap of the two
𝔾m-summands. So the chain from the datum field down to the geometry is unbroken, and the identity
is excluded.

## Main definitions and results

* `AlgebraicGeometry.annulusFibreChartBridgeXY`: the ideal-convention bridge at `x + y`.
* `AlgebraicGeometry.annulusFibreOverlapTransitionAlg`: 672's transition in the `I.map` convention,
  with `annulusFibreOverlapTransitionAlg_symm` (it is an involution) and
  `annulusFibreOverlapTransitionAlg_apply`.
* `AlgebraicGeometry.tateCurveExposeXDatum`: the datum, and `tateCurveExposeXGlued` /
  `tateCurveExposeXFibreProduct` for its derived objects.
* `AlgebraicGeometry.tateCurveExposeXDatum_g`, `tateCurveExposeXDatum_τ`: non-vacuity.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
-/

noncomputable section

open FormalSpectrum

universe u

namespace AlgEquiv

/-- **A conjugate, evaluated.** For `E : X ≃ₐ[R] Y` and `P : Y ≃ₐ[R] Y` the automorphism
`E ≫ P ≫ E⁻¹` of `X` sends `x` to `E⁻¹ (P (E x))`.

The equation is `rfl`, but it must be stated **generically**: at the concrete completions of this
file the same `rfl` first exhausts `maxRecDepth` and then, once the definitions are unfolded by
`simp`, OOM-kills the build. Stated at abstract types the kernel checks it once and the
instantiation is free. This is the same measure as `AlgEquiv.prodTwist_conj_apply`
(`FormalSchemes.TateOverlapTransitionAlg`) and the same lesson as issues 609 and 636. -/
theorem trans_trans_symm_apply {R X Y : Type u} [CommSemiring R] [Semiring X] [Semiring Y]
    [Algebra R X] [Algebra R Y] (E : X ≃ₐ[R] Y) (P : Y ≃ₐ[R] Y) (x : X) :
    ((E.trans P).trans E.symm) x = E.symm (P (E x)) :=
  rfl

end AlgEquiv

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-! ### The ideal-convention bridge at `x + y` -/

/-- **The ideal-convention bridge on the two-chart overlap.** `A{1/(x+y)}^` presented over
`I.map (algebraMap R A)` is identified as an `R`-algebra with the same completion presented over
`annulusIdealOfDefinition`, via `annulus_map_eq`.

This is the `x + y` analogue of `annulusFibreChartBridgeX` / `annulusFibreChartBridgeY`
(`FormalSchemes.TwoPatchFibreProductObject`). Like them it is an `AdicCompletion.congrIdealₐ`, so
the ideal transport is `subst`-built and never has to be projected at a point. -/
def annulusFibreChartBridgeXY :
    awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapX R I q + overlapY R I q) ≃ₐ[R]
      awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q + overlapY R I q) :=
  AdicCompletion.congrIdealₐ R
    (congrArg (Ideal.map (algebraMap (annulusAlgebra R I q)
      (Localization.Away (overlapX R I q + overlapY R I q)))) (annulus_map_eq R I q))

/-! ### The transition in the `I.map (algebraMap R A)` convention -/

/-- **The chart transition of the Tate two-chart overlap, over the `I.map (algebraMap R A)` ideal
convention** that `AffineChartedFibreDatum` uses: 672's `tateOverlapTransitionAlg` conjugated by the
bridge.

Because the overlap of the two charts of `𝔈_q` is the *single* basic open `D(x + y)` (601a), this
one `R`-algebra automorphism is the whole of the datum's `τ`, for both ordered pairs of
`ULift Bool`. -/
def annulusFibreOverlapTransitionAlg (hq : q ∈ I) (hI : I.FG) :
    awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapX R I q + overlapY R I q) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapX R I q + overlapY R I q) :=
  ((annulusFibreChartBridgeXY R I q).trans (tateOverlapTransitionAlg R I q hq hI)).trans
    (annulusFibreChartBridgeXY R I q).symm

/-- **The bridged transition is still an involution**, which is what the datum's `τ_symm` field
consumes. Conjugation preserves involutions
(`AlgEquiv.symm_trans_trans_symm_of_symm_eq`, stated generically in 672's file for exactly this
step), and the inner map is one by `tateOverlapTransitionAlg_symm`. -/
theorem annulusFibreOverlapTransitionAlg_symm (hq : q ∈ I) (hI : I.FG) :
    (annulusFibreOverlapTransitionAlg R I q hq hI).symm =
      annulusFibreOverlapTransitionAlg R I q hq hI :=
  AlgEquiv.symm_trans_trans_symm_of_symm_eq _ _ (tateOverlapTransitionAlg_symm R I q hq hI)

/-- **The computation rule**: unwinding the bridge, the transition is 672's
`tateOverlapTransitionAlg`. Chained with that map's own computation rule
(`tateOverlapTransitionAlg_apply`, which exhibits it as the twisted swap of the two 𝔾m-summands
under the splitting) and with `tateCurveExposeXDatum_τ`, this is what rules out the datum's `τ`
being the identity — see the module docstring. -/
theorem annulusFibreOverlapTransitionAlg_apply (hq : q ∈ I) (hI : I.FG)
    (s : awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
      (overlapX R I q + overlapY R I q)) :
    annulusFibreOverlapTransitionAlg R I q hq hI s =
      (annulusFibreChartBridgeXY R I q).symm
        (tateOverlapTransitionAlg R I q hq hI (annulusFibreChartBridgeXY R I q s)) :=
  AlgEquiv.trans_trans_symm_apply _ _ s

/-! ### The datum -/

variable (B : Type u) [CommRing B] [Algebra R B]

/-- **The Tate curve model presented as an `AffineChartedFibreDatumX`.** Two charts, both
`Spf A` with `A = R{x, y}/(x·y − q)`; the overlap of the two is the single basic open `D(x + y)`
(601a); and the transition is the 𝔾m-inversion twisted swap of 672, bridged to the
`I.map (algebraMap R A)` ideal convention.

The double-overlap data `σ`, `hστ`, `hσc` are vacuous on a two-element index type, so the content
is exactly `g` and `τ` — see `tateCurveExposeXDatum_g` and `tateCurveExposeXDatum_τ`.

**This does not claim `xGlued ≅ tateCurveModel`.** The charts, overlaps and transitions match
`tateCurveGlueData'` by construction, but the comparison of glued objects is separate work
(601's brick 4). -/
def tateCurveExposeXDatum (hq : q ∈ I) (hI : I.FG) [IsNoetherianRing R] :
    AffineChartedFibreDatumX R I hI B :=
  AffineChartedFibreDatumX.ofAlgebraData hI
    (A := fun _ : ULift.{u} Bool => annulusAlgebra R I q)
    (g := fun _ _ => overlapX R I q + overlapY R I q)
    (topology := fun _ => annulusTopologicalSpace R I q)
    (isAdic := fun _ => annulus_map_eq R I q ▸ annulus_isAdicRing R I q hI)
    (τ := fun _ _ _ => annulusFibreOverlapTransitionAlg R I q hq hI)
    (τ_symm := fun _ _ _ => (annulusFibreOverlapTransitionAlg_symm R I q hq hI).symm)
    (σ := fun _ _ _ hij hik hjk => (uliftBool_not_pairwise_distinct hij hik hjk).elim)
    (hστ := fun _ _ _ hij hik hjk => (uliftBool_not_pairwise_distinct hij hik hjk).elim)
    (hσc := fun _ _ _ hij hik hjk => (uliftBool_not_pairwise_distinct hij hik hjk).elim)

/-- **The glued formal scheme** of the Tate datum. Not yet known to be `𝔈_q` — see brick 4. -/
def tateCurveExposeXGlued (hq : q ∈ I) (hI : I.FG) [IsNoetherianRing R] : FormalScheme.{u} :=
  (tateCurveExposeXDatum R I q B hq hI).xGlued

/-- **The fibre product** `X ×_{Spf R} Spf B` of the Tate datum. -/
def tateCurveExposeXFibreProduct (hq : q ∈ I) (hI : I.FG) [IsNoetherianRing R] :
    FormalScheme.{u} :=
  (tateCurveExposeXDatum R I q B hq hI).fibreProduct

/-! ### Non-vacuity -/

/-- **The away element is `x + y` for every ordered pair.** This is 601a's content entering the
datum: the two-chart overlap is a single basic open, which is what allows a *circular* two-chart
gluing to be described by a `ULift Bool`-indexed datum at all. -/
theorem tateCurveExposeXDatum_g (hq : q ∈ I) (hI : I.FG) [IsNoetherianRing R]
    (i j : ULift.{u} Bool) :
    (tateCurveExposeXDatum R I q B hq hI).g i j = overlapX R I q + overlapY R I q :=
  rfl

/-- **The transition is the bridged 𝔾m-inversion twisted swap**, at both ordered pairs — not the
identity, which the elaborator would equally have accepted, since `A i = A j` and `g i j = g j i`
make the two sides of the `τ` binder the *same* type. -/
theorem tateCurveExposeXDatum_τ (hq : q ∈ I) (hI : I.FG) [IsNoetherianRing R]
    (i j : ULift.{u} Bool) (h : i ≠ j) :
    (tateCurveExposeXDatum R I q B hq hI).τ i j h =
      annulusFibreOverlapTransitionAlg R I q hq hI :=
  rfl

end AlgebraicGeometry

end
