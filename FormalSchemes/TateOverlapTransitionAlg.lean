import FormalSchemes.TateAwaySplit
import FormalSchemes.TateSelfProductTransitionInv

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000

/-!
# The `R`-algebra transition of the Tate two-chart overlap, presented as a single chart

Fix an adic base `(R, I)` with `I` finitely generated and a Tate parameter `q ∈ I`, and let
`A = R{x, y}/(x·y − q)` be the coordinate ring of the formal Tate annulus. `AffineChartedFibreDatum`
(`FormalSchemes.GeneralFibreProductAffineBase`) demands, for each ordered pair `i ≠ j` of charts, an
**`R`-algebra** transition between the two presentations of the double overlap. For the Tate curve
model `𝔈_q` the index type is `ULift Bool`, both chart algebras are `A`, and both ordered pairs have
the *same* away element `x + y` (601a: the two-chart overlap is the single basic open `D(x + y)`).
So the whole content of `τ` is one `R`-algebra **automorphism** of

```
S := awayCompletion (I·A) (x + y) ,
```

and `τ_symm` reduces to showing it is an involution. This file builds it.

## The construction

`FormalSchemes.TateAwaySplit` (644) splits the overlap, `S ≃ₐ[R] Sx × Sy` with
`Sx = awayCompletion (I·A) x` and `Sy = awayCompletion (I·A) y`. Under that splitting the glue
transition `t` of `tateCurveGlueData'`,

```
t = coprod.desc (annulusChartTransitionInvSpf.hom ≫ coprod.inr)
                (annulusChartTransitionInvSpf.inv ≫ coprod.inl) ,
```

carries the `x`-summand to the `y`-summand by the 𝔾m-inversion and the `y`-summand back to the
`x`-summand by its inverse. Pulling functions back (`Spf` is contravariant) this is the **twisted
swap**

```
(a, b)  ↦  (ι.symm b, ι a) ,      ι := annulusChartTransitionInvAlg : Sx ≃ₐ[R] Sy ,
```

which is visibly an involution. Conjugating it by the splitting gives `tateOverlapTransitionAlg`,
and `tateOverlapTransitionAlg_symm` is the conjugate of that involution.

### Which leg is which, and why this direction

The direction is pinned by `annulusChartTransitionInvSpf_hom_eq`
(`FormalSchemes.TateChartTransitionInvAlgEq`), which is *not* a naming choice but a proved equation:
`annulusChartTransitionInvSpf.hom` is the locally-ringed-space map induced by
`ι.symm.toRingHom : Sy →+* Sx`. Hence pulling a section `b : Sy` back along the `x`-summand leg
`hom ≫ inr` gives `ι.symm b : Sx`, and pulling `a : Sx` back along the `y`-summand leg
`inv ≫ inl` gives `ι a : Sy` — exactly the twisted swap above. Choosing `ι` where `ι.symm` belongs
would still produce an involution, so the compiler cannot catch a swap here; the equation above is
what rules it out.

## Main results

* `AlgEquiv.prodTwist`: the generic twisted swap `(a, b) ↦ (e.symm b, e a)` of `X × Y` attached to
  `e : X ≃ₐ[R] Y`, and `AlgEquiv.prodTwist_symm` — it is an involution.
* `AlgebraicGeometry.tateOverlapTransitionAlg`: the `R`-algebra automorphism of
  `awayCompletion (I·A) (x + y)`, with `tateOverlapTransitionAlg_apply` computing it through the
  splitting.
* `AlgebraicGeometry.tateOverlapTransitionAlg_symm`: it is an involution, which is what
  `AffineChartedFibreDatum`'s `τ_symm` field consumes on a two-element index type.

## Implementation notes

Everything generic is stated at abstract types and only then instantiated. The concrete completions
here are `AdicCompletion` of a localization of a quotient of a restricted-power-series ring, and
reducing such a type is what makes the kernel expensive in this tree (cf. the module notes in
`FormalSchemes.ThreeChartCoverCharts` and issue 636). In particular the involution law is proved
once, generically, as `AlgEquiv.symm_trans_trans_symm_of_symm_eq`.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
-/

noncomputable section

open FormalSpectrum

universe u

namespace AlgEquiv

section Generic

variable {R X Y : Type u} [CommSemiring R] [Semiring X] [Semiring Y] [Algebra R X] [Algebra R Y]

/-- The commutativity isomorphism `X × Y ≃ₐ[R] Y × X` of a product of `R`-algebras. Mathlib has
`RingEquiv.prodComm` but no `AlgEquiv` version; the `commutes'` obligation is `rfl`. -/
def prodComm : (X × Y) ≃ₐ[R] Y × X :=
  .ofRingEquiv (f := RingEquiv.prodComm) fun _ => rfl

@[simp]
theorem prodComm_apply (p : X × Y) : (prodComm : (X × Y) ≃ₐ[R] Y × X) p = p.swap := rfl

/-- **The twisted swap of `X × Y` attached to an isomorphism `e : X ≃ₐ[R] Y`**:
`(a, b) ↦ (e.symm b, e a)`. It exchanges the two factors and corrects the types with `e`, and it is
its own inverse (`prodTwist_symm`).

This is the algebraic shadow of a *circular* two-chart gluing: the transition sends the first
summand of the overlap to the second through `e` and the second back to the first through `e⁻¹`. -/
def prodTwist (e : X ≃ₐ[R] Y) : (X × Y) ≃ₐ[R] X × Y :=
  (prodComm : (X × Y) ≃ₐ[R] Y × X).trans (prodCongr e.symm e)

@[simp]
theorem prodTwist_apply (e : X ≃ₐ[R] Y) (p : X × Y) :
    prodTwist e p = (e.symm p.2, e p.1) := rfl

@[simp]
theorem prodTwist_symm_apply (e : X ≃ₐ[R] Y) (p : X × Y) :
    (prodTwist e).symm p = (e.symm p.2, e p.1) := rfl

/-- **The twisted swap is an involution.** Both `prodTwist e` and its inverse are
`(a, b) ↦ (e.symm b, e a)`, so the equality holds pointwise by `rfl`. -/
@[simp]
theorem prodTwist_symm (e : X ≃ₐ[R] Y) : (prodTwist e).symm = prodTwist e :=
  AlgEquiv.ext fun _ => rfl

end Generic

section Conjugate

variable {R X Y : Type u} [CommSemiring R] [Semiring X] [Semiring Y] [Algebra R X] [Algebra R Y]

/-- **An involution stays an involution after conjugation.** If `P : Y ≃ₐ[R] Y` satisfies
`P.symm = P` then so does `E ≫ P ≫ E⁻¹` for any `E : X ≃ₐ[R] Y`.

Stated generically and proved pointwise by `change`, so the kernel checks it once at abstract
types; instantiating it at the concrete completions of this file never unfolds them. -/
theorem symm_trans_trans_symm_of_symm_eq (E : X ≃ₐ[R] Y) (P : Y ≃ₐ[R] Y) (hP : P.symm = P) :
    ((E.trans P).trans E.symm).symm = (E.trans P).trans E.symm :=
  AlgEquiv.ext fun x => by
    change E.symm (P.symm (E x)) = E.symm (P (E x))
    rw [hP]

/-- **The conjugate of a twisted swap, computed.** For `E : S ≃ₐ[R] X × Y` and `e : X ≃ₐ[R] Y` the
automorphism `E ≫ prodTwist e ≫ E⁻¹` of `S` sends `s` to `E⁻¹ (e⁻¹ (E s).2, e (E s).1)`.

The equation is `rfl`, but it must be stated *generically*: checking the same `rfl` directly at a
concrete `AdicCompletion`-of-a-localization type exhausts `maxRecDepth`, whereas here the kernel
sees it once at abstract types and the instantiation is free. -/
theorem prodTwist_conj_apply {S : Type u} [Semiring S] [Algebra R S]
    (E : S ≃ₐ[R] X × Y) (e : X ≃ₐ[R] Y) (s : S) :
    ((E.trans (prodTwist e)).trans E.symm) s = E.symm (e.symm (E s).2, e (E s).1) :=
  rfl

end Conjugate

end AlgEquiv

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- **The transition of the Tate two-chart overlap, in split form.** Under the splitting
`awaySplitAlgEquiv : A{1/(x+y)}^ ≃ₐ[R] A{1/x}^ × A{1/y}^` the glue transition of `𝔈_q` is the
twisted swap attached to the 𝔾m-inversion chart transition `annulusChartTransitionInvAlg`. -/
abbrev tateOverlapProdTwist (hI : I.FG) :
    (awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q) ×
        awayCompletion (annulusIdealOfDefinition R I q) (overlapY R I q)) ≃ₐ[R]
      (awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q) ×
        awayCompletion (annulusIdealOfDefinition R I q) (overlapY R I q)) :=
  AlgEquiv.prodTwist (annulusChartTransitionInvAlg R I q hI)

/-- **The `R`-algebra chart transition of the Tate curve model's two-chart overlap.** The overlap of
the two charts of `𝔈_q` is the single basic open `D(x + y)` (601a), so the transition is an
`R`-algebra *automorphism* of `A{1/(x+y)}^`: the twisted swap of the two 𝔾m-summands, conjugated by
the splitting `awaySplitAlgEquiv` (644).

This is the `τ` field `AffineChartedFibreDatum` demands, for both ordered pairs of the two-element
index type `ULift Bool`. -/
def tateOverlapTransitionAlg (hq : q ∈ I) (hI : I.FG) :
    awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q + overlapY R I q) ≃ₐ[R]
      awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q + overlapY R I q) :=
  ((TateAwaySplit.awaySplitAlgEquiv R I q hq).trans (tateOverlapProdTwist R I q hI)).trans
    (TateAwaySplit.awaySplitAlgEquiv R I q hq).symm

/-- **The computation rule**: `tateOverlapTransitionAlg` read through the splitting is the twisted
swap. This is the form a consumer identifying it with the geometric transition will want; a rule on
the image of `A` is *not* available, and could not be — the 𝔾m-inversion does not fix the image of
`A` (it sends `x ↦ y⁻¹`), it is only `R`-linear. -/
theorem tateOverlapTransitionAlg_apply (hq : q ∈ I) (hI : I.FG)
    (s : awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q + overlapY R I q)) :
    tateOverlapTransitionAlg R I q hq hI s =
      (TateAwaySplit.awaySplitAlgEquiv R I q hq).symm
        ((annulusChartTransitionInvAlg R I q hI).symm
            ((TateAwaySplit.awaySplitAlgEquiv R I q hq) s).2,
          (annulusChartTransitionInvAlg R I q hI)
            ((TateAwaySplit.awaySplitAlgEquiv R I q hq) s).1) :=
  AlgEquiv.prodTwist_conj_apply _ _ s

/-- **The transition is an involution**, which is exactly what `AffineChartedFibreDatum`'s `τ_symm`
field consumes on the two-element index type `ULift Bool`: there `i ≠ j` forces
`{i, j} = {⟨false⟩, ⟨true⟩}`, so both ordered pairs carry the *same* automorphism and `τ_symm`
becomes `τ = τ⁻¹`.

Geometrically this is the statement that the Tate 2-gon's two gluings are inverse to each other:
going round the circle once in each direction returns to the start. -/
theorem tateOverlapTransitionAlg_symm (hq : q ∈ I) (hI : I.FG) :
    (tateOverlapTransitionAlg R I q hq hI).symm = tateOverlapTransitionAlg R I q hq hI :=
  AlgEquiv.symm_trans_trans_symm_of_symm_eq _ _
    (AlgEquiv.prodTwist_symm (annulusChartTransitionInvAlg R I q hI))

end AlgebraicGeometry
