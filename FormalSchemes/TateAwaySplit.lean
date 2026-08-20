import FormalSchemes.AdicCompletionAwayTrans
import FormalSchemes.AdicCompletionSplitAway
import FormalSchemes.TateOverlapDisjoint

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000

/-!
# The Tate annulus overlap splits: `A{1/(x+y)}^ ≃ₐ[R] A{1/x}^ × A{1/y}^`

Fix an adic base `(R, I)` with `q ∈ I`, and let `A = R{x, y}/(x·y − q)` be the coordinate ring of
the formal Tate annulus, with ideal of definition `J = I·A`. The two overlap coordinates satisfy
`x · y = q ∈ J`, so on the formal spectrum the basic open `D(x + y)` is the *disjoint* union
`D(x) ⊔ D(y)` (issue 601a, `FormalSchemes.BasicOpenDisjointUnion`). This file proves the ring-level
counterpart:

```
A{1/(x+y)}^  ≃ₐ[R]  A{1/x}^ × A{1/y}^ .
```

Nothing here is new mathematics — both ingredients are already general theorems on `master`, and
this file is their instantiation at the Tate annulus:

* `RingSplit.adicAwaySplitEquiv` (`FormalSchemes.AdicCompletionSplitAway`, issue 603/601b) splits
  `AdicCompletion K B` as a product of two completed localizations as soon as `f + g` is a unit
  and `f · g ∈ K`. Applied with `B := L = A{1/(x+y)}` and `f, g` the images of `x, y`, its
  left-hand side is *definitionally* `awayCompletion J (x + y)`, but its factors are completions of
  the **iterated** localizations `(A_{x+y})_{x̄}` rather than of `A_x`.
* `RingSplit.adicAwayTransEquiv'` (`FormalSchemes.AdicCompletionAwayTrans`, issue 631/618a) closes
  that gap: inverting `x + y` in addition to `x` does not change the completion, because
  `D(x) ⊆ D(x + y)` holds in the **formal** spectrum. This is where the geometry enters, and it is
  the only hypothesis with content — see `RingSplit.isUnit_mk_add_of_mul_mem` below.

Note that `D(x) ⊆ D(x + y)` fails in `Spec A`: `x + y = x · (1 + q/x²)` and `q/x²` is only
*topologically* nilpotent, so `x + y` is not a unit in `A_x` and the `Spec`-level transitivity
`FormalSpectrum.awayCompletionAwayEquiv` does not apply. That is exactly why issue 631 exists.

## Main definitions and results

* `RingSplit.isUnit_mk_add_of_mul_mem`: the general form of the one hypothesis with content — if
  `a` is invertible in `S` and `a · b` lies in `J`, then `a + b` is invertible in `S ⧸ J·S`.
* `AdicCompletion.congrIdeal_of`: the ideal transport fixes the image of the base ring.
* `AlgebraicGeometry.TateAwaySplit.awaySplitEquiv` and `awaySplitAlgEquiv`: the splitting, as a
  `≃+*` and as an `≃ₐ[R]`, with the computation rules `awaySplitEquiv_of` / `awaySplitAlgEquiv_of`
  on the image of `A`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1, §10.8.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9 (the Tate curve).
-/

noncomputable section

open FormalSpectrum

universe u

namespace RingSplit

/-- **`a + b` is invertible modulo `J·S` as soon as `a` is invertible in `S` and `a · b ∈ J`.**

Geometrically: in the formal spectrum `Spf (S, J·S)` the basic opens `D(a)` and `D(b)` are
disjoint, because `a · b` dies in the residue ring; so on `D(a)` the element `b` vanishes and
`a + b` agrees with the unit `a`. This is the hypothesis `adicAwayTransEquiv'` consumes, and at the
Tate annulus it is the whole geometric content of the splitting: `x · y = q` lies in the ideal of
definition. -/
theorem isUnit_mk_add_of_mul_mem {A : Type u} [CommRing A] (J : Ideal A) (a b : A)
    (hab : a * b ∈ J) (S : Type u) [CommRing S] [Algebra A S]
    (ha : IsUnit (algebraMap A S a)) :
    IsUnit (Ideal.Quotient.mk (J.map (algebraMap A S)) (algebraMap A S (a + b))) := by
  have hA : IsUnit (Ideal.Quotient.mk (J.map (algebraMap A S)) (algebraMap A S a)) := ha.map _
  have hzero : Ideal.Quotient.mk (J.map (algebraMap A S)) (algebraMap A S a) *
      Ideal.Quotient.mk (J.map (algebraMap A S)) (algebraMap A S b) = 0 := by
    rw [← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hab
  rw [map_add, map_add, hA.mul_right_eq_zero.mp hzero, add_zero]
  exact hA

end RingSplit

namespace AdicCompletion

/-- **The ideal transport fixes the image of the base ring.** `congrIdeal` is `subst`-built, so
this is `rfl` after the substitution; it is what turns a computation rule stated for one spelling
of the ideal into one for the other. -/
theorem congrIdeal_of {B : Type u} [CommRing B] {K₁ K₂ : Ideal B} (h : K₁ = K₂) (b : B) :
    congrIdeal h (of K₁ B b) = of K₂ B b := by
  subst h; rfl

end AdicCompletion

namespace AlgebraicGeometry

namespace TateAwaySplit

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-! ### The three localizations of the annulus involved -/

/-- `L = A{1/(x + y)}`, the *uncompleted* localization of the Tate annulus at `x + y`. Its
completion is the overlap `awayCompletion J (x + y)` being split. -/
abbrev overlapLoc : Type u :=
  Localization.Away (overlapX R I q + overlapY R I q)

/-- The image of `x` in `L`; the first of the two elements `adicAwaySplitEquiv` splits along. -/
abbrev overlapLocX : overlapLoc R I q :=
  algebraMap (annulusAlgebra R I q) (overlapLoc R I q) (overlapX R I q)

/-- The image of `y` in `L`. -/
abbrev overlapLocY : overlapLoc R I q :=
  algebraMap (annulusAlgebra R I q) (overlapLoc R I q) (overlapY R I q)

/-- The iterated localization `L_{x̄} = (A{1/(x+y)}){1/x}`, which is what the splitting theorem
produces on the `x` side. It is a localization of `A` away from `(x + y) · x`, hence the
formal-transitivity theorem identifies its completion with that of `A_x`. -/
abbrev locX : Type u := Localization.Away (overlapLocX R I q)

/-- The iterated localization `L_{ȳ}` on the `y` side. -/
abbrev locY : Type u := Localization.Away (overlapLocY R I q)

/-! ### The two hypotheses of the splitting theorem -/

/-- The Tate parameter lies in the ideal of definition of the annulus. -/
theorem algebraMap_q_mem (hq : q ∈ I) :
    algebraMap R (annulusAlgebra R I q) q ∈ annulusIdealOfDefinition R I q := by
  rw [← annulus_map_eq]
  exact Ideal.mem_map_of_mem _ hq

/-- **`x · y` lies in the ideal of definition**, since it *is* the Tate parameter
(`overlapX_mul_overlapY`). This single fact powers both hypotheses below and the level-`1`
invertibility of `x + y` in each chart. -/
theorem overlapX_mul_overlapY_mem (hq : q ∈ I) :
    overlapX R I q * overlapY R I q ∈ annulusIdealOfDefinition R I q := by
  rw [overlapX_mul_overlapY]
  exact algebraMap_q_mem R I q hq

/-- `x + y` is a unit in `L` — that is what `L` is. -/
theorem isUnit_overlapLoc_add :
    IsUnit (overlapLocX R I q + overlapLocY R I q) := by
  have h : IsUnit (algebraMap (annulusAlgebra R I q) (overlapLoc R I q)
      (overlapX R I q + overlapY R I q)) := IsLocalization.Away.algebraMap_isUnit _
  simpa only [map_add] using h

/-- `x · y` lies in the extension `J·L` of the ideal of definition. -/
theorem overlapLoc_mul_mem (hq : q ∈ I) :
    overlapLocX R I q * overlapLocY R I q ∈
      (annulusIdealOfDefinition R I q).map
        (algebraMap (annulusAlgebra R I q) (overlapLoc R I q)) := by
  rw [← map_mul]
  exact Ideal.mem_map_of_mem _ (overlapX_mul_overlapY_mem R I q hq)

/-! ### The splitting, before the factors are recognised -/

/-- **The splitting of the overlap**, straight from `RingSplit.adicAwaySplitEquiv`. The source is
definitionally `awayCompletion J (x + y)`; the factors are still completions of the iterated
localizations `L_{x̄}`, `L_{ȳ}`. -/
def rawSplitEquiv (hq : q ∈ I) :
    awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q + overlapY R I q) ≃+*
      AdicCompletion (RingSplit.awayIdeal
          ((annulusIdealOfDefinition R I q).map
            (algebraMap (annulusAlgebra R I q) (overlapLoc R I q)))
          (overlapLocX R I q)) (locX R I q) ×
        AdicCompletion (RingSplit.awayIdeal
          ((annulusIdealOfDefinition R I q).map
            (algebraMap (annulusAlgebra R I q) (overlapLoc R I q)))
          (overlapLocY R I q)) (locY R I q) :=
  RingSplit.adicAwaySplitEquiv _ (isUnit_overlapLoc_add R I q) (overlapLoc_mul_mem R I q hq)

/-! ### Recognising the factors -/

/-- The two spellings of the ideal of definition of `L_{x̄}` — extended in two steps along
`A → L → L_{x̄}`, or in one step along `A → L_{x̄}` — agree. -/
theorem awayIdeal_eq_locX :
    RingSplit.awayIdeal
        ((annulusIdealOfDefinition R I q).map
          (algebraMap (annulusAlgebra R I q) (overlapLoc R I q)))
        (overlapLocX R I q) =
      (annulusIdealOfDefinition R I q).map
        (algebraMap (annulusAlgebra R I q) (locX R I q)) := by
  rw [RingSplit.awayIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]

/-- The `y`-side companion of `awayIdeal_eq_locX`. -/
theorem awayIdeal_eq_locY :
    RingSplit.awayIdeal
        ((annulusIdealOfDefinition R I q).map
          (algebraMap (annulusAlgebra R I q) (overlapLoc R I q)))
        (overlapLocY R I q) =
      (annulusIdealOfDefinition R I q).map
        (algebraMap (annulusAlgebra R I q) (locY R I q)) := by
  rw [RingSplit.awayIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]

/-- **`x + y` is invertible in the residue ring of the chart `A{1/x}`.** This is the level-`1`
hypothesis of `adicAwayTransEquiv'`, i.e. the statement `D(x) ⊆ D(x + y)` on the underlying space
of the formal spectrum. It holds because `x · y = q` dies in the residue ring, so `y` does too. -/
theorem isUnit_mk_add_locX (hq : q ∈ I) :
    IsUnit (Ideal.Quotient.mk
      ((annulusIdealOfDefinition R I q).map
        (algebraMap (annulusAlgebra R I q) (Localization.Away (overlapX R I q))))
      (algebraMap (annulusAlgebra R I q) (Localization.Away (overlapX R I q))
        (overlapX R I q + overlapY R I q))) :=
  RingSplit.isUnit_mk_add_of_mul_mem _ _ _ (overlapX_mul_overlapY_mem R I q hq) _
    (IsLocalization.Away.algebraMap_isUnit _)

/-- The `y`-side companion of `isUnit_mk_add_locX`: `D(y) ⊆ D(x + y)`. -/
theorem isUnit_mk_add_locY (hq : q ∈ I) :
    IsUnit (Ideal.Quotient.mk
      ((annulusIdealOfDefinition R I q).map
        (algebraMap (annulusAlgebra R I q) (Localization.Away (overlapY R I q))))
      (algebraMap (annulusAlgebra R I q) (Localization.Away (overlapY R I q))
        (overlapX R I q + overlapY R I q))) := by
  rw [add_comm]
  exact RingSplit.isUnit_mk_add_of_mul_mem _ _ _
    (by rw [mul_comm]; exact overlapX_mul_overlapY_mem R I q hq) _
    (IsLocalization.Away.algebraMap_isUnit _)

/-- **Inverting `x + y` on top of `x` does not change the completion**: the `x`-side instance of
issue 631's formal transitivity. -/
def transEquivX (hq : q ∈ I) :
    awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q) ≃+*
      AdicCompletion
        ((annulusIdealOfDefinition R I q).map
          (algebraMap (annulusAlgebra R I q) (locX R I q))) (locX R I q) :=
  RingSplit.adicAwayTransEquiv' _ (overlapX R I q + overlapY R I q) (overlapX R I q)
    (Localization.Away (overlapX R I q)) (locX R I q) (isUnit_mk_add_locX R I q hq)

/-- The `y`-side companion of `transEquivX`. -/
def transEquivY (hq : q ∈ I) :
    awayCompletion (annulusIdealOfDefinition R I q) (overlapY R I q) ≃+*
      AdicCompletion
        ((annulusIdealOfDefinition R I q).map
          (algebraMap (annulusAlgebra R I q) (locY R I q))) (locY R I q) :=
  RingSplit.adicAwayTransEquiv' _ (overlapX R I q + overlapY R I q) (overlapY R I q)
    (Localization.Away (overlapY R I q)) (locY R I q) (isUnit_mk_add_locY R I q hq)

/-! ### The splitting -/

/-- **The Tate overlap splits.** The completed localization of the Tate annulus at `x + y` is the
product of those at `x` and at `y`:

```
A{1/(x+y)}^  ≃+*  A{1/x}^ × A{1/y}^ ,
```

the ring-level counterpart of `D(x + y) = D(x) ⊔ D(y)` on the formal spectrum (issue 601a). -/
def awaySplitEquiv (hq : q ∈ I) :
    awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q + overlapY R I q) ≃+*
      awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q) ×
        awayCompletion (annulusIdealOfDefinition R I q) (overlapY R I q) :=
  (rawSplitEquiv R I q hq).trans
    (RingEquiv.prodCongr
      ((AdicCompletion.congrIdeal (awayIdeal_eq_locX R I q)).trans (transEquivX R I q hq).symm)
      ((AdicCompletion.congrIdeal (awayIdeal_eq_locY R I q)).trans (transEquivY R I q hq).symm))

/-- **The splitting is the pair of canonical maps on the image of `A`.** This is the computation
rule a geometric consumer needs: it identifies the two components with the chart maps. -/
theorem awaySplitEquiv_of (hq : q ∈ I) (a : annulusAlgebra R I q) :
    awaySplitEquiv R I q hq
        (AdicCompletion.of _ (overlapLoc R I q)
          (algebraMap (annulusAlgebra R I q) (overlapLoc R I q) a)) =
      (AdicCompletion.of _ (Localization.Away (overlapX R I q))
          (algebraMap (annulusAlgebra R I q) (Localization.Away (overlapX R I q)) a),
        AdicCompletion.of _ (Localization.Away (overlapY R I q))
          (algebraMap (annulusAlgebra R I q) (Localization.Away (overlapY R I q)) a)) := by
  have hX : (transEquivX R I q hq)
      (AdicCompletion.of _ (Localization.Away (overlapX R I q))
        (algebraMap (annulusAlgebra R I q) (Localization.Away (overlapX R I q)) a)) =
      AdicCompletion.of _ (locX R I q)
        (algebraMap (annulusAlgebra R I q) (locX R I q) a) := by
    rw [transEquivX, RingSplit.adicAwayTransEquiv'_of, RingSplit.awayTransHom_algebraMap]
  have hY : (transEquivY R I q hq)
      (AdicCompletion.of _ (Localization.Away (overlapY R I q))
        (algebraMap (annulusAlgebra R I q) (Localization.Away (overlapY R I q)) a)) =
      AdicCompletion.of _ (locY R I q)
        (algebraMap (annulusAlgebra R I q) (locY R I q) a) := by
    rw [transEquivY, RingSplit.adicAwayTransEquiv'_of, RingSplit.awayTransHom_algebraMap]
  rw [awaySplitEquiv, RingEquiv.trans_apply, rawSplitEquiv, RingSplit.adicAwaySplitEquiv_of,
    RingEquiv.prodCongr_apply, Prod.map_apply, RingEquiv.trans_apply, RingEquiv.trans_apply,
    AdicCompletion.congrIdeal_of, AdicCompletion.congrIdeal_of,
    ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    ← hX, ← hY, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]

/-- **The splitting is `R`-linear.** The `R`-algebra structure on each side is the structural one
through `A`, and the computation rule `awaySplitEquiv_of` at `a = algebraMap R A r` is exactly the
`commutes'` obligation — the algebra maps on all three completions are `AdicCompletion.of` of the
structural image of `R`, definitionally.

This is the form issue 618 asks for, and the form `AffineChartedFibreDatumX` will consume. -/
def awaySplitAlgEquiv (hq : q ∈ I) :
    awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q + overlapY R I q) ≃ₐ[R]
      awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q) ×
        awayCompletion (annulusIdealOfDefinition R I q) (overlapY R I q) :=
  AlgEquiv.ofRingEquiv (f := awaySplitEquiv R I q hq) fun r =>
    awaySplitEquiv_of R I q hq (algebraMap R (annulusAlgebra R I q) r)

@[simp]
theorem awaySplitAlgEquiv_toRingEquiv (hq : q ∈ I) :
    (awaySplitAlgEquiv R I q hq).toRingEquiv = awaySplitEquiv R I q hq := rfl

/-- The computation rule, in the `≃ₐ[R]` spelling. -/
theorem awaySplitAlgEquiv_of (hq : q ∈ I) (a : annulusAlgebra R I q) :
    awaySplitAlgEquiv R I q hq
        (AdicCompletion.of _ (overlapLoc R I q)
          (algebraMap (annulusAlgebra R I q) (overlapLoc R I q) a)) =
      (AdicCompletion.of _ (Localization.Away (overlapX R I q))
          (algebraMap (annulusAlgebra R I q) (Localization.Away (overlapX R I q)) a),
        AdicCompletion.of _ (Localization.Away (overlapY R I q))
          (algebraMap (annulusAlgebra R I q) (Localization.Away (overlapY R I q)) a)) :=
  awaySplitEquiv_of R I q hq a

end TateAwaySplit

end AlgebraicGeometry

end
