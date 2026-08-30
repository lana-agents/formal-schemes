import FormalSchemes.TateInvGlobalSections
import FormalSchemes.TateChartTransitionInvAlgEq
import FormalSchemes.GraphCodiagonalClosedEmbedding

set_option linter.style.header false

/-!
# `Γ (T_inv/⟨σ⟩)` is a **proper** subring of `A = R{x, y}/(x·y − q)`

`FormalSchemes.TateInvGlobalSections` identifies `Γ (T_inv/⟨σ⟩)` with
`AlgebraicGeometry.tateInvGlobalSubring hI`, the elements of `A` on which two pairs of ring maps
agree, and leaves open whether that subring is proper — equivalently whether
`AlgebraicGeometry.tateInvGlobalLegX` and `AlgebraicGeometry.tateInvGlobalLegYX` are the same ring
map of `A`. **They are not**, as soon as `I ≠ ⊤`, and this file proves it by evaluating both on the
coordinate `x`.

## The computation

Read `A{1/x}` in `Ĝm` coordinates through `RestrictedLaurentSeries.overlapEquiv`
(`FormalSchemes.TateOverlap`), which sends `x ↦ X` and `y ↦ q·X⁻¹`. The `𝔾m`-inversion transition
`AlgebraicGeometry.annulusChartTransitionInvAlg` becomes `RestrictedLaurentSeries.rlsInv`,
`X ↦ X⁻¹`. So on the coordinate `x`:

* the `x`-chart leg reads as `X`;
* the transition-then-`y`-chart leg reads as `rlsInv (q·X⁻¹) = q·X`.

That is `tateInvGlobalLegYX_overlapX`: **the two forward legs differ on `x` by exactly the Tate
parameter**, `tateInvGlobalLegYX hI x = tateInvGlobalLegX (q·x)`. `tateInvGlobalLegXY_overlapY` is
the mirror on `y`, read through the `y`-side coordinate `annulusOverlapEquivY`.

Since `X` is a unit, `tateInvGlobalLegX = tateInvGlobalLegYX` forces `q = 1` in `R{X, X⁻¹}` and
hence, by `RestrictedLaurentSeries.algebraMap_injective`, in `R`. With `q ∈ I` that is `I = ⊤`.

## Main results

* `RestrictedLaurentSeries.algebraMap_injective`: for a complete adic ring, `R → R{X, X⁻¹}` is
  injective. Proved by evaluating at the unit `1`, i.e. by the point `X ↦ 1` of `Ĝm` valued in `R`
  itself. **General; it is here only to avoid rebuilding `FormalSchemes.FormalGm`.**
* `AlgebraicGeometry.tateInvGlobalLegYX_overlapX` and
  `AlgebraicGeometry.tateInvGlobalLegXY_overlapY`: the two pairs of legs differ by `q` on the two
  coordinates.
* `AlgebraicGeometry.eq_top_of_tateInvGlobalSubring_eq_top`: if the subring is all of `A` then
  `I = ⊤`.
* **`AlgebraicGeometry.tateInvGlobalSubring_ne_top`**: for `I ≠ ⊤` the subring is proper, and
  `AlgebraicGeometry.exists_notMem_tateInvGlobalSubring` exhibits the coordinate `x` as an element
  outside it.
* `AlgebraicGeometry.tateInvChartAnnulusSubring_univ_ne_top`: the same statement for
  `AlgebraicGeometry.tateInvChartAnnulusSubring` at `S = Set.univ`, i.e. **issue 1250's goal 2, in
  the affirmative, at the one `S` where it has an answer.**

## What is *not* proved

**That the subring is exactly the image of `R`.** The expected answer — the formal-geometry shadow
of properness of the Néron 1-gon — is that `Γ (T_inv/⟨σ⟩) ≃+* R`, and
`AlgebraicGeometry.algebraMap_mem_tateInvGlobalSubring` (`FormalSchemes.TateInvGlobalSections`) is
its easy half. This file proves the subring is **smaller than `A`**, not that it is **as small as
`R`**; the converse needs a coefficientwise argument in `R{X, X⁻¹}` and is not attempted.

**Issue 1223's goal 3 is untouched.** That asks for an element of the chart ring *outside* the
image of `Γ (Spf R, ·)`, i.e. that the ring is *bigger* than the base. Properness is that it is
*smaller* than the patch's sections. Neither implies the other, and this file settles only the
second, at `S = Set.univ`.

**Nothing here is a chart**, and nothing here says the quotient is a formal scheme. That is issue
1197.

**Nothing here is claimed at a general `S`.** `tateInvChartAnnulusSubring_empty_eq_top`
(`FormalSchemes.TateInvChartAnnulusRing`) shows the question has no `S`-free answer: at `S = ∅` the
ambient ring is the zero ring and the subring is `⊤`.

## References

* [Deligne–Rapoport, *Les schémas de modules de courbes elliptiques*], II.1 — the Néron `n`-gon.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1.3, §10.6.
-/
noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum RestrictedLaurentSeries

universe u

namespace RestrictedLaurentSeries

section Injective

variable {R : Type u} [CommRing R] {I : Ideal R}

/-- The extension of `I` along the identity of `R` is contained in `I` — the side condition
`RestrictedLaurentSeries.unitEval` needs to be evaluated in `R` itself. -/
theorem map_algebraMap_self_le : I.map (algebraMap R R) ≤ I := by
  rw [Algebra.algebraMap_self, Ideal.map_id]

variable [TopologicalSpace R] [IsAdicRing I]

/-- **Evaluating a constant at the unit `1` returns it.** The point `X ↦ 1` of `Ĝm` valued in `R`
itself; `R` is complete adic because `IsAdicRing` extends `IsAdicComplete`. -/
theorem unitEvalAlgHom_one_algebraMap (r : R) :
    haveI : IsAdicComplete I R := ‹IsAdicRing I›.toIsAdicComplete
    unitEvalAlgHom R I (S := R) I map_algebraMap_self_le 1
        (algebraMap R (RestrictedLaurentSeries R I) r) = r := by
  haveI : IsAdicComplete I R := ‹IsAdicRing I›.toIsAdicComplete
  rw [AlgHom.commutes]
  exact Algebra.algebraMap_self_apply r

/-- **`R → R{X, X⁻¹}` is injective for a complete adic ring**: the point `X ↦ 1` of `Ĝm` valued in
`R` retracts it. This is general and belongs beside `RestrictedLaurentSeries.isUnit_X` in
`FormalSchemes.FormalGm`; it is here because that file sits under the whole tree and moving it
would force a full rebuild. **Move it opportunistically.** -/
theorem algebraMap_injective :
    Function.Injective (algebraMap R (RestrictedLaurentSeries R I)) := by
  haveI : IsAdicComplete I R := ‹IsAdicRing I›.toIsAdicComplete
  intro r s h
  have := congrArg (unitEvalAlgHom R I (S := R) I map_algebraMap_self_le 1) h
  rwa [unitEvalAlgHom_one_algebraMap, unitEvalAlgHom_one_algebraMap] at this

end Injective

end RestrictedLaurentSeries


namespace AlgebraicGeometry

section Coordinates

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-! ### The two chart-domain identifications, read on the structural maps -/

/-- The `x`-chart identification carries the `x`-chart leg onto the structural map
`A → A[x⁻¹]^∧`. -/
theorem annulusChartOverlapAlgX_tateInvGlobalLegX (a : annulusAlgebra R I q) :
    annulusChartOverlapAlgX R I q (tateInvGlobalLegX (R := R) (I := I) (q := q) a) =
      algebraMap (annulusAlgebra R I q) (annulusOverlap R I q) a := by
  rw [tateInvGlobalLegX, FormalSpectrum.awayCompletionHom, RingHom.comp_apply,
    annulusChartOverlapAlgX, AdicCompletion.congrIdealₐ_algebraMap]
  exact (IsScalarTower.algebraMap_apply (annulusAlgebra R I q) (annulusLoc R I q)
    (annulusOverlap R I q) a).symm

/-- The `y`-chart identification carries the `y`-chart leg onto the structural map
`A → A[y⁻¹]^∧`. -/
theorem annulusChartOverlapAlgY_tateInvGlobalLegY (a : annulusAlgebra R I q) :
    annulusChartOverlapAlgY R I q (tateInvGlobalLegY (R := R) (I := I) (q := q) a) =
      algebraMap (annulusAlgebra R I q) (annulusOverlapY R I q) a := by
  rw [tateInvGlobalLegY, FormalSpectrum.awayCompletionHom, RingHom.comp_apply,
    annulusChartOverlapAlgY, AdicCompletion.congrIdealₐ_algebraMap]
  exact (IsScalarTower.algebraMap_apply (annulusAlgebra R I q) (annulusLocY R I q)
    (annulusOverlapY R I q) a).symm

/-- The `x`-chart identification turns the inverse chart transition into the inverse overlap
transition: unfold `AlgebraicGeometry.annulusChartTransitionInvAlg` and cancel the `x`-chart
identification. The final step is `rfl` because `annulusOverlapInversionAlg` is
`AlgEquiv.ofRingEquiv` of `annulusOverlapInversion`. -/
theorem annulusChartOverlapAlgX_annulusChartTransitionInvAlg_symm (hI : I.FG)
    (z : awayCompletion (annulusIdealOfDefinition R I q) (overlapY R I q)) :
    annulusChartOverlapAlgX R I q ((annulusChartTransitionInvAlg R I q hI).symm z) =
      (annulusOverlapInversion R I q hI).symm (annulusChartOverlapAlgY R I q z) := by
  rw [annulusChartTransitionInvAlg, AlgEquiv.symm_trans_apply, AlgEquiv.symm_trans_apply,
    AlgEquiv.symm_symm, AlgEquiv.apply_symm_apply]
  rfl

/-- The `y`-chart identification turns the chart transition into the overlap transition — the
mirror of `annulusChartOverlapAlgX_annulusChartTransitionInvAlg_symm`. -/
theorem annulusChartOverlapAlgY_annulusChartTransitionInvAlg (hI : I.FG)
    (z : awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q)) :
    annulusChartOverlapAlgY R I q (annulusChartTransitionInvAlg R I q hI z) =
      annulusOverlapInversion R I q hI (annulusChartOverlapAlgX R I q z) := by
  rw [annulusChartTransitionInvAlg, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    AlgEquiv.apply_symm_apply]
  rfl

/-! ### The coordinate swap and the inversion, on the structural maps -/

/-- The inverse flip transition intertwines the two structural maps through the coordinate swap:
`RingEquiv.symm_apply_eq` on `AlgebraicGeometry.annulusOverlapTransition_algebraMap_annulus`. -/
theorem annulusOverlapTransition_symm_algebraMap_annulus (hI : I.FG) (a : annulusAlgebra R I q) :
    (annulusOverlapTransition R I q hI).symm
        (algebraMap (annulusAlgebra R I q) (annulusOverlapY R I q) a) =
      algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)
        ((annulusFlip R I q hI).symm a) := by
  rw [RingEquiv.symm_apply_eq, annulusOverlapTransition_algebraMap_annulus,
    AlgEquiv.apply_symm_apply]

/-- The coordinate swap is an involution, so its inverse also sends `x` to `y`. -/
theorem annulusFlip_symm_overlapX (hI : I.FG) :
    (annulusFlip R I q hI).symm (overlapX R I q) = overlapY R I q := by
  rw [annulusFlip_symm_apply, ← annulusFlip_apply, annulusFlip_overlapX]

/-- The coordinate swap is an involution, so its inverse also sends `y` to `x`. -/
theorem annulusFlip_symm_overlapY (hI : I.FG) :
    (annulusFlip R I q hI).symm (overlapY R I q) = overlapX R I q := by
  rw [annulusFlip_symm_apply, ← annulusFlip_apply, annulusFlip_overlapY]

/-- Reading the inverse `𝔾m`-inversion transition on a structural image in `Ĝm` coordinates: it is
`RestrictedLaurentSeries.rlsInv` of the coordinate-swapped structural image. -/
theorem overlapEquiv_annulusOverlapInversion_symm_algebraMap (hI : I.FG)
    (a : annulusAlgebra R I q) :
    overlapEquiv R I q hI ((annulusOverlapInversion R I q hI).symm
        (algebraMap (annulusAlgebra R I q) (annulusOverlapY R I q) a)) =
      rlsInv R I hI (overlapEquiv R I q hI
        (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)
          ((annulusFlip R I q hI).symm a))) := by
  rw [annulusOverlapInversion_symm_apply, overlapEquiv_annulusOverlapInvX_symm,
    annulusOverlapTransition_symm_algebraMap_annulus]

/-- The overlap isomorphism is `R`-linear on the base. -/
theorem overlapEquiv_algebraMap_base (hI : I.FG) (r : R) :
    overlapEquiv R I q hI (algebraMap R (annulusOverlap R I q) r) =
      algebraMap R (RestrictedLaurentSeries R I) r := by
  rw [overlapEquiv_apply]
  exact (overlapHomAlg R I q hI).commutes r

/-- The overlap isomorphism sends the structural image of a scalar to that scalar. -/
theorem overlapEquiv_algebraMap_annulusAlgebra (hI : I.FG) (r : R) :
    overlapEquiv R I q hI (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)
        (algebraMap R (annulusAlgebra R I q) r)) =
      algebraMap R (RestrictedLaurentSeries R I) r := by
  rw [← IsScalarTower.algebraMap_apply R (annulusAlgebra R I q) (annulusOverlap R I q) r,
    overlapEquiv_algebraMap_base]

/-- The overlap isomorphism sends the structural image of the coordinate `y` to `q·X⁻¹`: the
`overlapY` spelling of `AlgebraicGeometry.overlapEquiv_annulusY`, which is stated at
`annulusMk (annulusY)`. The two are the same term, but `AlgebraicGeometry.overlapY` occurs inside
types below, so rewriting it is motive-incorrect and this restatement is what the rewrites need. -/
theorem overlapEquiv_algebraMap_overlapY (hI : I.FG) :
    overlapEquiv R I q hI (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)
        (overlapY R I q)) =
      algebraMap R (RestrictedLaurentSeries R I) q * X R I (-1) :=
  overlapEquiv_annulusY R I q hI

/-! ### The four global legs, evaluated on the two coordinates -/

/-- The transition-then-`y`-chart leg, unfolded: the inverse chart transition applied to the
`y`-chart leg. Stated on its own because the `RingHom.comp` and the `AlgEquiv` coercion have to be
discharged by `rfl` before any rewriting, and doing that inside a larger goal makes the kernel's
defeq check on this cluster time out — the trap `FormalSchemes.TateInvGlobalSections` records. -/
theorem tateInvGlobalLegYX_apply (hI : I.FG) (a : annulusAlgebra R I q) :
    tateInvGlobalLegYX (R := R) (I := I) (q := q) hI a =
      (annulusChartTransitionInvAlg R I q hI).symm
        (tateInvGlobalLegY (R := R) (I := I) (q := q) a) := by
  rw [tateInvGlobalLegYX, RingHom.comp_apply, tateInvGlobalLegY]
  rfl

/-- The inverse-transition-then-`x`-chart leg, unfolded. The mirror of
`tateInvGlobalLegYX_apply`. -/
theorem tateInvGlobalLegXY_apply (hI : I.FG) (a : annulusAlgebra R I q) :
    tateInvGlobalLegXY (R := R) (I := I) (q := q) hI a =
      annulusChartTransitionInvAlg R I q hI
        (tateInvGlobalLegX (R := R) (I := I) (q := q) a) := by
  rw [tateInvGlobalLegXY, RingHom.comp_apply, tateInvGlobalLegX]
  rfl

/-- The `x`-chart identification carries the transition-then-`y`-chart leg onto the inverse
overlap transition of the structural image. -/
theorem annulusChartOverlapAlgX_tateInvGlobalLegYX (hI : I.FG) (a : annulusAlgebra R I q) :
    annulusChartOverlapAlgX R I q (tateInvGlobalLegYX (R := R) (I := I) (q := q) hI a) =
      (annulusOverlapInversion R I q hI).symm
        (algebraMap (annulusAlgebra R I q) (annulusOverlapY R I q) a) := by
  rw [tateInvGlobalLegYX_apply, annulusChartOverlapAlgX_annulusChartTransitionInvAlg_symm,
    annulusChartOverlapAlgY_tateInvGlobalLegY]

/-- **The two forward legs differ on the coordinate `x` by exactly the Tate parameter.** In `Ĝm`
coordinates `tateInvGlobalLegX` sends `x` to `X` and `tateInvGlobalLegYX` sends it to
`rlsInv (q·X⁻¹) = q·X`, so the second leg at `x` is the first leg at `q·x`. -/
theorem tateInvGlobalLegYX_overlapX (hI : I.FG) :
    tateInvGlobalLegYX (R := R) (I := I) (q := q) hI (overlapX R I q) =
      tateInvGlobalLegX (R := R) (I := I) (q := q)
        (algebraMap R (annulusAlgebra R I q) q * overlapX R I q) := by
  refine (annulusChartOverlapAlgX R I q).injective ((overlapEquiv R I q hI).injective ?_)
  rw [annulusChartOverlapAlgX_tateInvGlobalLegYX,
    overlapEquiv_annulusOverlapInversion_symm_algebraMap, annulusFlip_symm_overlapX,
    overlapEquiv_algebraMap_overlapY, map_mul, rlsInv_algebraMap, rlsInv_X_neg_one,
    annulusChartOverlapAlgX_tateInvGlobalLegX, map_mul, map_mul,
    overlapEquiv_algebraMap_annulusAlgebra, overlapEquiv_overlapX]

/-! ### The `y`-side coordinate, and the mirror on `y` -/

/-- **The `y`-overlap in `Ĝm` coordinates**: the flip transition back to the `x`-overlap followed
by `RestrictedLaurentSeries.overlapEquiv`. It sends the coordinate `y` to `X`. -/
def annulusOverlapEquivY (hI : I.FG) :
    annulusOverlapY R I q ≃+* RestrictedLaurentSeries R I :=
  (annulusOverlapTransition R I q hI).symm.trans (overlapEquiv R I q hI)

theorem annulusOverlapEquivY_apply (hI : I.FG) (z : annulusOverlapY R I q) :
    annulusOverlapEquivY R I q hI z =
      overlapEquiv R I q hI ((annulusOverlapTransition R I q hI).symm z) := rfl

/-- The `y`-side coordinate reads a structural image through the coordinate swap. -/
theorem annulusOverlapEquivY_algebraMap (hI : I.FG) (a : annulusAlgebra R I q) :
    annulusOverlapEquivY R I q hI
        (algebraMap (annulusAlgebra R I q) (annulusOverlapY R I q) a) =
      overlapEquiv R I q hI (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)
        ((annulusFlip R I q hI).symm a)) := by
  rw [annulusOverlapEquivY_apply, annulusOverlapTransition_symm_algebraMap_annulus]

/-- The `y`-side coordinate reads the `𝔾m`-inversion transition as
`RestrictedLaurentSeries.rlsInv`, by
`AlgebraicGeometry.annulusOverlapInversion_annulusOverlapInvX`. -/
theorem annulusOverlapEquivY_annulusOverlapInversion (hI : I.FG) (z : annulusOverlap R I q) :
    annulusOverlapEquivY R I q hI (annulusOverlapInversion R I q hI z) =
      rlsInv R I hI (overlapEquiv R I q hI z) := by
  rw [annulusOverlapEquivY_apply, annulusOverlapInversion_apply,
    RingEquiv.symm_apply_apply, overlapEquiv_annulusOverlapInvX]

/-- The `y`-side coordinate sends the structural image of a scalar to that scalar. -/
theorem annulusOverlapEquivY_algebraMap_annulusAlgebra (hI : I.FG) (r : R) :
    annulusOverlapEquivY R I q hI (algebraMap (annulusAlgebra R I q) (annulusOverlapY R I q)
        (algebraMap R (annulusAlgebra R I q) r)) =
      algebraMap R (RestrictedLaurentSeries R I) r := by
  rw [annulusOverlapEquivY_algebraMap, AlgEquiv.commutes,
    overlapEquiv_algebraMap_annulusAlgebra]

/-- The `y`-side coordinate sends the structural image of the coordinate `y` to `X`. -/
theorem annulusOverlapEquivY_algebraMap_overlapY (hI : I.FG) :
    annulusOverlapEquivY R I q hI (algebraMap (annulusAlgebra R I q) (annulusOverlapY R I q)
        (overlapY R I q)) = X R I 1 := by
  rw [annulusOverlapEquivY_algebraMap, annulusFlip_symm_overlapY, overlapEquiv_overlapX]

/-- **The two backward legs differ on the coordinate `y` by exactly the Tate parameter** — the
mirror of `tateInvGlobalLegYX_overlapX`, read in the `y`-side coordinate. -/
theorem tateInvGlobalLegXY_overlapY (hI : I.FG) :
    tateInvGlobalLegXY (R := R) (I := I) (q := q) hI (overlapY R I q) =
      tateInvGlobalLegY (R := R) (I := I) (q := q)
        (algebraMap R (annulusAlgebra R I q) q * overlapY R I q) := by
  refine (annulusChartOverlapAlgY R I q).injective ((annulusOverlapEquivY R I q hI).injective ?_)
  rw [tateInvGlobalLegXY_apply, annulusChartOverlapAlgY_annulusChartTransitionInvAlg,
    annulusChartOverlapAlgX_tateInvGlobalLegX, annulusOverlapEquivY_annulusOverlapInversion,
    overlapEquiv_algebraMap_overlapY, map_mul, rlsInv_algebraMap, rlsInv_X_neg_one,
    annulusChartOverlapAlgY_tateInvGlobalLegY, map_mul, map_mul,
    annulusOverlapEquivY_algebraMap_annulusAlgebra, annulusOverlapEquivY_algebraMap_overlapY]

end Coordinates

/-! ### Properness -/

section Properness

variable {R : Type u} [CommRing R] {I : Ideal R} {q : R}
variable [TopologicalSpace R] [IsAdicRing I]

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **In `Ĝm` coordinates the forward condition on `x` reads `X = q·X`.** -/
theorem overlapEquiv_eq_of_overlapX_mem_tateInvGlobalSubring (hI : I.FG)
    (h : overlapX R I q ∈ tateInvGlobalSubring hI) :
    algebraMap R (RestrictedLaurentSeries R I) 1 * X R I 1 =
      algebraMap R (RestrictedLaurentSeries R I) q * X R I 1 := by
  have h1 := ((mem_tateInvGlobalSubring_iff hI _).1 h).1
  rw [tateInvGlobalLegYX_overlapX] at h1
  have h2 := congrArg
    (fun z => overlapEquiv R I q hI (annulusChartOverlapAlgX R I q z)) h1
  simp only [annulusChartOverlapAlgX_tateInvGlobalLegX] at h2
  rw [overlapEquiv_overlapX, map_mul, map_mul, overlapEquiv_algebraMap_annulusAlgebra,
    overlapEquiv_overlapX] at h2
  rw [map_one, one_mul]
  exact h2

/-- **If the coordinate `x` is a global section of the quotient then the Tate parameter is `1`.**
`X` is a unit in `R{X, X⁻¹}`, so `X = q·X` cancels to `1 = q` there, and
`RestrictedLaurentSeries.algebraMap_injective` brings that back to `R`. -/
theorem eq_one_of_overlapX_mem_tateInvGlobalSubring (hI : I.FG)
    (h : overlapX R I q ∈ tateInvGlobalSubring hI) : q = 1 :=
  (RestrictedLaurentSeries.algebraMap_injective
    ((isUnit_X R I 1).mul_right_cancel
      (overlapEquiv_eq_of_overlapX_mem_tateInvGlobalSubring hI h))).symm

/-- **The coordinate `x` is an explicit element of `A` outside `Γ (T_inv/⟨σ⟩)`**, whenever the
ideal of definition is proper. With `q ∈ I`, `q = 1` would put `1` in `I`. -/
theorem notMem_tateInvGlobalSubring_overlapX (hq : q ∈ I) (hI : I.FG) (hItop : I ≠ ⊤) :
    overlapX R I q ∉ tateInvGlobalSubring hI := fun h =>
  hItop ((Ideal.eq_top_iff_one I).2
    (eq_one_of_overlapX_mem_tateInvGlobalSubring hI h ▸ hq))

/-- **`Γ (T_inv/⟨σ⟩)` is a proper subring of `A = R{x, y}/(x·y − q)`**, for `I ≠ ⊤`: issue 1250's
goal 2 at `S = Set.univ`, in the affirmative. The overlap condition is a genuine restriction. -/
theorem tateInvGlobalSubring_ne_top (hq : q ∈ I) (hI : I.FG) (hItop : I ≠ ⊤) :
    tateInvGlobalSubring (R := R) (I := I) (q := q) hI ≠ ⊤ := fun h =>
  notMem_tateInvGlobalSubring_overlapX hq hI hItop (by rw [h]; exact Subring.mem_top _)

/-- The existential form of `tateInvGlobalSubring_ne_top`, with the witness named. -/
theorem exists_notMem_tateInvGlobalSubring (hq : q ∈ I) (hI : I.FG) (hItop : I ≠ ⊤) :
    ∃ a : annulusAlgebra R I q, a ∉ tateInvGlobalSubring hI :=
  ⟨overlapX R I q, notMem_tateInvGlobalSubring_overlapX hq hI hItop⟩

variable [IsNoetherianRing R]

/-- **The chart ring at `S = Set.univ` is proper**: the same statement for
`AlgebraicGeometry.tateInvChartAnnulusSubring`, transported along
`AlgebraicGeometry.tateInvGlobalPatchEquiv` by
`AlgebraicGeometry.mem_tateInvChartAnnulusSubring_iff_mem_tateInvGlobalSubring`
(`FormalSchemes.TateInvGlobalSections`).

`AlgebraicGeometry.tateInvChartAnnulusSubring_empty_eq_top`
(`FormalSchemes.TateInvChartAnnulusRing`) shows the question has no `S`-free answer, so this is a
statement about `S = Set.univ` and nothing is claimed at any other `S`. -/
theorem tateInvChartAnnulusSubring_univ_ne_top (hq : q ∈ I) (hI : I.FG) (hItop : I ≠ ⊤) :
    tateInvChartAnnulusSubring (hq := hq) (hI := hI) (S := Set.univ) isOpen_univ ≠ ⊤ := by
  haveI _hann : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI _hax : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  haveI _hay : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  intro h
  refine notMem_tateInvGlobalSubring_overlapX hq hI hItop ?_
  have hs : (tateInvGlobalPatchEquiv hq hI).symm (overlapX R I q) ∈
      tateInvChartAnnulusSubring (hq := hq) (hI := hI) (S := Set.univ) isOpen_univ := by
    rw [h]; exact Subring.mem_top _
  have hmem := (mem_tateInvChartAnnulusSubring_iff_mem_tateInvGlobalSubring hq hI _).1 hs
  rwa [RingEquiv.apply_symm_apply] at hmem

/-- **No global section of `T_inv/⟨σ⟩` has the coordinate `x` as its value.** The injection
`AlgebraicGeometry.injective_globalSectionsToAnnulus`
(`FormalSchemes.TateInvNodeChartRing`) locates `Γ (T_inv/⟨σ⟩)` inside `A`; this says the
inclusion is **not** onto, and names an element it misses. -/
theorem tateInvGlobalSectionsRingEquiv_ne_overlapX (hq : q ∈ I) (hI : I.FG) (hItop : I ≠ ⊤)
    (s : (actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj
      (Opposite.op (⊤ : TopologicalSpace.Opens
        (actionQuotient (tateInvPeriodAction R I q hq hI)).toTopCat))) :
    ((tateInvGlobalSectionsRingEquiv hq hI s : tateInvGlobalSubring hI) :
        annulusAlgebra R I q) ≠ overlapX R I q := fun h =>
  notMem_tateInvGlobalSubring_overlapX hq hI hItop (h ▸ (tateInvGlobalSectionsRingEquiv hq hI s).2)

end Properness

end AlgebraicGeometry
