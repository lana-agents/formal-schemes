import FormalSchemes.TateAnnulus
import FormalSchemes.FormalGm
import FormalSchemes.BaseChange
import Mathlib.RingTheory.Localization.Away.Basic

set_option linter.style.header false

/-!
# The Tate-annulus overlap: `A[x⁻¹]^∧ ≅ R{x, x⁻¹}`

Fix an adic ring `R` with ideal of definition `I` and a Tate parameter `q ∈ R`, and let
`A = R{x, y} / (x·y − q)` be the coordinate ring of the formal Tate annulus
(`FormalSchemes.TateAnnulus`). This file identifies the open of `Spf A` where the first coordinate
`x` is invertible with a copy of the formal multiplicative group `Ĝm = Spf R{x, x⁻¹}`.

Concretely, inverting `x` in `A` forces `y = q·x⁻¹`, so the `I`-adically completed localization is
the restricted Laurent series ring:
```
(A[x⁻¹])^∧  ≅  R{x, x⁻¹}      (continuous R-algebra isomorphism, `x ↦ X`, `y ↦ q·X⁻¹`).
```
This isomorphism is the crux of the transition maps of the Tate chain (Bosch, *Lectures on Formal
and Rigid Geometry*, §9): the overlap of two consecutive annulus patches `U_n`, `U_{n+1}` is a copy
of `Ĝm`, which is what the cocycle verification of the chain consumes.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open Ideal AlgebraicGeometry RestrictedLaurentSeries

universe u

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- The image `x` of the first coordinate in the annulus algebra `A = R{x, y}/(x·y − q)`. -/
abbrev overlapX : annulusAlgebra R I q := annulusMk R I q (annulusX R I)

/-- The localization `A[x⁻¹]` of the annulus algebra away from the coordinate `x`. -/
abbrev annulusLoc : Type u := Localization.Away (overlapX R I q)

/-- The ideal of definition of `A[x⁻¹]`: the extension `I·A[x⁻¹]`. -/
abbrev annulusLocIdeal : Ideal (annulusLoc R I q) :=
  I.map (algebraMap R (annulusLoc R I q))

/-- The completed localization `A[x⁻¹]^∧`, the `I`-adic completion of `A[x⁻¹]`. -/
abbrev annulusOverlap : Type u := AdicCompletion (annulusLocIdeal R I q) (annulusLoc R I q)

/-- The ideal of definition of `A[x⁻¹]^∧`: the extension of `I·A[x⁻¹]` to the completion. -/
abbrev annulusOverlapIdeal : Ideal (annulusOverlap R I q) :=
  (annulusLocIdeal R I q).map (algebraMap (annulusLoc R I q) (annulusOverlap R I q))

/-- `A[x⁻¹]^∧` is a complete adic ring with ideal of definition `I·A[x⁻¹]^∧` (`I` f.g.). -/
theorem annulusOverlap_isAdicRing (hI : I.FG) :
    IsAdicRing (annulusOverlapIdeal R I q) :=
  AdicCompletion.isAdicRing_map _ (hI.map _)

theorem annulusOverlap_isAdicComplete (hI : I.FG) :
    IsAdicComplete (annulusOverlapIdeal R I q) (annulusOverlap R I q) :=
  AdicCompletion.isAdicComplete_map _ (hI.map _)

/-!
### The forward map `A[x⁻¹]^∧ → R{x, x⁻¹}`, `x ↦ X`, `y ↦ q·X⁻¹`
-/

section Forward

variable (hI : I.FG)

/-- The evaluation point `(X, q·X⁻¹)` of `R{x, x⁻¹}` at which the annulus coordinates `(x, y)` are
sent by the forward overlap map. -/
def overlapEvalPoint : Fin 2 → RestrictedLaurentSeries R I :=
  ![X R I 1, algebraMap R (RestrictedLaurentSeries R I) q * X R I (-1)]

@[simp] theorem overlapEvalPoint_zero : overlapEvalPoint R I q 0 = X R I 1 := rfl

@[simp] theorem overlapEvalPoint_one :
    overlapEvalPoint R I q 1 = algebraMap R (RestrictedLaurentSeries R I) q * X R I (-1) := rfl

include hI

/-- The evaluation `R{x, y} → R{x, x⁻¹}` sending `x ↦ X`, `y ↦ q·X⁻¹` (before passing to the
quotient by the Tate relation). -/
def overlapPolyHom : RestrictedPowerSeries R I 2 →+* RestrictedLaurentSeries R I :=
  haveI := (RestrictedLaurentSeries.isAdicRing R I hI).toIsAdicComplete
  RestrictedPowerSeries.evalHom R I 2 (idealOfDefinition R I)
    (idealOfDefinition_eq_map R I).ge (overlapEvalPoint R I q)

theorem overlapPolyHom_annulusX :
    overlapPolyHom R I q hI (annulusX R I) = X R I 1 := by
  haveI := (RestrictedLaurentSeries.isAdicRing R I hI).toIsAdicComplete
  rw [overlapPolyHom, annulusX, RestrictedPowerSeries.evalHom_of, MvPolynomial.aeval_X,
    overlapEvalPoint_zero]

theorem overlapPolyHom_annulusY :
    overlapPolyHom R I q hI (annulusY R I) =
      algebraMap R (RestrictedLaurentSeries R I) q * X R I (-1) := by
  haveI := (RestrictedLaurentSeries.isAdicRing R I hI).toIsAdicComplete
  rw [overlapPolyHom, annulusY, RestrictedPowerSeries.evalHom_of, MvPolynomial.aeval_X,
    overlapEvalPoint_one]

theorem overlapPolyHom_algebraMap (r : R) :
    overlapPolyHom R I q hI (algebraMap R (RestrictedPowerSeries R I 2) r) =
      algebraMap R (RestrictedLaurentSeries R I) r := by
  haveI := (RestrictedLaurentSeries.isAdicRing R I hI).toIsAdicComplete
  rw [overlapPolyHom, AdicCompletion.algebraMap_apply, RestrictedPowerSeries.evalHom_of]
  exact (MvPolynomial.aeval (overlapEvalPoint R I q)).commutes r

/-- The forward polynomial map kills the Tate relation `x·y − q`. -/
theorem overlapPolyHom_annulusRel :
    overlapPolyHom R I q hI (annulusRel R I q) = 0 := by
  rw [annulusRel, map_sub, map_mul, overlapPolyHom_annulusX, overlapPolyHom_annulusY,
    overlapPolyHom_algebraMap]
  linear_combination (algebraMap R (RestrictedLaurentSeries R I) q) *
    RestrictedLaurentSeries.X_one_mul_X_neg_one R I

/-- The forward map descends to the annulus algebra `A = R{x, y}/(x·y − q)`. -/
def overlapQuotHom : annulusAlgebra R I q →+* RestrictedLaurentSeries R I :=
  Ideal.Quotient.lift (annulusIdeal R I q) (overlapPolyHom R I q hI) <| by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
    rw [map_mul, overlapPolyHom_annulusRel, zero_mul]

theorem overlapQuotHom_mk (p : RestrictedPowerSeries R I 2) :
    overlapQuotHom R I q hI (annulusMk R I q p) = overlapPolyHom R I q hI p :=
  Ideal.Quotient.lift_mk _ _ _

theorem overlapQuotHom_overlapX :
    overlapQuotHom R I q hI (overlapX R I q) = X R I 1 := by
  rw [overlapX, overlapQuotHom_mk, overlapPolyHom_annulusX]

theorem overlapQuotHom_algebraMap (r : R) :
    overlapQuotHom R I q hI (algebraMap R (annulusAlgebra R I q) r) =
      algebraMap R (RestrictedLaurentSeries R I) r := by
  have : algebraMap R (annulusAlgebra R I q) r = annulusMk R I q (algebraMap R _ r) :=
    (AlgHom.commutes (annulusMk R I q) r).symm
  rw [this, overlapQuotHom_mk, overlapPolyHom_algebraMap]

theorem isUnit_overlapQuotHom_overlapX :
    IsUnit (overlapQuotHom R I q hI (overlapX R I q)) := by
  rw [overlapQuotHom_overlapX]; exact isUnit_X R I 1

/-- The forward map on the localization `A[x⁻¹] → R{x, x⁻¹}` (the universal property of the
localization; `x` maps to the unit `X`). -/
def overlapLocHom : annulusLoc R I q →+* RestrictedLaurentSeries R I :=
  IsLocalization.Away.lift (overlapX R I q) (isUnit_overlapQuotHom_overlapX R I q hI)

theorem overlapLocHom_algebraMap (a : annulusAlgebra R I q) :
    overlapLocHom R I q hI (algebraMap (annulusAlgebra R I q) (annulusLoc R I q) a) =
      overlapQuotHom R I q hI a :=
  IsLocalization.Away.lift_eq _ _ _

theorem overlapLocHom_comp_algebraMap :
    (overlapLocHom R I q hI).comp (algebraMap R (annulusLoc R I q)) =
      algebraMap R (RestrictedLaurentSeries R I) := by
  ext r
  rw [RingHom.comp_apply,
    IsScalarTower.algebraMap_apply R (annulusAlgebra R I q) (annulusLoc R I q),
    overlapLocHom_algebraMap, overlapQuotHom_algebraMap]

/-- The forward localization map is continuous: it carries the powers of `I·A[x⁻¹]` into the
powers of the ideal of definition of `R{x, x⁻¹}`. -/
theorem overlapLocHom_pow_le (m : ℕ) :
    (annulusLocIdeal R I q) ^ m ≤
      ((idealOfDefinition R I) ^ m).comap (overlapLocHom R I q hI) := by
  have h : ((annulusLocIdeal R I q) ^ m).map (overlapLocHom R I q hI)
      = (idealOfDefinition R I) ^ m := by
    rw [annulusLocIdeal, ← Ideal.map_pow, Ideal.map_map, overlapLocHom_comp_algebraMap,
      Ideal.map_pow, ← idealOfDefinition_eq_map]
  exact Ideal.map_le_iff_le_comap.mp (le_of_eq h)

/-- **The forward overlap map** `A[x⁻¹]^∧ → R{x, x⁻¹}`, the continuous extension of the
localization map to the completion. -/
def overlapHom : annulusOverlap R I q →+* RestrictedLaurentSeries R I :=
  haveI := (RestrictedLaurentSeries.isAdicRing R I hI).toIsAdicComplete
  AdicCompletion.extendRingHom (annulusLocIdeal R I q) (idealOfDefinition R I)
    (overlapLocHom R I q hI) (overlapLocHom_pow_le R I q hI)

theorem overlapHom_of (a : annulusLoc R I q) :
    overlapHom R I q hI (AdicCompletion.of (annulusLocIdeal R I q) (annulusLoc R I q) a) =
      overlapLocHom R I q hI a := by
  haveI := (RestrictedLaurentSeries.isAdicRing R I hI).toIsAdicComplete
  exact AdicCompletion.extendRingHom_of _ _ _ _ a

end Forward

/-!
### The inverse map `R{x, x⁻¹} → A[x⁻¹]^∧`, `X ↦ x`

The coordinate `x` becomes a unit in the localization `A[x⁻¹]`, hence in its completion, so
evaluation of the formal multiplicative group at that unit gives the inverse map.
-/

section Inverse

variable (hI : I.FG)

/-- The ideal of definition of `A[x⁻¹]^∧` is the extension of `I` itself. -/
theorem overlapIdeal_eq_map :
    annulusOverlapIdeal R I q = I.map (algebraMap R (annulusOverlap R I q)) := by
  change (I.map (algebraMap R (annulusLoc R I q))).map
      (algebraMap (annulusLoc R I q) (annulusOverlap R I q)) = _
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R (annulusLoc R I q) (annulusOverlap R I q)]

/-- The image of the coordinate `x` in `A[x⁻¹]^∧` is a unit. -/
theorem isUnit_overlapX_image :
    IsUnit (algebraMap (annulusLoc R I q) (annulusOverlap R I q)
      (algebraMap (annulusAlgebra R I q) (annulusLoc R I q) (overlapX R I q))) :=
  (IsLocalization.map_units (Localization.Away (overlapX R I q))
    (⟨overlapX R I q, Submonoid.mem_powers _⟩ :
      Submonoid.powers (overlapX R I q))).map
    (algebraMap (annulusLoc R I q) (annulusOverlap R I q))

/-- The coordinate `x`, as a unit of `A[x⁻¹]^∧`. -/
def overlapUnit : (annulusOverlap R I q)ˣ := (isUnit_overlapX_image R I q).unit

@[simp] theorem overlapUnit_coe :
    (overlapUnit R I q : annulusOverlap R I q) =
      algebraMap (annulusLoc R I q) (annulusOverlap R I q)
        (algebraMap (annulusAlgebra R I q) (annulusLoc R I q) (overlapX R I q)) :=
  (isUnit_overlapX_image R I q).unit_spec

include hI

/-- **The inverse overlap map** `R{x, x⁻¹} → A[x⁻¹]^∧`, evaluation of the formal multiplicative
group at the unit `x`. It sends `X ↦ x`. -/
def overlapInv : RestrictedLaurentSeries R I →+* annulusOverlap R I q :=
  haveI := annulusOverlap_isAdicComplete R I q hI
  unitEval R I (annulusOverlapIdeal R I q) (overlapIdeal_eq_map R I q).ge (overlapUnit R I q)

theorem overlapInv_X (n : ℤ) :
    overlapInv R I q hI (X R I n) = ((overlapUnit R I q ^ n : (annulusOverlap R I q)ˣ) :
      annulusOverlap R I q) := by
  haveI := annulusOverlap_isAdicComplete R I q hI
  exact unitEval_X R I (annulusOverlapIdeal R I q) (overlapIdeal_eq_map R I q).ge
    (overlapUnit R I q) n

end Inverse

/-!
### The overlap isomorphism `A[x⁻¹]^∧ ≅ R{x, x⁻¹}`
-/

section Iso

variable (hI : I.FG)

/-- Membership in the powers of the ideal of definition of `A[x⁻¹]^∧`, expressed through the
module filtration used by the completion API. -/
theorem mem_overlapIdeal_pow_iff (m : ℕ) (x : annulusOverlap R I q) :
    x ∈ (annulusOverlapIdeal R I q) ^ m ↔
      x ∈ ((annulusLocIdeal R I q) ^ m • ⊤ :
        Submodule (annulusLoc R I q) (annulusOverlap R I q)) := by
  rw [← Ideal.mem_map_pow_iff_mem_smul_top (annulusLocIdeal R I q) m x]
  change x ∈ ((annulusLocIdeal R I q).map
      (algebraMap (annulusLoc R I q) (annulusOverlap R I q))) ^ m ↔ _
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Algebra.algebraMap_self, Ideal.map_id]

/-- Continuity of the forward map, in the module-filtration form consumed downstream. -/
theorem overlapHom_cont (m : ℕ) (x : annulusOverlap R I q)
    (hx : x ∈ ((annulusLocIdeal R I q) ^ m • ⊤ :
      Submodule (annulusLoc R I q) (annulusOverlap R I q))) :
    overlapHom R I q hI x ∈ (idealOfDefinition R I) ^ m := by
  haveI := (RestrictedLaurentSeries.isAdicRing R I hI).toIsAdicComplete
  exact AdicCompletion.extendRingHom_continuous (annulusLocIdeal R I q) (idealOfDefinition R I)
    (overlapLocHom R I q hI) (overlapLocHom_pow_le R I q hI) (hI.map _) m x hx

/-- The forward overlap map bundled as an `R`-algebra homomorphism. -/
def overlapHomAlg : annulusOverlap R I q →ₐ[R] RestrictedLaurentSeries R I where
  toRingHom := overlapHom R I q hI
  commutes' r := by
    change overlapHom R I q hI (algebraMap R (annulusOverlap R I q) r) =
      algebraMap R (RestrictedLaurentSeries R I) r
    rw [AdicCompletion.algebraMap_apply, overlapHom_of]
    exact RingHom.congr_fun (overlapLocHom_comp_algebraMap R I q hI) r

/-- The inverse overlap map bundled as an `R`-algebra homomorphism (evaluation at the unit `x`). -/
def overlapInvAlg : RestrictedLaurentSeries R I →ₐ[R] annulusOverlap R I q :=
  haveI := annulusOverlap_isAdicComplete R I q hI
  unitEvalAlgHom R I (annulusOverlapIdeal R I q) (overlapIdeal_eq_map R I q).ge (overlapUnit R I q)

@[simp] theorem overlapHomAlg_apply (x : annulusOverlap R I q) :
    overlapHomAlg R I q hI x = overlapHom R I q hI x := rfl

@[simp] theorem overlapInvAlg_apply (x : RestrictedLaurentSeries R I) :
    overlapInvAlg R I q hI x = overlapInv R I q hI x := rfl

/-- **Round-trip on `R{x, x⁻¹}`**: the forward map after the inverse map is the identity. -/
theorem overlapHomAlg_comp_overlapInvAlg :
    (overlapHomAlg R I q hI).comp (overlapInvAlg R I q hI) =
      AlgHom.id R (RestrictedLaurentSeries R I) := by
  haveI := (RestrictedLaurentSeries.isAdicRing R I hI).toIsAdicComplete
  refine point_ext R I (idealOfDefinition R I) hI ?_ ?_ ?_
  · -- continuity of the composite
    intro m x hx
    have h1 : overlapInv R I q hI x ∈ (annulusOverlapIdeal R I q) ^ m :=
      haveI := annulusOverlap_isAdicComplete R I q hI
      isContinuousPoint_unitEvalAlgHom R I (annulusOverlapIdeal R I q)
        (overlapIdeal_eq_map R I q).ge hI (overlapUnit R I q) m x hx
    exact overlapHom_cont R I q hI m _ ((mem_overlapIdeal_pow_iff R I q m _).mp h1)
  · -- continuity of the identity
    intro m x hx
    exact (RestrictedLaurentSeries.mem_idealOfDefinition_pow_iff R I m x).mpr hx
  · -- agreement on the coordinate `X`
    change overlapHom R I q hI (overlapInv R I q hI (X R I 1)) = X R I 1
    rw [overlapInv_X, zpow_one, overlapUnit_coe, AdicCompletion.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, overlapHom_of, overlapLocHom_algebraMap,
      overlapQuotHom_overlapX]

/-- The round-trip on `R{x, x⁻¹}` (function form). -/
theorem overlapHom_overlapInv (x : RestrictedLaurentSeries R I) :
    overlapHom R I q hI (overlapInv R I q hI x) = x := by
  have := AlgHom.congr_fun (overlapHomAlg_comp_overlapInvAlg R I q hI) x
  simpa using this

/-!
#### The reverse round-trip `A[x⁻¹]^∧ → A[x⁻¹]^∧`

This is proved by a threefold descent: `hom_ext_of_continuous` reduces the two continuous maps on
the completion `A[x⁻¹]^∧` to the dense subring `A[x⁻¹]`; `IsLocalization.ringHom_ext` reduces those
to the algebra `A`; and `RestrictedPowerSeries.hom_ext` reduces those to the two coordinates
`x, y` of the polydisc, where the computation `x ↦ x`, `y ↦ q·x⁻¹` closes the argument.
-/

/-- Continuity of `overlapPolyHom` (the evaluation `R{x,y} → R{x,x⁻¹}`). -/
theorem overlapPolyHom_mem_pow (m : ℕ) (x : RestrictedPowerSeries R I 2)
    (hx : x ∈ (RestrictedPowerSeries.idealOfDefinition R I 2) ^ m) :
    overlapPolyHom R I q hI x ∈ (idealOfDefinition R I) ^ m := by
  haveI := (RestrictedLaurentSeries.isAdicRing R I hI).toIsAdicComplete
  exact RestrictedPowerSeries.evalHom_mem_pow (n := 2) (L := idealOfDefinition R I)
    (hIL := (idealOfDefinition_eq_map R I).ge) (s := overlapEvalPoint R I q) hI m hx

/-- The inverse map is an `R`-algebra map on constants. -/
theorem overlapInv_algebraMap (r : R) :
    overlapInv R I q hI (algebraMap R (RestrictedLaurentSeries R I) r) =
      algebraMap R (annulusOverlap R I q) r := by
  haveI := annulusOverlap_isAdicComplete R I q hI
  exact (unitEvalAlgHom R I (annulusOverlapIdeal R I q) (overlapIdeal_eq_map R I q).ge
    (overlapUnit R I q)).commutes r

/-- The structural reduction `R{x, y} →ₐ[R] A[x⁻¹]^∧`, `p ↦ [p]`. -/
def overlapRedHom : RestrictedPowerSeries R I 2 →ₐ[R] annulusOverlap R I q :=
  (IsScalarTower.toAlgHom R (annulusAlgebra R I q) (annulusOverlap R I q)).comp
    (annulusMk R I q)

theorem overlapRedHom_apply (p : RestrictedPowerSeries R I 2) :
    overlapRedHom R I q p =
      algebraMap (annulusAlgebra R I q) (annulusOverlap R I q) (annulusMk R I q p) := rfl

/-- The unit `x` of `A[x⁻¹]^∧` times the image of `y` is `q`. -/
theorem overlapUnit_mul_annulusY :
    (overlapUnit R I q : annulusOverlap R I q) *
        algebraMap (annulusAlgebra R I q) (annulusOverlap R I q) (annulusMk R I q (annulusY R I))
      = algebraMap R (annulusOverlap R I q) q := by
  rw [overlapUnit_coe, ← IsScalarTower.algebraMap_apply (annulusAlgebra R I q) (annulusLoc R I q)
    (annulusOverlap R I q), ← map_mul]
  have h : overlapX R I q * annulusMk R I q (annulusY R I)
      = algebraMap R (annulusAlgebra R I q) q := annulus_coord_mul R I q
  rw [h, ← IsScalarTower.algebraMap_apply R (annulusAlgebra R I q) (annulusOverlap R I q)]

/-- **The inner reduction** (coordinate level): the inverse map after the polydisc evaluation is
the structural reduction. Both are continuous `R`-algebra maps out of `R{x, y}` agreeing on the two
coordinates, so `RestrictedPowerSeries.hom_ext` applies. -/
theorem overlapInv_comp_overlapPolyHom :
    (overlapInv R I q hI).comp (overlapPolyHom R I q hI) = (overlapRedHom R I q).toRingHom := by
  haveI := annulusOverlap_isAdicComplete R I q hI
  refine RestrictedPowerSeries.hom_ext (annulusOverlapIdeal R I q) hI ?_ ?_ ?_ ?_
  · -- continuity of `overlapInv ∘ overlapPolyHom`
    intro m x hx
    have h1 := overlapPolyHom_mem_pow R I q hI m x hx
    have h2 := (RestrictedLaurentSeries.mem_idealOfDefinition_pow_iff R I m _).mp h1
    exact isContinuousPoint_unitEvalAlgHom R I (annulusOverlapIdeal R I q)
      (overlapIdeal_eq_map R I q).ge hI (overlapUnit R I q) m _ h2
  · -- continuity of `overlapRedHom`
    intro m x hx
    have hle := Ideal.map_algebraMap_pow_le_comap I (annulusOverlapIdeal R I q)
      (overlapIdeal_eq_map R I q).ge (overlapRedHom R I q) m
    rw [← RestrictedPowerSeries.idealOfDefinition_eq_map] at hle
    exact hle hx
  · -- constants
    intro r
    rw [RingHom.comp_apply, overlapPolyHom_algebraMap, overlapInv_algebraMap,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  · -- coordinates
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · -- `x ↦ X`
      rw [RingHom.comp_apply, overlapPolyHom_annulusX R I q hI, overlapInv_X R I q hI, zpow_one,
        overlapUnit_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, overlapRedHom_apply,
        IsScalarTower.algebraMap_apply (annulusAlgebra R I q) (annulusLoc R I q)
          (annulusOverlap R I q)]
    · -- `y ↦ q·x⁻¹`
      rw [RingHom.comp_apply, overlapPolyHom_annulusY R I q hI, map_mul,
        overlapInv_algebraMap R I q hI, overlapInv_X R I q hI, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, overlapRedHom_apply, zpow_neg_one, mul_comm,
        ← overlapUnit_mul_annulusY R I q, ← mul_assoc, Units.inv_mul, one_mul]

/-- **The middle reduction** (algebra level): on the dense localization `A[x⁻¹]`, the inverse map
after the localization map is the canonical inclusion into the completion. -/
theorem overlapInv_overlapLocHom (b : annulusLoc R I q) :
    overlapInv R I q hI (overlapLocHom R I q hI b) =
      AdicCompletion.of (annulusLocIdeal R I q) (annulusLoc R I q) b := by
  have key : ((overlapInv R I q hI).comp (overlapLocHom R I q hI)).comp
        (algebraMap (annulusAlgebra R I q) (annulusLoc R I q))
      = (algebraMap (annulusLoc R I q) (annulusOverlap R I q)).comp
        (algebraMap (annulusAlgebra R I q) (annulusLoc R I q)) := by
    refine RingHom.ext fun a => ?_
    obtain ⟨p, rfl⟩ := annulusMk_surjective R I q a
    simp only [RingHom.comp_apply, overlapLocHom_algebraMap, overlapQuotHom_mk]
    rw [← RingHom.comp_apply (overlapInv R I q hI) (overlapPolyHom R I q hI),
      overlapInv_comp_overlapPolyHom R I q hI, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      overlapRedHom_apply, IsScalarTower.algebraMap_apply (annulusAlgebra R I q)
        (annulusLoc R I q) (annulusOverlap R I q)]
  have := IsLocalization.ringHom_ext (Submonoid.powers (overlapX R I q)) key
  have hb := RingHom.congr_fun this b
  rw [RingHom.comp_apply] at hb
  rw [hb, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

/-- **The reverse round-trip** on `A[x⁻¹]^∧`. -/
theorem overlapInv_comp_overlapHom :
    (overlapInv R I q hI).comp (overlapHom R I q hI) =
      RingHom.id (annulusOverlap R I q) := by
  haveI := annulusOverlap_isAdicComplete R I q hI
  refine AdicCompletion.hom_ext_of_continuous (annulusLocIdeal R I q) (annulusOverlapIdeal R I q)
    (hI.map _) ?_ ?_ ?_
  · -- continuity of `overlapInv ∘ overlapHom`
    intro m x hx
    have h1 : overlapHom R I q hI x ∈ (idealOfDefinition R I) ^ m := overlapHom_cont R I q hI m x hx
    have h2 := (RestrictedLaurentSeries.mem_idealOfDefinition_pow_iff R I m _).mp h1
    exact isContinuousPoint_unitEvalAlgHom R I (annulusOverlapIdeal R I q)
      (overlapIdeal_eq_map R I q).ge hI (overlapUnit R I q) m _ h2
  · -- continuity of the identity
    intro m x hx
    exact (mem_overlapIdeal_pow_iff R I q m x).mpr hx
  · -- agreement on the dense subring `A[x⁻¹]`
    intro b
    rw [RingHom.comp_apply, overlapHom_of, overlapInv_overlapLocHom, RingHom.id_apply]

theorem overlapHom_comp_overlapInv :
    (overlapHom R I q hI).comp (overlapInv R I q hI) =
      RingHom.id (RestrictedLaurentSeries R I) :=
  RingHom.ext fun x => overlapHom_overlapInv R I q hI x

/-- **The overlap isomorphism** `A[x⁻¹]^∧ ≅ R{x, x⁻¹}`: the completed localization of the Tate
annulus away from `x` is a copy of the restricted Laurent series ring — the formal multiplicative
group `Ĝm` (Bosch, §9). It sends `x ↦ X`. -/
def overlapEquiv : annulusOverlap R I q ≃+* RestrictedLaurentSeries R I :=
  RingEquiv.ofRingHom (overlapHom R I q hI) (overlapInv R I q hI)
    (overlapHom_comp_overlapInv R I q hI) (overlapInv_comp_overlapHom R I q hI)

@[simp] theorem overlapEquiv_apply (x : annulusOverlap R I q) :
    overlapEquiv R I q hI x = overlapHom R I q hI x := rfl

@[simp] theorem overlapEquiv_symm_apply (x : RestrictedLaurentSeries R I) :
    (overlapEquiv R I q hI).symm x = overlapInv R I q hI x := rfl

/-- The overlap isomorphism sends the coordinate `x` to the variable `X` of `Ĝm`. -/
theorem overlapEquiv_overlapX :
    overlapEquiv R I q hI (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)
      (overlapX R I q)) = X R I 1 := by
  rw [overlapEquiv_apply,
    IsScalarTower.algebraMap_apply (annulusAlgebra R I q) (annulusLoc R I q)
      (annulusOverlap R I q), AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, overlapHom_of, overlapLocHom_algebraMap, overlapQuotHom_overlapX]

/-- The overlap isomorphism sends the coordinate `y` to `q·X⁻¹`: the Tate relation `x·y = q`
becomes `y = q·x⁻¹` once `x` is inverted. -/
theorem overlapEquiv_annulusY :
    overlapEquiv R I q hI (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)
      (annulusMk R I q (annulusY R I)))
      = algebraMap R (RestrictedLaurentSeries R I) q * X R I (-1) := by
  rw [overlapEquiv_apply,
    IsScalarTower.algebraMap_apply (annulusAlgebra R I q) (annulusLoc R I q)
      (annulusOverlap R I q), AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, overlapHom_of, overlapLocHom_algebraMap, overlapQuotHom_mk,
    overlapPolyHom_annulusY]

end Iso

end
