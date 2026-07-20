import FormalSchemes.TateOverlap
import FormalSchemes.Completion

set_option linter.style.header false

/-!
# The Tate-chain transition: the coordinate swap `x ↔ y`

Fix an adic ring `R` with ideal of definition `I` and a Tate parameter `q ∈ R`, and let
`A = R{x, y} / (x·y − q)` be the coordinate ring of the formal Tate annulus
(`FormalSchemes.TateAnnulus`). The Tate chain glues consecutive annulus patches `U_n = Spf A_n`
and `U_{n+1} = Spf A_{n+1}` along the transition
```
x_{n+1} = y_n,   y_{n+1} = x_n,
```
which is consistent with the two Tate relations (`x_{n+1}·y_{n+1} = y_n·x_n = q`). At the level of
the coordinate rings this transition is the **coordinate swap** automorphism of `A` interchanging
the two coordinates `x` and `y`.

This file constructs that swap and the isomorphisms of the overlap charts it induces:

* `annulusSwap`: the swap `R{x, y} ≃ₐ[R] R{x, y}`, `x ↦ y`, `y ↦ x`, an involution.
* `annulusFlip`: its descent to `A = R{x, y}/(x·y − q)` — the transition automorphism of the Tate
  annulus, again an involution (`annulusFlip_annulusFlip`), since `x·y − q` is symmetric.
* `annulusLocTransition`: the induced isomorphism of the localized charts
  `A[x⁻¹] ≃+* A[y⁻¹]` (the flip carries the coordinate `x` to `y`).
* `annulusOverlapTransition`: the induced isomorphism of the completed overlap charts
  `A[x⁻¹]^∧ ≃+* A[y⁻¹]^∧` — the transition map `t_{n,n+1}` of the Tate chain at the level of the
  rings of sections of the overlap opens, again an involution (`annulusOverlapTransition` composed
  with its `y ↔ x` mirror is the identity — the cocycle condition for consecutive overlaps).

Both overlap charts are, by the crux identification of `FormalSchemes.TateOverlap`
(`overlapEquiv : A[x⁻¹]^∧ ≅ R{x, x⁻¹}`), copies of the formal multiplicative group `Ĝm`; the
transition constructed here is what the cocycle verification of the full gluing (issue 134)
consumes. The assembly of the `U_n` into the glued formal scheme `T` via
`FormalScheme.GlueData`, and the `q^ℤ`-shift action, are the remaining parts of the chain.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open Ideal AlgebraicGeometry RestrictedPowerSeries

universe u

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-!
### The coordinate swap on the polydisc `R{x, y}`
-/

section Swap

variable (hI : I.FG)

/-- The evaluation point `(y, x)` of `R{x, y}` swapping the two coordinates. -/
def swapPoint : Fin 2 → annulusRing R I := ![annulusY R I, annulusX R I]

@[simp] theorem swapPoint_zero : swapPoint R I 0 = annulusY R I := rfl
@[simp] theorem swapPoint_one : swapPoint R I 1 = annulusX R I := rfl

/-- The **coordinate swap** `R{x, y} →ₐ[R] R{x, y}`, `x ↦ y`, `y ↦ x`, obtained by evaluating the
polydisc at the swapped point `(y, x)`. -/
def annulusSwapHom : annulusRing R I →ₐ[R] annulusRing R I :=
  haveI := (RestrictedPowerSeries.isAdicRing R I 2 hI).toIsAdicComplete
  RestrictedPowerSeries.evalAlgHom (idealOfDefinition R I 2)
    (idealOfDefinition_eq_map R I 2).ge (swapPoint R I)

theorem annulusSwapHom_annulusX : annulusSwapHom R I hI (annulusX R I) = annulusY R I := by
  haveI := (RestrictedPowerSeries.isAdicRing R I 2 hI).toIsAdicComplete
  change RestrictedPowerSeries.evalHom R I 2 _ _ (swapPoint R I) (annulusX R I) = _
  rw [annulusX, RestrictedPowerSeries.evalHom_of, MvPolynomial.aeval_X, swapPoint_zero]

theorem annulusSwapHom_annulusY : annulusSwapHom R I hI (annulusY R I) = annulusX R I := by
  haveI := (RestrictedPowerSeries.isAdicRing R I 2 hI).toIsAdicComplete
  change RestrictedPowerSeries.evalHom R I 2 _ _ (swapPoint R I) (annulusY R I) = _
  rw [annulusY, RestrictedPowerSeries.evalHom_of, MvPolynomial.aeval_X, swapPoint_one]

/-- Continuity of the swap: it carries the powers of the ideal of definition into themselves. -/
theorem annulusSwapHom_mem_pow (m : ℕ) {x : annulusRing R I}
    (hx : x ∈ (idealOfDefinition R I 2) ^ m) :
    annulusSwapHom R I hI x ∈ (idealOfDefinition R I 2) ^ m := by
  haveI := (RestrictedPowerSeries.isAdicRing R I 2 hI).toIsAdicComplete
  exact RestrictedPowerSeries.evalHom_mem_pow (idealOfDefinition R I 2)
    (idealOfDefinition_eq_map R I 2).ge (swapPoint R I) hI m hx

/-- The swap is an involution: swapping twice is the identity. -/
theorem annulusSwapHom_annulusSwapHom :
    (annulusSwapHom R I hI).toRingHom.comp (annulusSwapHom R I hI).toRingHom =
      RingHom.id (annulusRing R I) := by
  haveI := (RestrictedPowerSeries.isAdicRing R I 2 hI).toIsAdicComplete
  refine RestrictedPowerSeries.hom_ext (idealOfDefinition R I 2) hI ?_ ?_ ?_ ?_
  · intro m x hx
    exact annulusSwapHom_mem_pow R I hI m (annulusSwapHom_mem_pow R I hI m hx)
  · intro m x hx; exact hx
  · intro r
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.id_apply,
      AlgHom.commutes]
  · refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · change annulusSwapHom R I hI (annulusSwapHom R I hI (annulusX R I)) = annulusX R I
      rw [annulusSwapHom_annulusX, annulusSwapHom_annulusY]
    · change annulusSwapHom R I hI (annulusSwapHom R I hI (annulusY R I)) = annulusY R I
      rw [annulusSwapHom_annulusY, annulusSwapHom_annulusX]

/-- The **coordinate swap** of the polydisc `R{x, y} ≃ₐ[R] R{x, y}` as an `R`-algebra
automorphism, `x ↦ y`, `y ↦ x`. -/
def annulusSwap : annulusRing R I ≃ₐ[R] annulusRing R I :=
  AlgEquiv.ofAlgHom (annulusSwapHom R I hI) (annulusSwapHom R I hI)
    (AlgHom.ext fun x => RingHom.congr_fun (annulusSwapHom_annulusSwapHom R I hI) x)
    (AlgHom.ext fun x => RingHom.congr_fun (annulusSwapHom_annulusSwapHom R I hI) x)

@[simp] theorem annulusSwap_apply (x : annulusRing R I) :
    annulusSwap R I hI x = annulusSwapHom R I hI x := rfl

/-- The swap fixes the Tate relation `x·y − q` (it is symmetric in `x` and `y`). -/
theorem annulusSwapHom_annulusRel :
    annulusSwapHom R I hI (annulusRel R I q) = annulusRel R I q := by
  have h : annulusRel R I q =
      annulusX R I * annulusY R I - algebraMap R (annulusRing R I) q := rfl
  rw [h, map_sub, map_mul, annulusSwapHom_annulusX, annulusSwapHom_annulusY, AlgHom.commutes,
    mul_comm]

end Swap

/-!
### The transition automorphism of the Tate annulus `A = R{x, y}/(x·y − q)`

The swap descends to `A` because it fixes the ideal `(x·y − q)`.
-/

section Flip

variable (hI : I.FG)

/-- The image `y` of the second coordinate in the annulus algebra `A = R{x, y}/(x·y − q)`; the
transition sends the first coordinate `x` (`overlapX`) here. -/
abbrev overlapY : annulusAlgebra R I q := annulusMk R I q (annulusY R I)

/-- The composite `R{x, y} → A`, `p ↦ [swap p]`, used to descend the swap to the quotient. -/
private def annulusFlipAux : annulusRing R I →ₐ[R] annulusAlgebra R I q :=
  (annulusMk R I q).comp (annulusSwap R I hI)

theorem annulusFlipAux_annulusRel :
    annulusFlipAux R I q hI (annulusRel R I q) = 0 := by
  change annulusMk R I q (annulusSwapHom R I hI (annulusRel R I q)) = 0
  rw [annulusSwapHom_annulusRel]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

/-- **The transition automorphism** of the Tate annulus `A = R{x, y}/(x·y − q)`, interchanging the
two coordinates `x` and `y`. This is the identification `x_{n+1} = y_n`, `y_{n+1} = x_n` of the
Tate chain at the level of the coordinate rings. -/
def annulusFlipHom : annulusAlgebra R I q →ₐ[R] annulusAlgebra R I q :=
  Ideal.Quotient.liftₐ (annulusIdeal R I q) (annulusFlipAux R I q hI) <| by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
    rw [map_mul, annulusFlipAux_annulusRel R I q hI, zero_mul]

@[simp] theorem annulusFlipHom_mk (p : annulusRing R I) :
    annulusFlipHom R I q hI (annulusMk R I q p) = annulusMk R I q (annulusSwapHom R I hI p) :=
  rfl

theorem annulusFlipHom_annulusFlipHom :
    (annulusFlipHom R I q hI).comp (annulusFlipHom R I q hI) =
      AlgHom.id R (annulusAlgebra R I q) := by
  refine AlgHom.ext fun a => ?_
  obtain ⟨p, rfl⟩ := annulusMk_surjective R I q a
  rw [AlgHom.comp_apply, annulusFlipHom_mk, annulusFlipHom_mk, AlgHom.id_apply]
  exact congrArg (annulusMk R I q) (RingHom.congr_fun (annulusSwapHom_annulusSwapHom R I hI) p)

/-- **The transition automorphism** `A ≃ₐ[R] A` as an `R`-algebra automorphism of the Tate
annulus, an involution interchanging the two coordinates. -/
def annulusFlip : annulusAlgebra R I q ≃ₐ[R] annulusAlgebra R I q :=
  AlgEquiv.ofAlgHom (annulusFlipHom R I q hI) (annulusFlipHom R I q hI)
    (annulusFlipHom_annulusFlipHom R I q hI) (annulusFlipHom_annulusFlipHom R I q hI)

@[simp] theorem annulusFlip_apply (a : annulusAlgebra R I q) :
    annulusFlip R I q hI a = annulusFlipHom R I q hI a := rfl

@[simp] theorem annulusFlip_symm_apply (a : annulusAlgebra R I q) :
    (annulusFlip R I q hI).symm a = annulusFlipHom R I q hI a := rfl

/-- The transition sends the first coordinate `x` to the second coordinate `y`. -/
theorem annulusFlip_overlapX :
    annulusFlip R I q hI (overlapX R I q) = overlapY R I q := by
  change annulusMk R I q (annulusSwapHom R I hI (annulusX R I)) = annulusMk R I q (annulusY R I)
  rw [annulusSwapHom_annulusX]

/-- The transition sends the second coordinate `y` to the first coordinate `x`. -/
theorem annulusFlip_overlapY :
    annulusFlip R I q hI (overlapY R I q) = overlapX R I q := by
  change annulusMk R I q (annulusSwapHom R I hI (annulusY R I)) = annulusMk R I q (annulusX R I)
  rw [annulusSwapHom_annulusY]

end Flip

/-!
### The transition of the overlap charts

The two consecutive annulus patches `U_n`, `U_{n+1}` overlap on the loci `{x_n invertible}` and
`{y_{n+1} invertible}`; under the coordinate swap these are identified. This section records the
resulting isomorphism of the localized charts `A[x⁻¹] ≃+* A[y⁻¹]` and of the completed charts
`A[x⁻¹]^∧ ≃+* A[y⁻¹]^∧` (the ring of sections of the overlap open).
-/

section Transition

variable (hI : I.FG)

/-- The localization `A[y⁻¹]` of the annulus algebra away from the second coordinate `y`. -/
abbrev annulusLocY : Type u := Localization.Away (overlapY R I q)

/-- The ideal of definition of `A[y⁻¹]`: the extension `I·A[y⁻¹]`. -/
abbrev annulusLocIdealY : Ideal (annulusLocY R I q) :=
  I.map (algebraMap R (annulusLocY R I q))

/-- The completed localization `A[y⁻¹]^∧`, the `I`-adic completion of `A[y⁻¹]`. -/
abbrev annulusOverlapY : Type u :=
  AdicCompletion (annulusLocIdealY R I q) (annulusLocY R I q)

/-- The transition carries the multiplicative set `{xⁿ}` to `{yⁿ}` (it sends `x` to `y`). -/
theorem annulusFlip_map_powers :
    (Submonoid.powers (overlapX R I q)).map (annulusFlip R I q hI).toRingEquiv.toMonoidHom =
      Submonoid.powers (overlapY R I q) := by
  rw [Submonoid.map_powers]
  exact congrArg Submonoid.powers (annulusFlip_overlapX R I q hI)

/-- **The transition of the localized overlap charts** `A[x⁻¹] ≃+* A[y⁻¹]`, induced by the
coordinate swap `A ≃ A` (which carries `x` to `y`). -/
def annulusLocTransition : annulusLoc R I q ≃+* annulusLocY R I q :=
  IsLocalization.ringEquivOfRingEquiv (annulusLoc R I q) (annulusLocY R I q)
    (annulusFlip R I q hI).toRingEquiv (annulusFlip_map_powers R I q hI)

theorem annulusLocTransition_algebraMap (a : annulusAlgebra R I q) :
    annulusLocTransition R I q hI (algebraMap (annulusAlgebra R I q) (annulusLoc R I q) a) =
      algebraMap (annulusAlgebra R I q) (annulusLocY R I q) (annulusFlip R I q hI a) :=
  IsLocalization.ringEquivOfRingEquiv_eq (annulusFlip_map_powers R I q hI) a

theorem annulusLocTransition_algebraMap_R (r : R) :
    annulusLocTransition R I q hI (algebraMap R (annulusLoc R I q) r) =
      algebraMap R (annulusLocY R I q) r := by
  rw [IsScalarTower.algebraMap_apply R (annulusAlgebra R I q) (annulusLoc R I q),
    annulusLocTransition_algebraMap, AlgEquiv.commutes,
    ← IsScalarTower.algebraMap_apply R (annulusAlgebra R I q) (annulusLocY R I q)]

theorem annulusLocTransition_symm_algebraMap_R (r : R) :
    (annulusLocTransition R I q hI).symm (algebraMap R (annulusLocY R I q) r) =
      algebraMap R (annulusLoc R I q) r := by
  rw [RingEquiv.symm_apply_eq, annulusLocTransition_algebraMap_R]

theorem annulusLocTransition_comp_algebraMap :
    (annulusLocTransition R I q hI : annulusLoc R I q →+* annulusLocY R I q).comp
      (algebraMap R (annulusLoc R I q)) = algebraMap R (annulusLocY R I q) :=
  RingHom.ext (annulusLocTransition_algebraMap_R R I q hI)

theorem annulusLocTransition_symm_comp_algebraMap :
    ((annulusLocTransition R I q hI).symm : annulusLocY R I q →+* annulusLoc R I q).comp
      (algebraMap R (annulusLocY R I q)) = algebraMap R (annulusLoc R I q) :=
  RingHom.ext (annulusLocTransition_symm_algebraMap_R R I q hI)

theorem annulusLocTransition_map_ideal :
    (annulusLocIdeal R I q).map
        (annulusLocTransition R I q hI : annulusLoc R I q →+* annulusLocY R I q) =
      annulusLocIdealY R I q := by
  rw [show annulusLocIdeal R I q = I.map (algebraMap R (annulusLoc R I q)) from rfl, Ideal.map_map,
    annulusLocTransition_comp_algebraMap]

theorem annulusLocTransition_symm_map_ideal :
    (annulusLocIdealY R I q).map
        ((annulusLocTransition R I q hI).symm : annulusLocY R I q →+* annulusLoc R I q) =
      annulusLocIdeal R I q := by
  rw [show annulusLocIdealY R I q = I.map (algebraMap R (annulusLocY R I q)) from rfl,
    Ideal.map_map, annulusLocTransition_symm_comp_algebraMap]

/-- The forward completed transition `A[x⁻¹]^∧ →+* A[y⁻¹]^∧`. -/
def annulusOverlapTransitionHom : annulusOverlap R I q →+* annulusOverlapY R I q :=
  AdicCompletion.mapCompletion
    (annulusLocTransition R I q hI : annulusLoc R I q →+* annulusLocY R I q)
    (le_of_eq (annulusLocTransition_map_ideal R I q hI)) (hI.map _)

/-- The inverse completed transition `A[y⁻¹]^∧ →+* A[x⁻¹]^∧`. -/
def annulusOverlapTransitionInv : annulusOverlapY R I q →+* annulusOverlap R I q :=
  AdicCompletion.mapCompletion
    ((annulusLocTransition R I q hI).symm : annulusLocY R I q →+* annulusLoc R I q)
    (le_of_eq (annulusLocTransition_symm_map_ideal R I q hI)) (hI.map _)

theorem annulusOverlapTransitionHom_of (b : annulusLoc R I q) :
    annulusOverlapTransitionHom R I q hI
        (AdicCompletion.of (annulusLocIdeal R I q) (annulusLoc R I q) b) =
      algebraMap (annulusLocY R I q) (annulusOverlapY R I q) (annulusLocTransition R I q hI b) :=
  AdicCompletion.mapCompletion_of _ _ _ b

theorem annulusOverlapTransitionInv_algebraMap (c : annulusLocY R I q) :
    annulusOverlapTransitionInv R I q hI
        (algebraMap (annulusLocY R I q) (annulusOverlapY R I q) c) =
      algebraMap (annulusLoc R I q) (annulusOverlap R I q)
        ((annulusLocTransition R I q hI).symm c) :=
  AdicCompletion.mapCompletion_algebraMap _ _ _ c

theorem annulusOverlapTransitionHom_algebraMap (b : annulusLoc R I q) :
    annulusOverlapTransitionHom R I q hI
        (algebraMap (annulusLoc R I q) (annulusOverlap R I q) b) =
      algebraMap (annulusLocY R I q) (annulusOverlapY R I q) (annulusLocTransition R I q hI b) :=
  AdicCompletion.mapCompletion_algebraMap _ _ _ b

theorem annulusOverlapTransitionInv_of (c : annulusLocY R I q) :
    annulusOverlapTransitionInv R I q hI
        (AdicCompletion.of (annulusLocIdealY R I q) (annulusLocY R I q) c) =
      algebraMap (annulusLoc R I q) (annulusOverlap R I q)
        ((annulusLocTransition R I q hI).symm c) :=
  AdicCompletion.mapCompletion_of _ _ _ c

/-- **Left round-trip**: the inverse transition after the forward transition is the identity. -/
theorem annulusOverlapTransition_left :
    (annulusOverlapTransitionInv R I q hI).comp (annulusOverlapTransitionHom R I q hI) =
      RingHom.id (annulusOverlap R I q) := by
  haveI := AdicCompletion.isAdicComplete_map (annulusLocIdeal R I q) (hI.map _)
  refine AdicCompletion.hom_ext_of_continuous (annulusLocIdeal R I q)
    (AdicCompletion.idealOfDefinition (annulusLocIdeal R I q)) (hI.map _) ?_ ?_ ?_
  · intro m x hx
    have h1 : annulusOverlapTransitionHom R I q hI x ∈
        (AdicCompletion.idealOfDefinition (annulusLocIdealY R I q)) ^ m :=
      AdicCompletion.mapCompletion_mem_pow
        (annulusLocTransition R I q hI : annulusLoc R I q →+* annulusLocY R I q)
        (le_of_eq (annulusLocTransition_map_ideal R I q hI)) (hI.map _) (hI.map _) m hx
    rw [AdicCompletion.mem_idealOfDefinition_pow_iff] at h1
    exact AdicCompletion.mapCompletion_mem_pow
      ((annulusLocTransition R I q hI).symm : annulusLocY R I q →+* annulusLoc R I q)
      (le_of_eq (annulusLocTransition_symm_map_ideal R I q hI)) (hI.map _) (hI.map _) m h1
  · intro m x hx
    exact (AdicCompletion.mem_idealOfDefinition_pow_iff m x).mpr hx
  · intro b
    rw [RingHom.comp_apply, RingHom.id_apply, annulusOverlapTransitionHom_of,
      annulusOverlapTransitionInv_algebraMap, RingEquiv.symm_apply_apply,
      AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

/-- **Right round-trip**: the forward transition after the inverse transition is the identity. -/
theorem annulusOverlapTransition_right :
    (annulusOverlapTransitionHom R I q hI).comp (annulusOverlapTransitionInv R I q hI) =
      RingHom.id (annulusOverlapY R I q) := by
  haveI := AdicCompletion.isAdicComplete_map (annulusLocIdealY R I q) (hI.map _)
  refine AdicCompletion.hom_ext_of_continuous (annulusLocIdealY R I q)
    (AdicCompletion.idealOfDefinition (annulusLocIdealY R I q)) (hI.map _) ?_ ?_ ?_
  · intro m x hx
    have h1 : annulusOverlapTransitionInv R I q hI x ∈
        (AdicCompletion.idealOfDefinition (annulusLocIdeal R I q)) ^ m :=
      AdicCompletion.mapCompletion_mem_pow
        ((annulusLocTransition R I q hI).symm : annulusLocY R I q →+* annulusLoc R I q)
        (le_of_eq (annulusLocTransition_symm_map_ideal R I q hI)) (hI.map _) (hI.map _) m hx
    rw [AdicCompletion.mem_idealOfDefinition_pow_iff] at h1
    exact AdicCompletion.mapCompletion_mem_pow
      (annulusLocTransition R I q hI : annulusLoc R I q →+* annulusLocY R I q)
      (le_of_eq (annulusLocTransition_map_ideal R I q hI)) (hI.map _) (hI.map _) m h1
  · intro m x hx
    exact (AdicCompletion.mem_idealOfDefinition_pow_iff m x).mpr hx
  · intro c
    rw [RingHom.comp_apply, RingHom.id_apply, annulusOverlapTransitionInv_of,
      annulusOverlapTransitionHom_algebraMap, RingEquiv.apply_symm_apply,
      AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

/-- **The transition of the completed overlap charts** `A[x⁻¹]^∧ ≃+* A[y⁻¹]^∧`: the ring of
sections of the overlap open `{x invertible} = {y invertible}` of two consecutive annulus patches,
identified through the coordinate swap. This is the transition map `t_{n,n+1}` of the Tate chain at
the level of the rings of sections. -/
def annulusOverlapTransition : annulusOverlap R I q ≃+* annulusOverlapY R I q :=
  RingEquiv.ofRingHom (annulusOverlapTransitionHom R I q hI) (annulusOverlapTransitionInv R I q hI)
    (annulusOverlapTransition_right R I q hI) (annulusOverlapTransition_left R I q hI)

@[simp] theorem annulusOverlapTransition_apply (x : annulusOverlap R I q) :
    annulusOverlapTransition R I q hI x = annulusOverlapTransitionHom R I q hI x := rfl

@[simp] theorem annulusOverlapTransition_symm_apply (x : annulusOverlapY R I q) :
    (annulusOverlapTransition R I q hI).symm x = annulusOverlapTransitionInv R I q hI x := rfl

end Transition

end
