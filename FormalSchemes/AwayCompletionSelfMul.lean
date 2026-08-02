import FormalSchemes.AwayCompletionAway

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The completed localization is insensitive to squaring the away element

Let `A` be a commutative ring which is an `R`-algebra, `J : Ideal A` and `g : A`. Geometrically the
basic opens `D(g)` and `D(g·g)` of `Spec A` coincide, so the two affine basic-open charts of the
formal spectrum built from them agree. At the level of the completed localizations
(`FormalSpectrum.awayCompletion`, `FormalSchemes/BasicOpenChart.lean`) this is the isomorphism

```
A{1/g}  ≃  A{1/g·g}
```

obtained by completing the elementary localization identity `A_g ≅ A_{g·g}` (both are localizations
of `A` at the powers of `g·g`, since `g` is already a unit in `A_g`), pushed through the completion
functor `AdicCompletion.mapCompletion`. This is the self-multiply special case of the transitivity
`FormalSpectrum.awayCompletionAwayEquiv` on `D(g) ⊆ D(f)`, and — unlike that transitivity — the
base ring does not change, so it is available as an `R`-algebra isomorphism.

## Main definitions and results

* `FormalSpectrum.awaySelfMulLocEquiv`: the localization identity `A_g ≃ₐ[A] A_{g·g}`.
* `FormalSpectrum.awayCompletionSelfMulEquiv`: its completion, the `R`-algebra isomorphism
  `A{1/g} ≃ₐ[R] A{1/g·g}`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1 (10.1.4).
-/

noncomputable section

open TopologicalSpace

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R]
variable {A : Type u} [CommRing A] [Algebra R A]
variable (J : Ideal A) (g : A)

/-- **The localization identity `A_g ≃ₐ[A] A_{g·g}`.** Since `g` is a unit in
`A_g = Localization.Away g`, the ring `A_g` is also the localization of `A` away from `g·g`: both
`A_g` and `A_{g·g} = Localization.Away (g·g)` are localizations of `A` at the powers of `g·g`. -/
def awaySelfMulLocEquiv (g : A) :
    Localization.Away g ≃ₐ[A] Localization.Away (g * g) :=
  haveI : IsLocalization.Away (g * g) (Localization.Away g) :=
    IsLocalization.Away.mul_of_isUnit' g g (IsLocalization.Away.algebraMap_isUnit g)
  (IsLocalization.algEquiv (Submonoid.powers (g * g)) (Localization.Away (g * g))
    (Localization.Away g)).symm

/-- The localization identity carries `algebraMap A A_g` to `algebraMap A A_{g·g}`. -/
theorem awaySelfMulLocEquiv_comp_algebraMap :
    (awaySelfMulLocEquiv g).toRingEquiv.toRingHom.comp (algebraMap A (Localization.Away g)) =
      algebraMap A (Localization.Away (g * g)) := by
  ext a
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, AlgEquiv.coe_ringEquiv,
    RingHom.coe_coe]
  exact (awaySelfMulLocEquiv g).commutes a

/-- `J·A_g` is carried onto `J·A_{g·g}` by the localization identity. -/
theorem map_awaySelfMulLocEquiv :
    (J.map (algebraMap A (Localization.Away g))).map (awaySelfMulLocEquiv g).toRingEquiv.toRingHom =
      J.map (algebraMap A (Localization.Away (g * g))) := by
  rw [Ideal.map_map, awaySelfMulLocEquiv_comp_algebraMap]

/-- The inverse localization identity carries `algebraMap A A_{g·g}` back to `algebraMap A A_g`. -/
theorem awaySelfMulLocEquiv_symm_comp_algebraMap :
    (awaySelfMulLocEquiv g).symm.toRingEquiv.toRingHom.comp
        (algebraMap A (Localization.Away (g * g))) =
      algebraMap A (Localization.Away g) := by
  ext a
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, AlgEquiv.coe_ringEquiv,
    RingHom.coe_coe]
  exact (awaySelfMulLocEquiv g).symm.commutes a

/-- `J·A_{g·g}` is carried back onto `J·A_g` by the inverse localization identity. -/
theorem map_awaySelfMulLocEquiv_symm :
    (J.map (algebraMap A (Localization.Away (g * g)))).map
        (awaySelfMulLocEquiv g).symm.toRingEquiv.toRingHom =
      J.map (algebraMap A (Localization.Away g)) := by
  rw [Ideal.map_map, awaySelfMulLocEquiv_symm_comp_algebraMap]

/-- The forward ring map `A{1/g} →+* A{1/g·g}`, the completion of the localization identity. -/
def awayCompletionSelfMulHom (hJ : J.FG) :
    awayCompletion J g →+* awayCompletion J (g * g) :=
  AdicCompletion.mapCompletion (awaySelfMulLocEquiv g).toRingEquiv.toRingHom
    (map_awaySelfMulLocEquiv J g).le (hJ.map _)

/-- The backward ring map `A{1/g·g} →+* A{1/g}`, the completion of the inverse identity. -/
def awayCompletionSelfMulInvHom (hJ : J.FG) :
    awayCompletion J (g * g) →+* awayCompletion J g :=
  AdicCompletion.mapCompletion (awaySelfMulLocEquiv g).symm.toRingEquiv.toRingHom
    (map_awaySelfMulLocEquiv_symm J g).le (hJ.map _)

/-- The forward map fixes the structural image `algebraMap A A{1/g}` of `A`. -/
theorem awayCompletionSelfMulHom_algebraMap (hJ : J.FG) (a : A) :
    awayCompletionSelfMulHom J g hJ (algebraMap A (awayCompletion J g) a) =
      algebraMap A (awayCompletion J (g * g)) a := by
  rw [awayCompletionSelfMulHom,
    IsScalarTower.algebraMap_apply A (Localization.Away g) (awayCompletion J g),
    AdicCompletion.mapCompletion_algebraMap]
  have hcomm := RingHom.congr_fun (awaySelfMulLocEquiv_comp_algebraMap g) a
  rw [RingHom.comp_apply] at hcomm
  rw [hcomm, ← IsScalarTower.algebraMap_apply A (Localization.Away (g * g))
    (awayCompletion J (g * g))]

/-- The backward map fixes the structural image `algebraMap A A{1/g·g}` of `A`. -/
theorem awayCompletionSelfMulInvHom_algebraMap (hJ : J.FG) (a : A) :
    awayCompletionSelfMulInvHom J g hJ (algebraMap A (awayCompletion J (g * g)) a) =
      algebraMap A (awayCompletion J g) a := by
  rw [awayCompletionSelfMulInvHom,
    IsScalarTower.algebraMap_apply A (Localization.Away (g * g)) (awayCompletion J (g * g)),
    AdicCompletion.mapCompletion_algebraMap]
  have hcomm := RingHom.congr_fun (awaySelfMulLocEquiv_symm_comp_algebraMap g) a
  rw [RingHom.comp_apply] at hcomm
  rw [hcomm, ← IsScalarTower.algebraMap_apply A (Localization.Away g) (awayCompletion J g)]

set_option maxHeartbeats 400000 in
-- the kernel type-checks a nested tower of localization/completion instances, which is costly
/-- **The completed localization is insensitive to squaring the away element** (ring version): the
ring isomorphism `A{1/g} ≃+* A{1/g·g}`, obtained by completing the localization identity
`awaySelfMulLocEquiv`. -/
def awayCompletionSelfMulRingEquiv (hJ : J.FG) :
    awayCompletion J g ≃+* awayCompletion J (g * g) := by
  let φ := (awaySelfMulLocEquiv g).toRingEquiv.toRingHom
  let ψ := (awaySelfMulLocEquiv g).symm.toRingEquiv.toRingHom
  let Kg : Ideal (Localization.Away g) := J.map (algebraMap A (Localization.Away g))
  let Kgg : Ideal (Localization.Away (g * g)) := J.map (algebraMap A (Localization.Away (g * g)))
  have hKgFG : Kg.FG := hJ.map _
  have hKggFG : Kgg.FG := hJ.map _
  have hA : Kg.map φ ≤ Kgg := le_of_eq (map_awaySelfMulLocEquiv J g)
  have hB : Kgg.map ψ ≤ Kg := le_of_eq (map_awaySelfMulLocEquiv_symm J g)
  haveI : IsAdicComplete (AdicCompletion.idealOfDefinition Kg)
      (AdicCompletion Kg (Localization.Away g)) :=
    (AdicCompletion.isAdicRing_map _ hKgFG).toIsAdicComplete
  haveI : IsAdicComplete (AdicCompletion.idealOfDefinition Kgg)
      (AdicCompletion Kgg (Localization.Away (g * g))) :=
    (AdicCompletion.isAdicRing_map _ hKggFG).toIsAdicComplete
  refine RingEquiv.ofRingHom
    (AdicCompletion.mapCompletion φ hA hKggFG)
    (AdicCompletion.mapCompletion ψ hB hKgFG) ?_ ?_
  · refine AdicCompletion.hom_ext_of_continuous Kgg (AdicCompletion.idealOfDefinition Kgg) hKggFG
      (fun m x hx => ?_)
      (fun m x hx => (AdicCompletion.mem_idealOfDefinition_pow_iff m x).mpr hx) (fun c => ?_)
    · have h1 := AdicCompletion.mapCompletion_mem_pow ψ hB hKgFG hKggFG m hx
      rw [AdicCompletion.mem_idealOfDefinition_pow_iff] at h1
      exact AdicCompletion.mapCompletion_mem_pow φ hA hKggFG hKgFG m h1
    · rw [RingHom.comp_apply, AdicCompletion.mapCompletion_of,
        AdicCompletion.mapCompletion_algebraMap]
      have hφψ : φ (ψ c) = c := by
        simp only [φ, ψ, RingEquiv.toRingHom_eq_coe, AlgEquiv.coe_ringEquiv, RingHom.coe_coe,
          AlgEquiv.apply_symm_apply]
      rw [hφψ, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        RingHom.id_apply]
  · refine AdicCompletion.hom_ext_of_continuous Kg (AdicCompletion.idealOfDefinition Kg) hKgFG
      (fun m x hx => ?_)
      (fun m x hx => (AdicCompletion.mem_idealOfDefinition_pow_iff m x).mpr hx) (fun r => ?_)
    · have h1 := AdicCompletion.mapCompletion_mem_pow φ hA hKggFG hKgFG m hx
      rw [AdicCompletion.mem_idealOfDefinition_pow_iff] at h1
      exact AdicCompletion.mapCompletion_mem_pow ψ hB hKgFG hKggFG m h1
    · rw [RingHom.comp_apply, AdicCompletion.mapCompletion_of,
        AdicCompletion.mapCompletion_algebraMap]
      have hψφ : ψ (φ r) = r := by
        simp only [φ, ψ, RingEquiv.toRingHom_eq_coe, AlgEquiv.coe_ringEquiv, RingHom.coe_coe,
          AlgEquiv.symm_apply_apply]
      rw [hψφ, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        RingHom.id_apply]

theorem awayCompletionSelfMulRingEquiv_apply (hJ : J.FG) (x : awayCompletion J g) :
    awayCompletionSelfMulRingEquiv J g hJ x = awayCompletionSelfMulHom J g hJ x := by
  rw [awayCompletionSelfMulRingEquiv, RingEquiv.ofRingHom_apply, awayCompletionSelfMulHom]

theorem awayCompletionSelfMulRingEquiv_symm_apply (hJ : J.FG) (x : awayCompletion J (g * g)) :
    (awayCompletionSelfMulRingEquiv J g hJ).symm x = awayCompletionSelfMulInvHom J g hJ x := by
  rw [awayCompletionSelfMulRingEquiv, RingEquiv.ofRingHom_symm_apply, awayCompletionSelfMulInvHom]

set_option maxHeartbeats 400000 in
-- the kernel type-checks a nested tower of localization/completion instances, which is costly
/-- **The completed localization is insensitive to squaring the away element**: the `R`-algebra
isomorphism `A{1/g} ≃ₐ[R] A{1/g·g}`, obtained by completing the localization identity
`awaySelfMulLocEquiv`. -/
def awayCompletionSelfMulEquiv (hJ : J.FG) :
    awayCompletion J g ≃ₐ[R] awayCompletion J (g * g) :=
  AlgEquiv.ofRingEquiv (f := awayCompletionSelfMulRingEquiv J g hJ) fun r => by
    rw [awayCompletionSelfMulRingEquiv_apply,
      IsScalarTower.algebraMap_apply R A (awayCompletion J g),
      awayCompletionSelfMulHom_algebraMap,
      ← IsScalarTower.algebraMap_apply R A (awayCompletion J (g * g))]

/-- The underlying ring map of `awayCompletionSelfMulEquiv` commutes with `algebraMap A`. -/
theorem awayCompletionSelfMulEquiv_comp_algebraMap (hJ : J.FG) :
    (awayCompletionSelfMulEquiv (R := R) J g hJ).toRingEquiv.toRingHom.comp
        (algebraMap A (awayCompletion J g)) =
      algebraMap A (awayCompletion J (g * g)) := by
  ext a
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AlgEquiv.coe_ringEquiv, awayCompletionSelfMulEquiv, AlgEquiv.ofRingEquiv_apply]
  rw [awayCompletionSelfMulRingEquiv_apply, awayCompletionSelfMulHom_algebraMap]

/-- The inverse ring map of `awayCompletionSelfMulEquiv` commutes with `algebraMap A`. -/
theorem awayCompletionSelfMulEquiv_symm_comp_algebraMap (hJ : J.FG) :
    (awayCompletionSelfMulEquiv (R := R) J g hJ).symm.toRingEquiv.toRingHom.comp
        (algebraMap A (awayCompletion J (g * g))) =
      algebraMap A (awayCompletion J g) := by
  refine RingHom.ext fun a => ?_
  have h : (awayCompletionSelfMulEquiv (R := R) J g hJ).symm
      (algebraMap A (awayCompletion J (g * g)) a) = algebraMap A (awayCompletion J g) a := by
    rw [awayCompletionSelfMulEquiv, AlgEquiv.ofRingEquiv_symm_apply,
      awayCompletionSelfMulRingEquiv_symm_apply, awayCompletionSelfMulInvHom_algebraMap]
  simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AlgEquiv.coe_ringEquiv] using h

end FormalSpectrum
