import FormalSchemes.AdicCompletionLimit
import FormalSchemes.LocalizationQuotient
import Mathlib.RingTheory.Nilpotent.Basic

set_option linter.style.header false

/-!
# Isomorphisms of adic completions from isomorphisms of thickenings

The `K`-adic completion of `B` is the inverse limit of the thickenings `B ⧸ Kⁿ`
(`AdicCompletion.liftRingHom` / `AdicCompletion.ext_evalₐ` package this universal property).
Consequently a family of ring isomorphisms `B ⧸ Kⁿ ≃+* C ⧸ Lⁿ` compatible with the transition
maps induces an isomorphism `AdicCompletion K B ≃+* AdicCompletion L C`
(`AdicCompletion.congrOfLevelEquiv`). No finite-generation or Noetherian hypothesis is involved.

The first application is the smallest one: a ring isomorphism `f : B ≃+* C` gives such a family by
descending `f` to the thickenings, so completion is functorial in a ring isomorphism
(`AdicCompletion.congrRingEquiv`). The compatibility with the transition maps is `rfl` on
representatives, which is what makes that cheap.

The application here is the second half of the observation that a completed localization only sees
`D(f)` *inside the formal spectrum*: if `s : B` has invertible image in every thickening `B ⧸ Kⁿ`
— equivalently, `D(s) = Spf (B, K)` — then localizing at `s` does not change the completion,

```
AdicCompletion K B ≃+* AdicCompletion (K·B_s) B_s = B{1/s}^ .
```

This is `RingSplit.adicAwayUnitEquiv`. It is what lets one recognise a completed localization
`B{1/(s·t)}^` as `B{1/t}^` when `s` becomes a unit after completing at `t`, which is the shape the
Tate two-chart overlap takes (`x + y = x · (1 + q/x²)` on `D(x)`, with `q` in the ideal of
definition).

## Main results

* `AdicCompletion.congrOfLevelEquiv`: a compatible family of isomorphisms of thickenings induces an
  isomorphism of completions, with `evalₐ_congrOfLevelEquiv` and `congrOfLevelEquiv_of`.
* `AdicCompletion.congrRingEquiv`: **a ring isomorphism `f : B ≃+* C` induces
  `AdicCompletion K B ≃+* AdicCompletion (K.map f) C`**, with
  `AdicCompletion.evalₐ_congrRingEquiv` and `AdicCompletion.congrRingEquiv_of`. Mathlib
  transports the predicates `IsAdicComplete`, `IsHausdorff` and
  `IsPrecomplete` along a `RingEquiv` (`IsAdicComplete.congr_ringEquiv` and companions) but not the
  completion itself; the ideal is written `K.map f` here so that the two compose.
* `RingSplit.isUnit_mk_pow_of_isUnit_mk`: a unit modulo `K` is a unit modulo every `Kⁿ`.
* `RingSplit.adicAwayUnitEquiv`: `AdicCompletion K B ≃+* B{1/s}^` when `s` is invertible in every
  thickening, and `RingSplit.adicAwayUnitEquiv'`, its level-`1` form.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. 0, §7.2, and Ch. I, §10.1.
-/

noncomputable section

universe u

open Ideal

namespace AdicCompletion

variable {B C : Type u} [CommRing B] [CommRing C] (K : Ideal B) (L : Ideal C)
  (e : ∀ n : ℕ, (B ⧸ K ^ n) ≃+* (C ⧸ L ^ n))

/-- The level-`n` component of the induced map on completions. -/
def congrLevel (n : ℕ) : AdicCompletion K B →+* C ⧸ L ^ n :=
  (e n).toRingHom.comp (evalₐ K n).toRingHom

theorem congrLevel_compat
    (he : ∀ {m n : ℕ} (hle : m ≤ n) (z : B ⧸ K ^ n),
      Ideal.Quotient.factorPow L hle (e n z) = e m (Ideal.Quotient.factorPow K hle z))
    {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow L hle).comp (congrLevel K L e n) = congrLevel K L e m :=
  RingHom.ext fun z => by
    change Ideal.Quotient.factorPow L hle (e n (evalₐ K n z)) = e m (evalₐ K m z)
    rw [he hle, factorPow_evalₐ]

/-- The map on completions induced by a compatible family of isomorphisms of thickenings. -/
def congrLevelHom
    (he : ∀ {m n : ℕ} (hle : m ≤ n) (z : B ⧸ K ^ n),
      Ideal.Quotient.factorPow L hle (e n z) = e m (Ideal.Quotient.factorPow K hle z)) :
    AdicCompletion K B →+* AdicCompletion L C :=
  liftRingHom _ (congrLevel K L e) (fun {_ _} hle => congrLevel_compat K L e he hle)

@[simp]
theorem evalₐ_congrLevelHom
    (he : ∀ {m n : ℕ} (hle : m ≤ n) (z : B ⧸ K ^ n),
      Ideal.Quotient.factorPow L hle (e n z) = e m (Ideal.Quotient.factorPow K hle z))
    (n : ℕ) (z : AdicCompletion K B) :
    evalₐ L n (congrLevelHom K L e he z) = e n (evalₐ K n z) :=
  evalₐ_liftRingHom _ _ (fun {_ _} hle => congrLevel_compat K L e he hle) n z

theorem congrLevel_symm_compat
    (he : ∀ {m n : ℕ} (hle : m ≤ n) (z : B ⧸ K ^ n),
      Ideal.Quotient.factorPow L hle (e n z) = e m (Ideal.Quotient.factorPow K hle z))
    {m n : ℕ} (hle : m ≤ n) (w : C ⧸ L ^ n) :
    Ideal.Quotient.factorPow K hle ((e n).symm w) =
      (e m).symm (Ideal.Quotient.factorPow L hle w) := by
  have h := he hle ((e n).symm w)
  rw [RingEquiv.apply_symm_apply] at h
  rw [h, RingEquiv.symm_apply_apply]

/-- **A compatible family of isomorphisms of thickenings induces an isomorphism of completions.**
Both directions are assembled from the level maps by the universal property
`AdicCompletion.liftRingHom`, and the two composites are checked level by level with
`AdicCompletion.ext_evalₐ`. -/
def congrOfLevelEquiv
    (he : ∀ {m n : ℕ} (hle : m ≤ n) (z : B ⧸ K ^ n),
      Ideal.Quotient.factorPow L hle (e n z) = e m (Ideal.Quotient.factorPow K hle z)) :
    AdicCompletion K B ≃+* AdicCompletion L C where
  __ := congrLevelHom K L e he
  invFun := congrLevelHom L K (fun n => (e n).symm)
    (fun {_ _} hle z => congrLevel_symm_compat K L e he hle z)
  left_inv z := by
    refine ext_evalₐ fun n => ?_
    change evalₐ K n (congrLevelHom L K _ _ (congrLevelHom K L e he z)) = _
    rw [evalₐ_congrLevelHom, evalₐ_congrLevelHom, RingEquiv.symm_apply_apply]
  right_inv w := by
    refine ext_evalₐ fun n => ?_
    change evalₐ L n (congrLevelHom K L e he (congrLevelHom L K _ _ w)) = _
    rw [evalₐ_congrLevelHom, evalₐ_congrLevelHom, RingEquiv.apply_symm_apply]

@[simp]
theorem evalₐ_congrOfLevelEquiv
    (he : ∀ {m n : ℕ} (hle : m ≤ n) (z : B ⧸ K ^ n),
      Ideal.Quotient.factorPow L hle (e n z) = e m (Ideal.Quotient.factorPow K hle z))
    (n : ℕ) (z : AdicCompletion K B) :
    evalₐ L n (congrOfLevelEquiv K L e he z) = e n (evalₐ K n z) :=
  evalₐ_congrLevelHom K L e he n z

/-- The induced isomorphism on the images of the two dense subrings, when the level isomorphisms
match `b` with `c`. -/
theorem congrOfLevelEquiv_of
    (he : ∀ {m n : ℕ} (hle : m ≤ n) (z : B ⧸ K ^ n),
      Ideal.Quotient.factorPow L hle (e n z) = e m (Ideal.Quotient.factorPow K hle z))
    (b : B) (c : C)
    (hbc : ∀ n : ℕ, e n (Ideal.Quotient.mk (K ^ n) b) = Ideal.Quotient.mk (L ^ n) c) :
    congrOfLevelEquiv K L e he (of K B b) = of L C c := by
  refine ext_evalₐ fun n => ?_
  rw [evalₐ_congrOfLevelEquiv, evalₐ_of, evalₐ_of, hbc]

/-! ### Transport along a ring isomorphism -/

variable (f : B ≃+* C)

/-- The level-`n` component of `AdicCompletion.congrRingEquiv`: a ring isomorphism `f : B ≃+* C`
carries `K ^ n` onto `(K.map f) ^ n`, so it descends to the thickenings.

This has to be a named definition rather than an inline family: `AdicCompletion.congrOfLevelEquiv`
takes the compatibility as an argument whose statement mentions the family, and that argument
cannot be synthesised against an anonymous one. -/
def ringEquivLevel (n : ℕ) : B ⧸ K ^ n ≃+* C ⧸ (K.map (f : B →+* C)) ^ n :=
  Ideal.quotientEquiv (K ^ n) ((K.map (f : B →+* C)) ^ n) f (by rw [← Ideal.map_pow])

/-- The level isomorphisms of `AdicCompletion.ringEquivLevel` intertwine the transition maps
`Ideal.Quotient.factorPow`. On a representative both sides are the class of `f b`, so this is
`rfl` after `Quotient.inductionOn`. -/
theorem ringEquivLevel_step {m n : ℕ} (hle : m ≤ n) (z : B ⧸ K ^ n) :
    Ideal.Quotient.factorPow (K.map (f : B →+* C)) hle (ringEquivLevel K f n z) =
      ringEquivLevel K f m (Ideal.Quotient.factorPow K hle z) := by
  induction z using Quotient.inductionOn with
  | h b => rfl

/-- **Adic completion transports along a ring isomorphism**: `f : B ≃+* C` induces
`AdicCompletion K B ≃+* AdicCompletion (K.map f) C`. This is
`AdicCompletion.congrOfLevelEquiv` applied to `AdicCompletion.ringEquivLevel` and
`AdicCompletion.ringEquivLevel_step`, and it needs no hypothesis on `K`, `B`, `C` or `f`.

The ideal on the target side is written `K.map f`, which is the shape Mathlib's predicate-level
transports `IsAdicComplete.congr_ringEquiv`, `IsHausdorff.congr_ringEquiv` and
`IsPrecomplete.congr_ringEquiv` take, so the two compose. -/
def congrRingEquiv : AdicCompletion K B ≃+* AdicCompletion (K.map (f : B →+* C)) C :=
  congrOfLevelEquiv K (K.map (f : B →+* C)) (ringEquivLevel K f)
    (fun hle z => ringEquivLevel_step K f hle z)

@[simp]
theorem evalₐ_congrRingEquiv (n : ℕ) (z : AdicCompletion K B) :
    evalₐ (K.map (f : B →+* C)) n (congrRingEquiv K f z) =
      ringEquivLevel K f n (evalₐ K n z) :=
  evalₐ_congrOfLevelEquiv _ _ _ _ n z

/-- `AdicCompletion.congrRingEquiv` acts on the image of `B` as `f` does. -/
theorem congrRingEquiv_of (b : B) :
    congrRingEquiv K f (of K B b) = of (K.map (f : B →+* C)) C (f b) :=
  congrOfLevelEquiv_of _ _ _ _ b (f b) (fun n => by
    rw [ringEquivLevel, Ideal.quotientEquiv_mk])

end AdicCompletion

namespace RingSplit

variable {B : Type u} [CommRing B] (K : Ideal B) (s : B)

/-- **A unit modulo `K` is a unit modulo every power `Kⁿ`**: the kernel of `B ⧸ Kⁿ → B ⧸ K` is
nilpotent. -/
theorem isUnit_mk_pow_of_isUnit_mk (hs : IsUnit (Ideal.Quotient.mk K s)) (n : ℕ) :
    IsUnit (Ideal.Quotient.mk (K ^ n) s) := by
  obtain ⟨u, hu⟩ := hs
  obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective ((u⁻¹ : (B ⧸ K)ˣ) : B ⧸ K)
  have hsv : s * v - 1 ∈ K := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one, hv, ← hu, u.mul_inv, sub_self]
  have hnil : IsNilpotent (Ideal.Quotient.mk (K ^ n) (s * v - 1)) :=
    ⟨n, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow hsv n⟩
  have h1 : IsUnit (Ideal.Quotient.mk (K ^ n) (s * v)) := by
    have := IsNilpotent.isUnit_one_sub hnil.neg
    rw [map_sub, map_one] at this
    simpa using this
  rw [map_mul] at h1
  exact isUnit_of_mul_isUnit_left h1

/-- The ideal `K·B_s`, ideal of definition of the completed localization `B{1/s}^`. -/
abbrev awayUnitIdeal : Ideal (Localization.Away s) :=
  K.map (algebraMap B (Localization.Away s))

/-- **Localizing at an already-invertible element does not change the thickenings.** If `s` is a
unit in `B ⧸ Kⁿ` then `B ⧸ Kⁿ` is itself a localization of `B ⧸ Kⁿ` away from `s̄`, hence agrees
with `B_s ⧸ (K·B_s)ⁿ`. -/
def awayUnitLevelEquiv (hs : ∀ n : ℕ, IsUnit (Ideal.Quotient.mk (K ^ n) s)) (n : ℕ) :
    (B ⧸ K ^ n) ≃+* Localization.Away s ⧸ awayUnitIdeal K s ^ n :=
  haveI : IsLocalization.Away (Ideal.Quotient.mk (K ^ n) s) (B ⧸ K ^ n) :=
    IsLocalization.away_of_isUnit_of_bijective _ (hs n) Function.bijective_id
  (IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk (K ^ n) s)) (B ⧸ K ^ n)
      (Localization.Away s ⧸ (K ^ n).map (algebraMap B (Localization.Away s)))).toRingEquiv.trans
    (Ideal.quotEquivOfEq (Ideal.map_pow _ K n))

@[simp]
theorem awayUnitLevelEquiv_mk (hs : ∀ n : ℕ, IsUnit (Ideal.Quotient.mk (K ^ n) s)) (n : ℕ)
    (b : B) :
    awayUnitLevelEquiv K s hs n (Ideal.Quotient.mk (K ^ n) b) =
      Ideal.Quotient.mk (awayUnitIdeal K s ^ n) (algebraMap B (Localization.Away s) b) := by
  haveI : IsLocalization.Away (Ideal.Quotient.mk (K ^ n) s) (B ⧸ K ^ n) :=
    IsLocalization.away_of_isUnit_of_bijective _ (hs n) Function.bijective_id
  have h := (IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk (K ^ n) s)) (B ⧸ K ^ n)
      (Localization.Away s ⧸ (K ^ n).map (algebraMap B (Localization.Away s)))).commutes
    (Ideal.Quotient.mk (K ^ n) b)
  rw [awayUnitLevelEquiv, RingEquiv.trans_apply]
  change Ideal.quotEquivOfEq _ ((IsLocalization.algEquiv _ _ _) _) = _
  rw [show ((IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk (K ^ n) s)) (B ⧸ K ^ n)
      (Localization.Away s ⧸ (K ^ n).map (algebraMap B (Localization.Away s))))
      (Ideal.Quotient.mk (K ^ n) b)) = _ from h]
  exact Ideal.quotEquivOfEq_mk _ _

theorem factorPow_awayUnitLevelEquiv (hs : ∀ n : ℕ, IsUnit (Ideal.Quotient.mk (K ^ n) s))
    {m n : ℕ} (hle : m ≤ n) (z : B ⧸ K ^ n) :
    Ideal.Quotient.factorPow (awayUnitIdeal K s) hle (awayUnitLevelEquiv K s hs n z) =
      awayUnitLevelEquiv K s hs m (Ideal.Quotient.factorPow K hle z) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
  simp only [awayUnitLevelEquiv_mk, Ideal.Quotient.factor_mk]

/-- **Localizing at an element that is invertible in every thickening does not change the
completion**: `AdicCompletion K B ≃+* B{1/s}^`. Geometrically, `D(s) = Spf (B, K)`. -/
def adicAwayUnitEquiv (hs : ∀ n : ℕ, IsUnit (Ideal.Quotient.mk (K ^ n) s)) :
    AdicCompletion K B ≃+* AdicCompletion (awayUnitIdeal K s) (Localization.Away s) :=
  AdicCompletion.congrOfLevelEquiv K (awayUnitIdeal K s) (awayUnitLevelEquiv K s hs)
    (fun {_ _} hle z => factorPow_awayUnitLevelEquiv K s hs hle z)

theorem adicAwayUnitEquiv_of (hs : ∀ n : ℕ, IsUnit (Ideal.Quotient.mk (K ^ n) s)) (b : B) :
    adicAwayUnitEquiv K s hs (AdicCompletion.of K B b) =
      AdicCompletion.of (awayUnitIdeal K s) (Localization.Away s)
        (algebraMap B (Localization.Away s) b) :=
  AdicCompletion.congrOfLevelEquiv_of _ _ _ _ _ _ (fun n => awayUnitLevelEquiv_mk K s hs n b)

/-- **The level-`1` form of `RingSplit.adicAwayUnitEquiv`**: it is enough that `s` be invertible
in the residue ring `B ⧸ K`, i.e. that `D(s)` be all of `Spf (B, K)`. -/
def adicAwayUnitEquiv' (hs : IsUnit (Ideal.Quotient.mk K s)) :
    AdicCompletion K B ≃+* AdicCompletion (awayUnitIdeal K s) (Localization.Away s) :=
  adicAwayUnitEquiv K s (isUnit_mk_pow_of_isUnit_mk K s hs)

theorem adicAwayUnitEquiv'_of (hs : IsUnit (Ideal.Quotient.mk K s)) (b : B) :
    adicAwayUnitEquiv' K s hs (AdicCompletion.of K B b) =
      AdicCompletion.of (awayUnitIdeal K s) (Localization.Away s)
        (algebraMap B (Localization.Away s) b) :=
  adicAwayUnitEquiv_of K s _ b

end RingSplit

end
