import FormalSchemes.LocalizationSplitOfNilpotentMul
import FormalSchemes.LocalizationQuotient
import FormalSchemes.AdicCompletionLimit

set_option linter.style.header false

/-!
# The adic completion splits as a product of two completed localizations

Let `B` be a commutative ring, `K : Ideal B`, and `f g : B` with

* `IsUnit (f + g)`, and
* `f · g ∈ K`.

Then `D(f)` and `D(g)` cover the formal spectrum `Spf (B, K)` (whose underlying space is
`Spec (B ⧸ K)`, where `f + g` is a unit) and are disjoint there (`f · g` vanishes on
`Spec (B ⧸ K)`), so `Spf (B, K) = D(f) ⊔ D(g)` and the ring of functions splits:

```
AdicCompletion K B ≃+* B{1/f}^ × B{1/g}^ .
```

Here `B{1/f}^ = AdicCompletion (K·B_f) B_f` is the completed localization, which is
`FormalSpectrum.awayCompletion K f` (an `abbrev`, so the statement below is literally about the
completed localizations of `FormalSchemes.BasicOpenChart` — this file simply does not need that
file's imports).

## Why this is not a corollary of `RingSplit.awaySplitEquiv`

`FormalSchemes.LocalizationSplitOfNilpotentMul` splits a ring `T` as `T_f × T_g` when `f · g` is
**nilpotent**. Here `f · g` is only *topologically* nilpotent: it lies in the ideal of definition
`K`, not in a nilpotent ideal. The splitting therefore happens **level by level**, in
`B ⧸ Kⁿ` (where `(f · g)ⁿ⁺¹ = 0`), and is then assembled by the universal property
`AdicCompletion.liftRingHom` of the completion as an inverse limit.

## The one thing that could have gone wrong, and did not

The idempotent produced by the level-`n` splitting is `εₙ = 1 - (1 - xⁿ⁺¹)ⁿ⁺¹` with
`x = f · (f + g)⁻¹`: its formula **depends on the level**, so compatibility of the level splittings
is not syntactic. One expects to need uniqueness of idempotent lifts
(`Ideal.eq_of_isNilpotent_sub_of_isIdempotentElem`) to compare `εₙ₊₁` with `εₙ`.

It is not needed. What the assembly actually requires is that each level isomorphism is the
*canonical* one on elements coming from `B`, i.e. `splitLevel_mk`:

```
splitLevel n (b mod Kⁿ) = (b/1 mod (K·B_f)ⁿ, b/1 mod (K·B_g)ⁿ) ,
```

and this holds however `εₙ` is spelled, because `AlgEquiv.prodQuotientOfIsIdempotentElem` is
`t ↦ (t mod (ε), t mod (1 - ε))` and the localization comparisons are algebra maps. Since
`B → B ⧸ Kⁿ` is surjective, `splitLevel_mk` pins the level maps down completely, and compatibility
(`factorPow_splitLevel`) follows in one line. The `εₙ` never have to be compared.

## Main results

* `RingSplit.awaySplitEquiv_apply`: the splitting of
  `FormalSchemes.LocalizationSplitOfNilpotentMul` is the canonical map `t ↦ (t/1, t/1)`.
* `RingSplit.splitLevel`: the level-`n` splitting `B ⧸ Kⁿ ≃+* B_f ⧸ (K·B_f)ⁿ × B_g ⧸ (K·B_g)ⁿ`,
  with `splitLevel_mk` and `factorPow_splitLevel`.
* `RingSplit.adicAwaySplitEquiv`: the splitting `AdicCompletion K B ≃+* B{1/f}^ × B{1/g}^`,
  with `adicAwaySplitEquiv_of` computing it on the image of `B`.

## References

* [The Stacks Project, Tag 00EE](https://stacks.math.columbia.edu/tag/00EE).
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1.
-/

noncomputable section

universe u

namespace RingSplit

open Ideal

/-! ### The splitting of a ring is the canonical map -/

section Canonical

variable {T : Type u} [CommRing T] {f g : T}

/-- **The splitting is canonical.** Both components of `RingSplit.awaySplitEquiv` are the
localization maps `T → T_f`, `T → T_g`. In particular the equivalence does not depend on the
choice of nilpotency exponent `n`, even though the idempotent used to build it does. -/
theorem awaySplitEquiv_apply (R : Type u) [CommRing R] [Algebra R T] (hu : IsUnit (f + g))
    {n : ℕ} (hn : n ≠ 0) (hfg : (f * g) ^ n = 0) (t : T) :
    awaySplitEquiv R hu hn hfg t =
      (algebraMap T (Localization.Away f) t, algebraMap T (Localization.Away g) t) := by
  letI := isLocalization_away_left hu hn hfg
  letI := isLocalization_away_right hu hn hfg
  ext
  · change (IsLocalization.algEquiv (Submonoid.powers f) _ _) ((splitQuotEquiv R hu hfg t).1) = _
    rw [show (splitQuotEquiv R hu hfg t).1 = Ideal.Quotient.mk _ t from
      AlgEquiv.prodQuotientOfIsIdempotentElem_apply_fst _ _ _ _ _ _,
      ← Ideal.Quotient.algebraMap_eq]
    exact (IsLocalization.algEquiv (Submonoid.powers f) _ _).commutes t
  · change (IsLocalization.algEquiv (Submonoid.powers g) _ _) ((splitQuotEquiv R hu hfg t).2) = _
    rw [show (splitQuotEquiv R hu hfg t).2 = Ideal.Quotient.mk _ t from
      AlgEquiv.prodQuotientOfIsIdempotentElem_apply_snd _ _ _ _ _ _,
      ← Ideal.Quotient.algebraMap_eq]
    exact (IsLocalization.algEquiv (Submonoid.powers g) _ _).commutes t

end Canonical

variable {B : Type u} [CommRing B] {f g : B}

/-- The ideal `K·B_f`, ideal of definition of the completed localization `B{1/f}^`. This is
`FormalSpectrum.awayCompletionIdeal`'s underlying ideal, spelled without the imports of
`FormalSchemes.BasicOpenChart`. -/
abbrev awayIdeal (K : Ideal B) (f : B) : Ideal (Localization.Away f) :=
  K.map (algebraMap B (Localization.Away f))

/-! ### The level-`n` splitting -/

section Level

variable (K : Ideal B)

/-- `f + g` stays a unit in every thickening `B ⧸ Kⁿ`. -/
theorem isUnit_mk_add (hu : IsUnit (f + g)) (n : ℕ) :
    IsUnit (Ideal.Quotient.mk (K ^ n) f + Ideal.Quotient.mk (K ^ n) g) := by
  rw [← map_add]
  exact hu.map _

/-- `f · g` is nilpotent in `B ⧸ Kⁿ`, with exponent `n + 1` — a *positive* exponent even at
level `0`, which is what `RingSplit.awaySplitEquiv`'s `n ≠ 0` hypothesis needs. -/
theorem mk_mul_pow_eq_zero (hfg : f * g ∈ K) (n : ℕ) :
    (Ideal.Quotient.mk (K ^ n) f * Ideal.Quotient.mk (K ^ n) g) ^ (n + 1) = 0 := by
  rw [← map_mul, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.pow_mem_pow hfg (n + 1))

/-- Localization commutes with quotient: `(B ⧸ Kⁿ)_{f̄} ≃+* B_f ⧸ (K·B_f)ⁿ`. -/
def awayLevelEquiv (f : B) (n : ℕ) :
    Localization.Away (Ideal.Quotient.mk (K ^ n) f) ≃+*
      Localization.Away f ⧸ awayIdeal K f ^ n :=
  (Localization.awayQuotientEquiv f (K ^ n)).trans
    (Ideal.quotEquivOfEq (Ideal.map_pow _ K n))

@[simp]
theorem awayLevelEquiv_mk (f : B) (n : ℕ) (b : B) :
    awayLevelEquiv K f n
        (algebraMap (B ⧸ K ^ n) (Localization.Away (Ideal.Quotient.mk (K ^ n) f))
          (Ideal.Quotient.mk (K ^ n) b)) =
      Ideal.Quotient.mk (awayIdeal K f ^ n) (algebraMap B (Localization.Away f) b) := by
  rw [awayLevelEquiv, RingEquiv.trans_apply, Localization.awayQuotientEquiv_algebraMap]
  exact Ideal.quotEquivOfEq_mk _ _

variable (hu : IsUnit (f + g)) (hfg : f * g ∈ K)

/-- **The level-`n` splitting** `B ⧸ Kⁿ ≃+* B_f ⧸ (K·B_f)ⁿ × B_g ⧸ (K·B_g)ⁿ`, obtained by
applying `RingSplit.awaySplitEquiv` in `B ⧸ Kⁿ` (where `f · g` is genuinely nilpotent) and
identifying the two localizations with quotients of localizations. -/
def splitLevel (n : ℕ) :
    (B ⧸ K ^ n) ≃+*
      (Localization.Away f ⧸ awayIdeal K f ^ n) × (Localization.Away g ⧸ awayIdeal K g ^ n) :=
  (awaySplitEquiv (B ⧸ K ^ n) (isUnit_mk_add K hu n) (Nat.succ_ne_zero n)
      (mk_mul_pow_eq_zero K hfg n)).toRingEquiv.trans
    (RingEquiv.prodCongr (awayLevelEquiv K f n) (awayLevelEquiv K g n))

/-- **The level-`n` splitting is canonical on elements of `B`.** This is the lemma that makes the
level-dependence of the idempotents irrelevant; together with surjectivity of `B → B ⧸ Kⁿ` it
determines `splitLevel n` completely. -/
@[simp]
theorem splitLevel_mk (n : ℕ) (b : B) :
    splitLevel K hu hfg n (Ideal.Quotient.mk (K ^ n) b) =
      (Ideal.Quotient.mk (awayIdeal K f ^ n) (algebraMap B (Localization.Away f) b),
        Ideal.Quotient.mk (awayIdeal K g ^ n) (algebraMap B (Localization.Away g) b)) := by
  change (RingEquiv.prodCongr (awayLevelEquiv K f n) (awayLevelEquiv K g n))
      ((awaySplitEquiv (B ⧸ K ^ n) (isUnit_mk_add K hu n) (Nat.succ_ne_zero n)
        (mk_mul_pow_eq_zero K hfg n)) (Ideal.Quotient.mk (K ^ n) b)) = _
  rw [awaySplitEquiv_apply, RingEquiv.prodCongr_apply, Prod.map_apply, awayLevelEquiv_mk,
    awayLevelEquiv_mk]

/-- **The level splittings are compatible with the transition maps of the two towers.** Immediate
from `splitLevel_mk`, since `B → B ⧸ Kⁿ` is surjective and the transition maps are the identity on
elements of `B`. -/
theorem factorPow_splitLevel {m n : ℕ} (hle : m ≤ n) (z : B ⧸ K ^ n) :
    ((Ideal.Quotient.factorPow (awayIdeal K f) hle) (splitLevel K hu hfg n z).1,
      (Ideal.Quotient.factorPow (awayIdeal K g) hle) (splitLevel K hu hfg n z).2) =
      splitLevel K hu hfg m (Ideal.Quotient.factorPow K hle z) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
  simp only [splitLevel_mk, Ideal.Quotient.factor_mk]

end Level

/-! ### The two directions -/

section Maps

variable (K : Ideal B) (hu : IsUnit (f + g)) (hfg : f * g ∈ K)

/-- The `f`-component of the level-`n` splitting, as a map out of the completion. -/
def splitFstLevel (n : ℕ) :
    AdicCompletion K B →+* Localization.Away f ⧸ awayIdeal K f ^ n :=
  (RingHom.fst _ _).comp
    ((splitLevel K hu hfg n).toRingHom.comp (AdicCompletion.evalₐ K n).toRingHom)

theorem splitFstLevel_apply (n : ℕ) (z : AdicCompletion K B) :
    splitFstLevel K hu hfg n z = (splitLevel K hu hfg n (AdicCompletion.evalₐ K n z)).1 := rfl

theorem splitFstLevel_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (awayIdeal K f) hle).comp (splitFstLevel K hu hfg n) =
      splitFstLevel K hu hfg m := by
  refine RingHom.ext fun z => ?_
  have h := congrArg Prod.fst (factorPow_splitLevel K hu hfg hle (AdicCompletion.evalₐ K n z))
  rw [AdicCompletion.factorPow_evalₐ] at h
  exact h

/-- The `g`-component of the level-`n` splitting, as a map out of the completion. -/
def splitSndLevel (n : ℕ) :
    AdicCompletion K B →+* Localization.Away g ⧸ awayIdeal K g ^ n :=
  (RingHom.snd _ _).comp
    ((splitLevel K hu hfg n).toRingHom.comp (AdicCompletion.evalₐ K n).toRingHom)

theorem splitSndLevel_apply (n : ℕ) (z : AdicCompletion K B) :
    splitSndLevel K hu hfg n z = (splitLevel K hu hfg n (AdicCompletion.evalₐ K n z)).2 := rfl

theorem splitSndLevel_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (awayIdeal K g) hle).comp (splitSndLevel K hu hfg n) =
      splitSndLevel K hu hfg m := by
  refine RingHom.ext fun z => ?_
  have h := congrArg Prod.snd (factorPow_splitLevel K hu hfg hle (AdicCompletion.evalₐ K n z))
  rw [AdicCompletion.factorPow_evalₐ] at h
  exact h

/-- The restriction `AdicCompletion K B →+* B{1/f}^`, assembled from the level maps by the
universal property of the completion as an inverse limit. -/
def toAwaySplitFst :
    AdicCompletion K B →+* AdicCompletion (awayIdeal K f) (Localization.Away f) :=
  AdicCompletion.liftRingHom _ (splitFstLevel K hu hfg)
    (fun {_ _} hle => splitFstLevel_compat K hu hfg hle)

@[simp]
theorem evalₐ_toAwaySplitFst (n : ℕ) (z : AdicCompletion K B) :
    AdicCompletion.evalₐ (awayIdeal K f) n (toAwaySplitFst K hu hfg z) =
      (splitLevel K hu hfg n (AdicCompletion.evalₐ K n z)).1 :=
  AdicCompletion.evalₐ_liftRingHom _ _ (fun {_ _} hle => splitFstLevel_compat K hu hfg hle) n z

/-- The restriction `AdicCompletion K B →+* B{1/g}^`. -/
def toAwaySplitSnd :
    AdicCompletion K B →+* AdicCompletion (awayIdeal K g) (Localization.Away g) :=
  AdicCompletion.liftRingHom _ (splitSndLevel K hu hfg)
    (fun {_ _} hle => splitSndLevel_compat K hu hfg hle)

@[simp]
theorem evalₐ_toAwaySplitSnd (n : ℕ) (z : AdicCompletion K B) :
    AdicCompletion.evalₐ (awayIdeal K g) n (toAwaySplitSnd K hu hfg z) =
      (splitLevel K hu hfg n (AdicCompletion.evalₐ K n z)).2 :=
  AdicCompletion.evalₐ_liftRingHom _ _ (fun {_ _} hle => splitSndLevel_compat K hu hfg hle) n z

/-- The level-`n` component of the inverse map: split a pair of compatible families by inverting
the level-`n` splitting. -/
def ofAwaySplitLevel (n : ℕ) :
    (AdicCompletion (awayIdeal K f) (Localization.Away f) ×
      AdicCompletion (awayIdeal K g) (Localization.Away g)) →+* B ⧸ K ^ n :=
  (splitLevel K hu hfg n).symm.toRingHom.comp
    (RingHom.prod ((AdicCompletion.evalₐ (awayIdeal K f) n).toRingHom.comp (RingHom.fst _ _))
      ((AdicCompletion.evalₐ (awayIdeal K g) n).toRingHom.comp (RingHom.snd _ _)))

theorem ofAwaySplitLevel_apply (n : ℕ)
    (w : AdicCompletion (awayIdeal K f) (Localization.Away f) ×
      AdicCompletion (awayIdeal K g) (Localization.Away g)) :
    ofAwaySplitLevel K hu hfg n w =
      (splitLevel K hu hfg n).symm
        (AdicCompletion.evalₐ (awayIdeal K f) n w.1,
          AdicCompletion.evalₐ (awayIdeal K g) n w.2) := rfl

theorem ofAwaySplitLevel_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow K hle).comp (ofAwaySplitLevel K hu hfg n) =
      ofAwaySplitLevel K hu hfg m := by
  refine RingHom.ext fun w => ?_
  change Ideal.Quotient.factorPow K hle (ofAwaySplitLevel K hu hfg n w) =
    ofAwaySplitLevel K hu hfg m w
  rw [ofAwaySplitLevel_apply, ofAwaySplitLevel_apply]
  have h := factorPow_splitLevel K hu hfg hle
    ((splitLevel K hu hfg n).symm
      (AdicCompletion.evalₐ (awayIdeal K f) n w.1, AdicCompletion.evalₐ (awayIdeal K g) n w.2))
  rw [RingEquiv.apply_symm_apply] at h
  have h2 := congrArg (splitLevel K hu hfg m).symm h
  rw [RingEquiv.symm_apply_apply] at h2
  rw [← h2, AdicCompletion.factorPow_evalₐ, AdicCompletion.factorPow_evalₐ]

/-- The inverse map `B{1/f}^ × B{1/g}^ →+* AdicCompletion K B`. -/
def ofAwaySplit :
    (AdicCompletion (awayIdeal K f) (Localization.Away f) ×
      AdicCompletion (awayIdeal K g) (Localization.Away g)) →+* AdicCompletion K B :=
  AdicCompletion.liftRingHom _ (ofAwaySplitLevel K hu hfg)
    (fun {_ _} hle => ofAwaySplitLevel_compat K hu hfg hle)

@[simp]
theorem evalₐ_ofAwaySplit (n : ℕ)
    (w : AdicCompletion (awayIdeal K f) (Localization.Away f) ×
      AdicCompletion (awayIdeal K g) (Localization.Away g)) :
    AdicCompletion.evalₐ K n (ofAwaySplit K hu hfg w) =
      (splitLevel K hu hfg n).symm
        (AdicCompletion.evalₐ (awayIdeal K f) n w.1,
          AdicCompletion.evalₐ (awayIdeal K g) n w.2) :=
  AdicCompletion.evalₐ_liftRingHom _ _ (fun {_ _} hle => ofAwaySplitLevel_compat K hu hfg hle) n w

/-! ### The splitting of the completion -/

/-- **The adic completion splits as a product of two completed localizations.** For `f + g` a unit
and `f · g` in the ideal `K`,

```
AdicCompletion K B ≃+* B{1/f}^ × B{1/g}^ ,
```

the geometric content being `Spf (B, K) = D(f) ⊔ D(g)`. The two directions are assembled level by
level from `RingSplit.splitLevel` through `AdicCompletion.liftRingHom`, and the two composites are
checked on each level with `AdicCompletion.ext_evalₐ`.

No finite-generation or Noetherian hypothesis is needed: the completion is used only through its
universal property as the inverse limit of the thickenings. -/
def adicAwaySplitEquiv :
    AdicCompletion K B ≃+*
      AdicCompletion (awayIdeal K f) (Localization.Away f) ×
        AdicCompletion (awayIdeal K g) (Localization.Away g) where
  __ := (toAwaySplitFst K hu hfg).prod (toAwaySplitSnd K hu hfg)
  invFun := ofAwaySplit K hu hfg
  left_inv z := by
    refine AdicCompletion.ext_evalₐ fun n => ?_
    show AdicCompletion.evalₐ K n (ofAwaySplit K hu hfg _) = _
    rw [evalₐ_ofAwaySplit]
    change (splitLevel K hu hfg n).symm
      (AdicCompletion.evalₐ (awayIdeal K f) n (toAwaySplitFst K hu hfg z),
        AdicCompletion.evalₐ (awayIdeal K g) n (toAwaySplitSnd K hu hfg z)) = _
    rw [evalₐ_toAwaySplitFst, evalₐ_toAwaySplitSnd]
    exact (splitLevel K hu hfg n).symm_apply_apply _
  right_inv w := by
    refine Prod.ext (AdicCompletion.ext_evalₐ fun n => ?_) (AdicCompletion.ext_evalₐ fun n => ?_)
    · change AdicCompletion.evalₐ (awayIdeal K f) n (toAwaySplitFst K hu hfg _) = _
      rw [evalₐ_toAwaySplitFst, evalₐ_ofAwaySplit, RingEquiv.apply_symm_apply]
    · change AdicCompletion.evalₐ (awayIdeal K g) n (toAwaySplitSnd K hu hfg _) = _
      rw [evalₐ_toAwaySplitSnd, evalₐ_ofAwaySplit, RingEquiv.apply_symm_apply]

theorem adicAwaySplitEquiv_apply (z : AdicCompletion K B) :
    adicAwaySplitEquiv K hu hfg z =
      (toAwaySplitFst K hu hfg z, toAwaySplitSnd K hu hfg z) := rfl

/-- **The splitting is the canonical map on the dense subring `B`**: it sends the image of `b : B`
in the completion to the pair of its images in the two completed localizations. This is the
naturality statement a geometric consumer needs. -/
theorem adicAwaySplitEquiv_of (b : B) :
    adicAwaySplitEquiv K hu hfg (AdicCompletion.of K B b) =
      (AdicCompletion.of (awayIdeal K f) (Localization.Away f)
          (algebraMap B (Localization.Away f) b),
        AdicCompletion.of (awayIdeal K g) (Localization.Away g)
          (algebraMap B (Localization.Away g) b)) := by
  rw [adicAwaySplitEquiv_apply, Prod.mk.injEq]
  constructor
  · refine AdicCompletion.ext_evalₐ fun n => ?_
    rw [evalₐ_toAwaySplitFst, AdicCompletion.evalₐ_of, splitLevel_mk, AdicCompletion.evalₐ_of]
  · refine AdicCompletion.ext_evalₐ fun n => ?_
    rw [evalₐ_toAwaySplitSnd, AdicCompletion.evalₐ_of, splitLevel_mk, AdicCompletion.evalₐ_of]

end Maps

end RingSplit

end
