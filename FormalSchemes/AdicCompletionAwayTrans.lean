import FormalSchemes.AdicCompletionCongrLevel

set_option linter.style.header false

/-!
# Formal transitivity of completed localizations

Let `B` be a commutative ring with an ideal `K`, and let `t f : B`. Write `B_f` for a localization
of `B` away from `f` and `C` for a localization of `B` away from `t · f` — for instance
`C = (B_t)_{f̄}`, which is one by `IsLocalization.Away.mul'`. This file proves

```
B{1/f}^ ≃+* C{1/(t·f)}^ ,   i.e.   AdicCompletion (K·B_f) B_f ≃+* AdicCompletion (K·C) C ,
```

under the hypothesis that **`t` is invertible in every thickening `B_f ⧸ (K·B_f)ⁿ`**. Geometrically
that hypothesis says `D(f) ⊆ D(t)` **inside the formal spectrum** `Spf (B_f, K·B_f)`, and the
conclusion says that further localizing at `t` then changes nothing: `Spf` only sees `D(f)`.

## Why this is not `FormalSpectrum.awayCompletionAwayEquiv`

`FormalSchemes.AwayCompletionAway` proves the same identification from the *stronger* hypothesis
`IsUnit (algebraMap B B_f t)` — `D(f) ⊆ D(t)` in `Spec B`. The motivating example fails that
hypothesis: on the Tate annulus `A = R{x, y}/(x·y − q)` with `t = x + y` and `f = x`, one has
`x + y = x · (1 + q/x²)` in `A_x`, and `q/x²` is only *topologically* nilpotent, so `x + y` is not
a unit in `A_x`. It *is* a unit in every `A_x ⧸ (J·A_x)ⁿ`, which is exactly the hypothesis here.

## The proof

Level by level, through `AdicCompletion.congrOfLevelEquiv`. At level `n` both

```
B_f ⧸ (Kⁿ)·B_f        and        C ⧸ (Kⁿ)·C
```

are localizations of `B ⧸ Kⁿ` away from the image of `t · f`:

* for `C` this is `IsLocalization.away_quotient'` applied to `t · f` directly;
* for `B_f` it is `IsLocalization.away_quotient'` applied to `f`, upgraded from `Away f̄` to
  `Away (t̄ · f̄)` by `IsLocalization.Away.mul_of_isUnit'`. **This is the only place the hypothesis
  is used**, and it is a one-line Mathlib citation.

So they are canonically isomorphic by `IsLocalization.algEquiv`. Compatibility across levels is
proved not by comparing the two localizations again but by computing the level map on the image of
`B_f`, via `IsLocalization.ringHom_ext` for `Submonoid.powers f`: the level map is
`z ↦ awayTransHom z` composed with the quotient map, which visibly commutes with the tower
transitions. (This is the same "pin the map down on a dense subring rather than compare the
auxiliary data" move that `FormalSchemes.AdicCompletionSplitAway` uses.)

## Main results

* `IsLocalization.away_quotient'`: localization away from `a` commutes with quotients, for an
  arbitrary localization `C`, not only `Localization.Away a`.
* `RingSplit.awayTransHom`: the canonical map `B_f →+* C`.
* `RingSplit.awayTransCongrLevel`: the level-`n` isomorphism `B_f ⧸ (K·B_f)ⁿ ≃+* C ⧸ (K·C)ⁿ`.
* `RingSplit.adicAwayTransEquiv`: the isomorphism of completions, with `adicAwayTransEquiv_of`
  computing it on the image of `B_f`.
* `RingSplit.adicAwayTransEquiv'`: the same from the level-`1` hypothesis alone.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1.
* [The Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7).
-/

noncomputable section

universe u

/-! ### Localization commutes with quotients, for an arbitrary localization

`FormalSchemes.LocalizationQuotient` proves this for `C = Localization.Away a`. The proof does not
use anything about that particular model, so it generalises verbatim, and the general form is what
this file needs — the two rings compared below are `B_f` and `C`, neither of which is presented as
a `Localization.Away` of the ring being quotiented.
-/

namespace IsLocalization

/-- **Localization away from `a` commutes with quotient by `K`**, for an arbitrary localization
`C` of `B` away from `a`. Generalises `IsLocalization.away_quotient`
(`FormalSchemes.LocalizationQuotient`), whose proof this repeats verbatim with `Localization.Away a`
replaced by `C`.

It is stated here rather than in `LocalizationQuotient.lean` — where it belongs, and where it would
turn the existing instance into a one-liner — only because that file sits at the bottom of the
import graph, so editing it forces a full-tree rebuild that currently cannot be completed on this
box (see the `TateSelfProductDSigmaInv` memory issue). Move it down and delete the special case as
part of the first low-level pass after that is fixed. -/
instance away_quotient' {B : Type*} [CommRing B] (a : B) (K : Ideal B) (C : Type*) [CommRing C]
    [Algebra B C] [IsLocalization.Away a C] :
    IsLocalization.Away (Ideal.Quotient.mk K a) (C ⧸ K.map (algebraMap B C)) := by
  have h : Algebra.algebraMapSubmonoid (B ⧸ K) (Submonoid.powers a)
      = Submonoid.powers (Ideal.Quotient.mk K a) := by
    change (Submonoid.powers a).map (algebraMap B (B ⧸ K))
      = Submonoid.powers (Ideal.Quotient.mk K a)
    rw [Submonoid.map_powers, Ideal.Quotient.algebraMap_eq]
  change IsLocalization (Submonoid.powers (Ideal.Quotient.mk K a)) _
  rw [← h]
  infer_instance

end IsLocalization

namespace RingSplit

open Ideal

/-! ### The canonical map `B_f → C` -/

section Hom

variable {B : Type u} [CommRing B]

/-- `f` is invertible in `C`, because `f` divides `t · f`. -/
theorem isUnit_algebraMap_of_away_mul (t f : B) (C : Type u) [CommRing C] [Algebra B C]
    [IsLocalization.Away (t * f) C] : IsUnit (algebraMap B C f) :=
  IsLocalization.Away.isUnit_of_dvd (S := C) (x := t * f) ⟨t, mul_comm t f⟩

/-- **The canonical map `B_f →+* C`.** It exists because `C` inverts `t · f`, hence `f`. -/
def awayTransHom (t f : B) (C : Type u) [CommRing C] [Algebra B C]
    [IsLocalization.Away (t * f) C] (Bf : Type u) [CommRing Bf] [Algebra B Bf]
    [IsLocalization.Away f Bf] : Bf →+* C :=
  IsLocalization.Away.lift (S := Bf) f (isUnit_algebraMap_of_away_mul t f C)

@[simp]
theorem awayTransHom_algebraMap (t f : B) (C : Type u) [CommRing C] [Algebra B C]
    [IsLocalization.Away (t * f) C] (Bf : Type u) [CommRing Bf] [Algebra B Bf]
    [IsLocalization.Away f Bf] (b : B) :
    awayTransHom t f C Bf (algebraMap B Bf b) = algebraMap B C b :=
  IsLocalization.Away.lift_eq _ _ _

end Hom

/-! ### The level-`n` isomorphism -/

section Level

variable {B : Type u} [CommRing B] (K : Ideal B) (t f : B)
variable (Bf : Type u) [CommRing Bf] [Algebra B Bf] [IsLocalization.Away f Bf]
variable (C : Type u) [CommRing C] [Algebra B C] [IsLocalization.Away (t * f) C]

/-- The hypothesis of this file, transported between the two spellings `(Kⁿ)·B_f` and `(K·B_f)ⁿ`
of the level-`n` ideal. These are equal (`Ideal.map_pow`) but not syntactically, hence not the same
quotient *type*. -/
theorem isUnit_mk_map_pow (n : ℕ)
    (ht : IsUnit (Ideal.Quotient.mk ((K.map (algebraMap B Bf)) ^ n) (algebraMap B Bf t))) :
    IsUnit (Ideal.Quotient.mk ((K ^ n).map (algebraMap B Bf)) (algebraMap B Bf t)) := by
  rwa [show (K ^ n).map (algebraMap B Bf) = (K.map (algebraMap B Bf)) ^ n from
    Ideal.map_pow _ K n]

/-- **`t · f` is inverted in `B_f ⧸ (Kⁿ)·B_f`.** The factor `f` is inverted because `B_f` is a
localization away from `f`, and `t` by hypothesis; `IsLocalization.Away.mul_of_isUnit'` combines
the two. This is the only step at which `D(f) ⊆ D(t)` is used. -/
theorem isLocalization_away_mul_level (n : ℕ)
    (ht : IsUnit (Ideal.Quotient.mk ((K ^ n).map (algebraMap B Bf)) (algebraMap B Bf t))) :
    IsLocalization.Away (Ideal.Quotient.mk (K ^ n) (t * f))
      (Bf ⧸ (K ^ n).map (algebraMap B Bf)) := by
  rw [map_mul]
  exact IsLocalization.Away.mul_of_isUnit' _ _ ht

/-- The level-`n` isomorphism in the `(Kⁿ)·B_f` spelling: both sides are localizations of
`B ⧸ Kⁿ` away from the image of `t · f`, so `IsLocalization.algEquiv` identifies them. -/
def awayTransLevelEquiv (n : ℕ)
    (ht : IsUnit (Ideal.Quotient.mk ((K ^ n).map (algebraMap B Bf)) (algebraMap B Bf t))) :
    (Bf ⧸ (K ^ n).map (algebraMap B Bf)) ≃ₐ[B ⧸ K ^ n] (C ⧸ (K ^ n).map (algebraMap B C)) :=
  letI := isLocalization_away_mul_level K t f Bf n ht
  IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk (K ^ n) (t * f))) _ _

/-- **The level-`n` isomorphism** `B_f ⧸ (K·B_f)ⁿ ≃+* C ⧸ (K·C)ⁿ`, in the spelling the tower of an
adic completion uses. The two `Ideal.quotEquivOfEq` bridges are the usual `(Kⁿ)·B_f` versus
`(K·B_f)ⁿ` bookkeeping. -/
def awayTransCongrLevel (n : ℕ)
    (ht : IsUnit (Ideal.Quotient.mk ((K.map (algebraMap B Bf)) ^ n) (algebraMap B Bf t))) :
    (Bf ⧸ (K.map (algebraMap B Bf)) ^ n) ≃+* (C ⧸ (K.map (algebraMap B C)) ^ n) :=
  (Ideal.quotEquivOfEq (Ideal.map_pow _ K n).symm).trans
    ((awayTransLevelEquiv K t f Bf C n
        (isUnit_mk_map_pow K t Bf n ht)).toRingEquiv.trans
      (Ideal.quotEquivOfEq (Ideal.map_pow _ K n)))

@[simp]
theorem awayTransCongrLevel_algebraMap (n : ℕ)
    (ht : IsUnit (Ideal.Quotient.mk ((K.map (algebraMap B Bf)) ^ n) (algebraMap B Bf t)))
    (b : B) :
    awayTransCongrLevel K t f Bf C n ht
        (Ideal.Quotient.mk ((K.map (algebraMap B Bf)) ^ n) (algebraMap B Bf b)) =
      Ideal.Quotient.mk ((K.map (algebraMap B C)) ^ n) (algebraMap B C b) := by
  rw [awayTransCongrLevel, RingEquiv.trans_apply, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  refine (congrArg (Ideal.quotEquivOfEq (Ideal.map_pow (algebraMap B C) K n)) ?_).trans
    (Ideal.quotEquivOfEq_mk _ _)
  exact (awayTransLevelEquiv K t f Bf C n (isUnit_mk_map_pow K t Bf n ht)).commutes
    (Ideal.Quotient.mk (K ^ n) b)

/-- **The level-`n` isomorphism is the reduction of `awayTransHom`.** This is what makes the levels
compatible: it is proved by `IsLocalization.ringHom_ext` for `Submonoid.powers f` on `B_f`, so it
never compares the two localization structures again. -/
theorem awayTransCongrLevel_mk (n : ℕ)
    (ht : IsUnit (Ideal.Quotient.mk ((K.map (algebraMap B Bf)) ^ n) (algebraMap B Bf t)))
    (z : Bf) :
    awayTransCongrLevel K t f Bf C n ht (Ideal.Quotient.mk _ z) =
      Ideal.Quotient.mk _ (awayTransHom t f C Bf z) := by
  have h : (awayTransCongrLevel K t f Bf C n ht).toRingHom.comp
        (Ideal.Quotient.mk ((K.map (algebraMap B Bf)) ^ n)) =
      (Ideal.Quotient.mk ((K.map (algebraMap B C)) ^ n)).comp (awayTransHom t f C Bf) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun b => ?_)
    change awayTransCongrLevel K t f Bf C n ht
        (Ideal.Quotient.mk _ (algebraMap B Bf b)) = _
    rw [awayTransCongrLevel_algebraMap]
    exact congrArg (Ideal.Quotient.mk _) (awayTransHom_algebraMap t f C Bf b).symm
  exact RingHom.congr_fun h z

theorem factorPow_awayTransCongrLevel
    (ht : ∀ n : ℕ, IsUnit (Ideal.Quotient.mk ((K.map (algebraMap B Bf)) ^ n) (algebraMap B Bf t)))
    {m n : ℕ} (hle : m ≤ n) (z : Bf ⧸ (K.map (algebraMap B Bf)) ^ n) :
    Ideal.Quotient.factorPow (K.map (algebraMap B C)) hle
        (awayTransCongrLevel K t f Bf C n (ht n) z) =
      awayTransCongrLevel K t f Bf C m (ht m)
        (Ideal.Quotient.factorPow (K.map (algebraMap B Bf)) hle z) := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
  simp only [awayTransCongrLevel_mk, Ideal.Quotient.factor_mk]

/-! ### The isomorphism of completions -/

/-- **Formal transitivity of completed localizations.** If `t` is invertible in every thickening of
`B_f`, i.e. `D(f) ⊆ D(t)` in the formal spectrum `Spf (B_f, K·B_f)`, then inverting `t` as well
does not change the completion:

```
AdicCompletion (K·B_f) B_f ≃+* AdicCompletion (K·C) C ,
```

where `C` is any localization of `B` away from `t · f` — for instance `(B_t)_{f̄}`. -/
def adicAwayTransEquiv
    (ht : ∀ n : ℕ, IsUnit (Ideal.Quotient.mk ((K.map (algebraMap B Bf)) ^ n) (algebraMap B Bf t))) :
    AdicCompletion (K.map (algebraMap B Bf)) Bf ≃+* AdicCompletion (K.map (algebraMap B C)) C :=
  AdicCompletion.congrOfLevelEquiv _ _ (fun n => awayTransCongrLevel K t f Bf C n (ht n))
    (fun {_ _} hle z => factorPow_awayTransCongrLevel K t f Bf C ht hle z)

/-- The isomorphism is the canonical map `awayTransHom` on the image of `B_f`. -/
theorem adicAwayTransEquiv_of
    (ht : ∀ n : ℕ, IsUnit (Ideal.Quotient.mk ((K.map (algebraMap B Bf)) ^ n) (algebraMap B Bf t)))
    (z : Bf) :
    adicAwayTransEquiv K t f Bf C ht (AdicCompletion.of _ Bf z) =
      AdicCompletion.of _ C (awayTransHom t f C Bf z) :=
  AdicCompletion.congrOfLevelEquiv_of _ _ _ _ _ _
    (fun n => awayTransCongrLevel_mk K t f Bf C n (ht n) z)

/-- **The level-`1` form.** It is enough that `t` be invertible in the residue ring `B_f ⧸ K·B_f`,
i.e. that `D(f) ⊆ D(t)` hold on the underlying space of the formal spectrum. -/
def adicAwayTransEquiv'
    (ht : IsUnit (Ideal.Quotient.mk (K.map (algebraMap B Bf)) (algebraMap B Bf t))) :
    AdicCompletion (K.map (algebraMap B Bf)) Bf ≃+* AdicCompletion (K.map (algebraMap B C)) C :=
  adicAwayTransEquiv K t f Bf C (isUnit_mk_pow_of_isUnit_mk _ _ ht)

theorem adicAwayTransEquiv'_of
    (ht : IsUnit (Ideal.Quotient.mk (K.map (algebraMap B Bf)) (algebraMap B Bf t)))
    (z : Bf) :
    adicAwayTransEquiv' K t f Bf C ht (AdicCompletion.of _ Bf z) =
      AdicCompletion.of _ C (awayTransHom t f C Bf z) :=
  adicAwayTransEquiv_of K t f Bf C _ z

end Level

end RingSplit

end
