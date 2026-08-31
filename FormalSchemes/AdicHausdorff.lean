import Mathlib.RingTheory.AdicCompletion.Basic

set_option linter.style.header false

/-!
# Comparing elements of an adic ring modulo every power of the ideal

Two small pieces of glue that the rest of this development was inlining, once per proof.

## The `smul_top` bridge

Mathlib's adic-completion API is stated for `Submodule`s, so it phrases the `I`-adic filtration on
a module `M` as `I ^ n • (⊤ : Submodule R M)`. When `M` is the ring `R` itself that submodule *is*
the ideal `I ^ n`, but not syntactically, and every proof that wants to move between the two spent
four rewrites (`Ideal.smul_top_eq_map`, `Submodule.restrictScalars_mem`, `Algebra.algebraMap_self`,
`Ideal.map_id`) doing so.

`Ideal.smul_top_self` says it once, as an equality of submodules rather than an iff, and it is two
rewrites rather than four: `I • ⊤ = I * ⊤ = I`. Note this is the *self* case only. The genuinely
`R`-versus-`S` statements are two different lemmas, both in
`FormalSchemes/RestrictedPowerSeries.lean`: `Ideal.mem_map_pow_iff_mem_pow_smul_top` says
`x ∈ (K.map (algebraMap B A)) ^ n ↔ x ∈ (K ^ n • ⊤ : Submodule B A)`, and
`Ideal.mem_map_pow_iff_mem_smul_top` says
`x ∈ ((K.map (algebraMap B A)) ^ n • ⊤ : Submodule A A) ↔ x ∈ (K ^ n • ⊤ : Submodule B A)`.

## The Hausdorff comparison idiom

A Hausdorff adic ring is one in which elements agreeing modulo every `I ^ n` are equal, and that
is the last step of a great many proofs here: build a family of equalities in the quotients
`R ⧸ I ^ n`, then conclude in `R`. Mathlib has the function-level `IsHausdorff.funext'`; the
element-level form is `IsHausdorff.eq_of_mk_pow_eq` below, and it is exactly `funext'` at a
one-point index type.

`IsHausdorff.eq_of_mk_pow_succ_eq` is the variant to reach for when the equalities are only
available from level `1` on, which happens whenever the family is indexed by the *thickenings*
`Spec (R ⧸ I ^ (n + 1))` rather than by the quotients directly. The missing level-`0` obligation is
vacuous, since `I ^ 0 = ⊤`, and doing it once here saves a `cases n with | zero => …` tail at every
such call site.

## Main results

* `Ideal.smul_top_self`, `Ideal.mem_smul_top_self_iff`: `I • (⊤ : Submodule R R) = I`.
* `IsHausdorff.eq_of_mk_pow_eq`: **equal modulo every `I ^ n` implies equal.**
* `IsHausdorff.eq_of_mk_pow_succ_eq`: the same, from level `1` on.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. 0, §7.2.
-/

namespace Ideal

variable {R : Type*} [CommSemiring R]

/-- **An ideal acting on the ring itself is that ideal**: `I • (⊤ : Submodule R R) = I`.

Mathlib's adic API phrases the filtration on a module `M` as `I ^ n • (⊤ : Submodule R M)`, so
every use of it on a ring-as-module-over-itself has to cross this bridge. Going through
`Ideal.smul_eq_mul` and `Ideal.mul_top` is shorter than going through `Ideal.smul_top_eq_map` and
back along `Algebra.algebraMap_self`, and it gives an equality of submodules rather than an
iff between memberships. -/
theorem smul_top_self (I : Ideal R) : I • (⊤ : Submodule R R) = I := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top]

/-- The membership form of `Ideal.smul_top_self`, which is the shape the adic-completion API
produces goals in. -/
theorem mem_smul_top_self_iff (I : Ideal R) (z : R) : z ∈ (I • ⊤ : Submodule R R) ↔ z ∈ I := by
  rw [Ideal.smul_top_self]

end Ideal

namespace IsHausdorff

variable {S : Type*} [CommRing S] (I : Ideal S) [IsHausdorff I S]

/-- **Two elements of a Hausdorff adic ring agreeing modulo every power of `I` are equal.**

This is the element-level companion of Mathlib's `IsHausdorff.funext'`, and it is that lemma at a
one-point index type. It is the last step of most of the uniqueness arguments in this
development: produce the family of equalities in the quotients `S ⧸ I ^ n`, then conclude in `S`. -/
theorem eq_of_mk_pow_eq {x y : S}
    (h : ∀ n : ℕ, Ideal.Quotient.mk (I ^ n) x = Ideal.Quotient.mk (I ^ n) y) : x = y :=
  congrFun (IsHausdorff.funext' (R := Unit) I (f := fun _ => x) (g := fun _ => y)
    fun n _ => h n) ()

/-- **`eq_of_mk_pow_eq`, for a family that only starts at level `1`.**

Families indexed by the infinitesimal thickenings `Spec (S ⧸ I ^ (n + 1))` supply their equalities
in that shape, and the missing level-`0` obligation is vacuous because `I ^ 0 = ⊤` makes
`S ⧸ I ^ 0` trivial. Discharging it here removes the `cases n with | zero => …` tail that each such
call site was carrying. -/
theorem eq_of_mk_pow_succ_eq {x y : S}
    (h : ∀ n : ℕ, Ideal.Quotient.mk (I ^ (n + 1)) x = Ideal.Quotient.mk (I ^ (n + 1)) y) :
    x = y := by
  refine eq_of_mk_pow_eq I fun n => ?_
  cases n with
  | zero =>
    refine Ideal.Quotient.eq.mpr ?_
    rw [pow_zero, Ideal.one_eq_top]
    trivial
  | succ m => exact h m

end IsHausdorff
