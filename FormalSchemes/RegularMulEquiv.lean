import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Regular.Defs

set_option linter.style.header false

/-!
# Regularity transports along a multiplicative equivalence

`IsLeftRegular c` is `Function.Injective (c * ·)`, so it is preserved and reflected by any
bijection that respects multiplication. Mathlib has no such transfer lemma — `Mathlib.Algebra.
Regular.Basic` relates regularity to products, powers and units, but never to an equivalence — so
it is stated here, at `Mul` and a bare `MulEquiv`, which is the weakest setting it makes sense in.

This is the shape a consumer wants when a ring is presented twice: once as a presheaf section ring,
where nothing about its elements is computable, and once as an explicit completed localization,
where the standard flatness and torsion-freeness arguments apply. Regularity of a *named* element
of such a ring is exactly a statement that transports.
-/

variable {M N : Type*} [Mul M] [Mul N]

/-- **Left-regularity transports along a multiplicative equivalence.** Both directions are the same
argument run through `e` and through `e.symm`.

Stated as an `iff` rather than as two implications because the intended use is rewriting a
regularity hypothesis from one presentation of a ring into another, in whichever direction the
consumer happens to need. -/
theorem MulEquiv.isLeftRegular_apply_iff (e : M ≃* N) {a : M} :
    IsLeftRegular (e a) ↔ IsLeftRegular a := by
  constructor
  · intro h x y hxy
    refine e.injective (h ?_)
    change e a * e x = e a * e y
    rw [← map_mul, ← map_mul]
    exact congrArg e hxy
  · intro h x y hxy
    have hxy' : a * e.symm x = a * e.symm y := by
      refine e.injective ?_
      rw [map_mul, map_mul, e.apply_symm_apply, e.apply_symm_apply]
      exact hxy
    calc x = e (e.symm x) := (e.apply_symm_apply x).symm
      _ = e (e.symm y) := congrArg e (h hxy')
      _ = y := e.apply_symm_apply y

/-- **Right-regularity transports along a multiplicative equivalence**, by the same argument on the
other side. Landed beside the left version so that a consumer who has `IsRegular` does not have to
split it by hand. -/
theorem MulEquiv.isRightRegular_apply_iff (e : M ≃* N) {a : M} :
    IsRightRegular (e a) ↔ IsRightRegular a := by
  constructor
  · intro h x y hxy
    refine e.injective (h ?_)
    change e x * e a = e y * e a
    rw [← map_mul, ← map_mul]
    exact congrArg e hxy
  · intro h x y hxy
    have hxy' : e.symm x * a = e.symm y * a := by
      refine e.injective ?_
      rw [map_mul, map_mul, e.apply_symm_apply, e.apply_symm_apply]
      exact hxy
    calc x = e (e.symm x) := (e.apply_symm_apply x).symm
      _ = e (e.symm y) := congrArg e (h hxy')
      _ = y := e.apply_symm_apply y
