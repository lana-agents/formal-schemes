import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

set_option linter.style.header false

/-!
# Units in limits of commutative rings

An element of a limit of commutative rings all of whose projections are units is itself a unit:
the inverses of the projections are forced to be compatible (ring homomorphisms send inverses of
units to inverses of units, and inverses are unique), so they assemble into an element of the
limit which is inverse to the given one.

This is the key mechanism by which invertibility propagates through the structure sheaf
`O_{Spf R}` of a formal spectrum, which is an inverse limit of sheaves: a section whose image is
invertible at every finite level is invertible. It replaces the Mittag-Leffler-type arguments of
EGA I, 10.1.6 in our setting.

## Main results

* `CommRingCat.isUnit_of_forall_isUnit_π`: if `c` is a limit cone over `F : J ⥤ CommRingCat`
  and `x : c.pt` has `IsUnit (c.π.app j x)` for every `j`, then `IsUnit x`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CommRingCat

variable {J : Type v} [Category.{v} J] {F : J ⥤ CommRingCat.{max v u}} {c : Cone F}

/-- In a limit of commutative rings, an element all of whose projections are units is a unit:
the inverses of the projections form a compatible family, hence an element of the limit, which
is inverse to the given element. -/
theorem isUnit_of_forall_isUnit_π (hc : IsLimit c) (x : c.pt)
    (h : ∀ j : J, IsUnit (c.π.app j x)) : IsUnit x := by
  classical
  -- the inverses of the projections form a section of `F ⋙ forget CommRingCat`
  choose u hu using h
  have hcompat : ∀ {j j' : J} (φ : j ⟶ j'),
      (F.map φ).hom ((u j)⁻¹ : (F.obj j)ˣ) = ((u j')⁻¹ : (F.obj j')ˣ) := by
    intro j j' φ
    have hx : (F.map φ).hom (c.π.app j x) = c.π.app j' x := by
      have hw := c.π.naturality φ
      simp only [Functor.const_obj_map] at hw
      exact (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hw) x).symm
    have h1 : (F.map φ).hom ((u j : F.obj j) * ((u j)⁻¹ : (F.obj j)ˣ)) = 1 := by
      rw [Units.mul_inv, map_one]
    rw [map_mul] at h1
    have h2 : (c.π.app j' x) * (F.map φ).hom ((u j)⁻¹ : (F.obj j)ˣ) = 1 := by
      rw [← hx, ← hu j]
      exact h1
    calc (F.map φ).hom ((u j)⁻¹ : (F.obj j)ˣ)
        = 1 * (F.map φ).hom ((u j)⁻¹ : (F.obj j)ˣ) := (one_mul _).symm
      _ = (((u j')⁻¹ : (F.obj j')ˣ) * c.π.app j' x) * (F.map φ).hom ((u j)⁻¹ : (F.obj j)ˣ) := by
          rw [← hu j', Units.inv_mul]
      _ = ((u j')⁻¹ : (F.obj j')ˣ) * ((c.π.app j' x) * (F.map φ).hom ((u j)⁻¹ : (F.obj j)ˣ)) :=
          mul_assoc _ _ _
      _ = ((u j')⁻¹ : (F.obj j')ˣ) := by rw [h2, mul_one]
  -- assemble the inverses into an element of the limit
  have hlim : IsLimit ((forget CommRingCat).mapCone c) := isLimitOfPreserves _ hc
  let v : ∀ j : J, (F ⋙ forget CommRingCat).obj j := fun j =>
    (((u j)⁻¹ : (F.obj j)ˣ) : F.obj j)
  let e := Types.isLimitEquivSections hlim
  let y : c.pt := e.symm ⟨v, fun φ => hcompat φ⟩
  have hy : ∀ j, c.π.app j y = ((u j)⁻¹ : (F.obj j)ˣ) := by
    intro j
    have := Types.isLimitEquivSections_apply hlim j (e.symm ⟨v, fun φ => hcompat φ⟩)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  refine IsUnit.of_mul_eq_one y (Concrete.isLimit_ext F hc (x * y) 1 fun j => ?_)
  calc (c.π.app j).hom (x * y)
      = (c.π.app j).hom x * (c.π.app j).hom y := map_mul _ _ _
    _ = (u j : F.obj j) * ((u j)⁻¹ : (F.obj j)ˣ) := by rw [hy j, hu j]
    _ = 1 := Units.mul_inv _
    _ = (c.π.app j).hom 1 := (map_one _).symm

end CommRingCat
