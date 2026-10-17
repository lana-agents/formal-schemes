/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartModuleAdic

/-!
# The category of chart modules

`ProjectiveLine.ChartModule A` with its morphisms `ChartModule.Hom` is a category; a morphism which
is bijective on all three charts is an isomorphism (`ChartModule.Hom.isIso_of_bijective`).
-/

universe u

open CategoryTheory

namespace ProjectiveLine

namespace ChartModule

variable {A : Type u} [CommRing A]

instance : Category (ChartModule A) where
  Hom := Hom
  id := Hom.id
  comp f g := g.comp f
  id_comp f := Hom.comp_id f
  comp_id f := Hom.id_comp f
  assoc f g h := (Hom.comp_assoc h g f).symm

variable {M N : ChartModule A}

lemma comp_eq (f : M ⟶ N) {P : ChartModule A} (g : N ⟶ P) :
    f ≫ g = Hom.comp (M := M) (N := N) (P := P) g f := rfl

lemma id_eq (M : ChartModule A) : 𝟙 M = Hom.id M := rfl

lemma apply_ofBijective_symm {P Q : Type u} [AddCommGroup P] [Module A P] [AddCommGroup Q]
    [Module A Q] (f : P →ₗ[A] Q) (hf : Function.Bijective f) (y : Q) :
    f ((LinearEquiv.ofBijective f hf).symm y) = y :=
  (LinearEquiv.ofBijective f hf).apply_symm_apply y

/-- The inverse of a morphism of chart modules which is bijective on the charts. -/
noncomputable def Hom.invOfBijective (φ : Hom M N) (h0 : Function.Bijective φ.f0)
    (h1 : Function.Bijective φ.f1) (h01 : Function.Bijective φ.f01) : Hom N M where
  f0 := (LinearEquiv.ofBijective φ.f0 h0).symm.toLinearMap
  f1 := (LinearEquiv.ofBijective φ.f1 h1).symm.toLinearMap
  f01 := (LinearEquiv.ofBijective φ.f01 h01).symm.toLinearMap
  comm_x0 m := (LinearEquiv.ofBijective φ.f0 h0).injective (by
    change φ.f0 ((LinearEquiv.ofBijective φ.f0 h0).symm (N.x0 m)) =
      φ.f0 (M.x0 ((LinearEquiv.ofBijective φ.f0 h0).symm m))
    rw [φ.comm_x0, apply_ofBijective_symm,
      apply_ofBijective_symm])
  comm_x1 m := (LinearEquiv.ofBijective φ.f1 h1).injective (by
    change φ.f1 ((LinearEquiv.ofBijective φ.f1 h1).symm (N.x1 m)) =
      φ.f1 (M.x1 ((LinearEquiv.ofBijective φ.f1 h1).symm m))
    rw [φ.comm_x1, apply_ofBijective_symm,
      apply_ofBijective_symm])
  comm_t z := (LinearEquiv.ofBijective φ.f01 h01).injective (by
    change φ.f01 ((LinearEquiv.ofBijective φ.f01 h01).symm (N.t z)) =
      φ.f01 (M.t ((LinearEquiv.ofBijective φ.f01 h01).symm z))
    rw [φ.comm_t, apply_ofBijective_symm,
      apply_ofBijective_symm])
  comm_r0 m := (LinearEquiv.ofBijective φ.f01 h01).injective (by
    change φ.f01 ((LinearEquiv.ofBijective φ.f01 h01).symm (N.r0 m)) =
      φ.f01 (M.r0 ((LinearEquiv.ofBijective φ.f0 h0).symm m))
    rw [φ.comm_r0, apply_ofBijective_symm,
      apply_ofBijective_symm])
  comm_r1 m := (LinearEquiv.ofBijective φ.f01 h01).injective (by
    change φ.f01 ((LinearEquiv.ofBijective φ.f01 h01).symm (N.r1 m)) =
      φ.f01 (M.r1 ((LinearEquiv.ofBijective φ.f1 h1).symm m))
    rw [φ.comm_r1, apply_ofBijective_symm,
      apply_ofBijective_symm])

lemma Hom.isIso_of_bijective (φ : M ⟶ N) (h0 : Function.Bijective (Hom.f0 φ))
    (h1 : Function.Bijective (Hom.f1 φ)) (h01 : Function.Bijective (Hom.f01 φ)) : IsIso φ :=
  ⟨⟨Hom.invOfBijective φ h0 h1 h01,
    Hom.ext' (LinearMap.ext fun m ↦ (LinearEquiv.ofBijective _ h0).symm_apply_apply m)
      (LinearMap.ext fun m ↦ (LinearEquiv.ofBijective _ h1).symm_apply_apply m)
      (LinearMap.ext fun m ↦ (LinearEquiv.ofBijective _ h01).symm_apply_apply m),
    Hom.ext' (LinearMap.ext fun m ↦ (LinearEquiv.ofBijective _ h0).apply_symm_apply m)
      (LinearMap.ext fun m ↦ (LinearEquiv.ofBijective _ h1).apply_symm_apply m)
      (LinearMap.ext fun m ↦ (LinearEquiv.ofBijective _ h01).apply_symm_apply m)⟩⟩

end ChartModule

end ProjectiveLine
