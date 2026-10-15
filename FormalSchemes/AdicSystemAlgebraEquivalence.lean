/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.AdicSystemAlgebra
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Finite algebras over a complete Noetherian ring are compatible systems of algebras

For a Noetherian `I`-adically complete ring `A`, the functor `C ↦ (C ⧸ I^(n+1) C)ₙ` from finite
commutative `A`-algebras to compatible systems of finite algebras over the thickenings
`A ⧸ I^(n+1)`, `AdicAlgSystem.ofAlgebraFunctor`, is an equivalence of categories,
`AdicAlgSystem.finiteAlgEquivalence`. This is the algebra form of Stacks, Lemma 30.23.1
(Tag 087W): compatible systems of finite algebras algebraize, uniquely, and so do the morphisms
between them.

## Main definitions and results

* `AdicAlgSystem.Hom`, `AdicAlgSystem.category`, `AdicAlgSystem.limitMap`.
* `AdicAlgSystem.FiniteAlgCat`: finite commutative `A`-algebras, as a full subcategory of
  `CommAlgCat A`.
* `AdicAlgSystem.ofAlgebraFunctor`, `AdicAlgSystem.limitIso`.
* `AdicAlgSystem.finiteAlgEquivalence : FiniteAlgCat A ≌ AdicAlgSystem I`.
-/

universe u v

open CategoryTheory

variable {A : Type u} [CommRing A] {I : Ideal A}

namespace AdicAlgSystem

/-- A morphism of compatible systems of algebras. -/
@[ext]
structure Hom (S T : AdicAlgSystem.{u, v} I) where
  /-- The component at level `n`. -/
  app : ∀ n, S.B n →ₐ[A] T.B n
  comm : ∀ n, (app n).comp (S.map n) = (T.map n).comp (app (n + 1))

instance category : Category (AdicAlgSystem.{u, v} I) where
  Hom := Hom
  id S := ⟨fun _ ↦ AlgHom.id A _, fun _ ↦ rfl⟩
  comp f g := ⟨fun n ↦ (g.app n).comp (f.app n), fun n ↦ by
    rw [AlgHom.comp_assoc, f.comm, ← AlgHom.comp_assoc, g.comm, AlgHom.comp_assoc]⟩

@[ext]
theorem hom_ext {S T : AdicAlgSystem.{u, v} I} {f g : S ⟶ T} (h : ∀ n, f.app n = g.app n) :
    f = g :=
  Hom.ext (funext h)

@[simp]
theorem id_app (S : AdicAlgSystem.{u, v} I) (n : ℕ) : Hom.app (𝟙 S) n = AlgHom.id A _ := rfl

@[simp]
theorem comp_app {S T U : AdicAlgSystem.{u, v} I} (f : S ⟶ T) (g : T ⟶ U) (n : ℕ) :
    Hom.app (f ≫ g) n = (g.app n).comp (f.app n) := rfl

/-- An isomorphism of systems from levelwise algebra isomorphisms compatible with the transition
maps. -/
@[simps]
def isoMk {S T : AdicAlgSystem.{u, v} I} (e : ∀ n, S.B n ≃ₐ[A] T.B n)
    (comm : ∀ n, (e n).toAlgHom.comp (S.map n) = (T.map n).comp (e (n + 1)).toAlgHom) :
    S ≅ T where
  hom := ⟨fun n ↦ (e n).toAlgHom, comm⟩
  inv := ⟨fun n ↦ (e n).symm.toAlgHom, fun n ↦ by
    ext x
    obtain ⟨y, rfl⟩ := (e (n + 1)).surjective x
    have := congrArg (fun φ : S.B (n + 1) →ₐ[A] T.B n ↦ φ y) (comm n)
    simp only [AlgHom.comp_apply] at this
    change (e n).symm (T.map n (e (n + 1) y)) = S.map n ((e (n + 1)).symm (e (n + 1) y))
    rw [AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_eq]
    exact this.symm⟩
  hom_inv_id := by
    ext n x
    simp
  inv_hom_id := by
    ext n x
    simp

/-- The map of limits induced by a morphism of systems. -/
def limitMap {S T : AdicAlgSystem.{u, v} I} (f : S ⟶ T) : S.limit →ₐ[A] T.limit :=
  (AlgHom.pi fun n ↦ (f.app n).comp (S.projAlg n)).codRestrict T.limit fun x n ↦ by
    have := congrArg (fun φ : S.B (n + 1) →ₐ[A] T.B n ↦ φ (x.1 (n + 1))) (f.comm n)
    simp only [AlgHom.comp_apply] at this
    change T.map n (f.app (n + 1) (x.1 (n + 1))) = f.app n (x.1 n)
    rw [← this, x.2 n]

@[simp]
theorem projAlg_limitMap {S T : AdicAlgSystem.{u, v} I} (f : S ⟶ T) (n : ℕ) (x : S.limit) :
    T.projAlg n (limitMap f x) = f.app n (S.projAlg n x) := rfl

variable (A) in
/-- Finite commutative `A`-algebras, as an object property of `CommAlgCat A`. -/
def isFinite : ObjectProperty (CommAlgCat.{v} A) := fun C ↦ Module.Finite A C

variable (A) in
/-- The category of finite commutative `A`-algebras. -/
abbrev FiniteAlgCat := (isFinite.{u, v} A).FullSubcategory

instance (C : FiniteAlgCat.{u, v} A) : Module.Finite A C.obj := C.property

section LevelMap

variable (I) {C D E : Type v} [CommRing C] [Algebra A C] [CommRing D] [Algebra A D]
  [CommRing E] [Algebra A E]

theorem map_le_comap_map (f : C →ₐ[A] D) (J : Ideal A) :
    J.map (algebraMap A C) ≤ (J.map (algebraMap A D)).comap f := by
  rw [← Ideal.map_le_iff_le_comap]
  change Ideal.map (f : C →+* D) _ ≤ _
  rw [Ideal.map_map, AlgHom.comp_algebraMap]

/-- The level-`n` component of `C ↦ (C ⧸ I^(n+1) C)ₙ` on a morphism. -/
def levelMapAlg (f : C →ₐ[A] D) (n : ℕ) :
    (C ⧸ (I ^ (n + 1)).map (algebraMap A C)) →ₐ[A] D ⧸ (I ^ (n + 1)).map (algebraMap A D) :=
  Ideal.quotientMapₐ _ f (map_le_comap_map f _)

@[simp]
theorem levelMapAlg_mk (f : C →ₐ[A] D) (n : ℕ) (x : C) :
    levelMapAlg I f n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (f x) := rfl

theorem levelMapAlg_id (n : ℕ) :
    levelMapAlg I (AlgHom.id A C) n = AlgHom.id A _ :=
  Ideal.Quotient.algHom_ext A (AlgHom.ext fun _ ↦ rfl)

theorem levelMapAlg_comp (f : C →ₐ[A] D) (g : D →ₐ[A] E) (n : ℕ) :
    levelMapAlg I (g.comp f) n = (levelMapAlg I g n).comp (levelMapAlg I f n) :=
  Ideal.Quotient.algHom_ext A (AlgHom.ext fun _ ↦ rfl)

variable [Module.Finite A C] [Module.Finite A D]

theorem levelMapAlg_comm (f : C →ₐ[A] D) (n : ℕ) :
    (levelMapAlg I f n).comp ((ofAlgebra I C).map n) =
      ((ofAlgebra I D).map n).comp (levelMapAlg I f (n + 1)) :=
  Ideal.Quotient.algHom_ext A (AlgHom.ext fun _ ↦ rfl)

end LevelMap

variable (I) in
/-- The functor `C ↦ (C ⧸ I^(n+1) C)ₙ` from finite algebras to compatible systems. -/
def ofAlgebraFunctor : FiniteAlgCat.{u, v} A ⥤ AdicAlgSystem.{u, v} I where
  obj C := ofAlgebra I C.obj
  map f := ⟨fun n ↦ levelMapAlg I f.hom.hom n, fun n ↦ levelMapAlg_comm I f.hom.hom n⟩
  map_id _ := hom_ext fun n ↦ levelMapAlg_id I n
  map_comp f g := hom_ext fun n ↦ levelMapAlg_comp I f.hom.hom g.hom.hom n

/-- Every compatible system of finite algebras is isomorphic to the system of its limit. -/
noncomputable def limitIso [IsPrecomplete I A] (S : AdicAlgSystem.{u, v} I) :
    ofAlgebra I S.limit ≅ S :=
  isoMk (fun n ↦ S.quotAlgEquiv n) fun n ↦
    Ideal.Quotient.algHom_ext A (AlgHom.ext fun x ↦ (x.2 n).symm)

variable [IsNoetherianRing A] [IsAdicComplete I A]

instance : (ofAlgebraFunctor I).EssSurj where
  mem_essImage S := ⟨⟨CommAlgCat.of A S.limit, S.limit_finite⟩, ⟨limitIso S⟩⟩

instance : (ofAlgebraFunctor I).Faithful where
  map_injective {C D} f g h := by
    ext x
    apply toLimitAlg_injective I D.obj (IsAdicComplete.le_jacobson_bot I)
    refine Subtype.ext (funext fun n ↦ ?_)
    exact congrArg (fun φ : ofAlgebra I C.obj ⟶ ofAlgebra I D.obj ↦
      φ.app n (Ideal.Quotient.mk _ x)) h

instance : (ofAlgebraFunctor I).Full where
  map_surjective {C D} φ := by
    let g : C.obj →ₐ[A] D.obj :=
      ((algEquivLimit I D.obj).symm.toAlgHom.comp (limitMap φ)).comp (toLimitAlg I C.obj)
    refine ⟨ObjectProperty.homMk (CommAlgCat.ofHom g), hom_ext fun n ↦ ?_⟩
    refine Ideal.Quotient.algHom_ext A (AlgHom.ext fun x ↦ ?_)
    have h : toLimitAlg I D.obj (g x) = limitMap φ (toLimitAlg I C.obj x) :=
      (algEquivLimit I D.obj).apply_symm_apply _
    exact congrArg (fun y ↦ (ofAlgebra I D.obj).projAlg n y) h

instance : (ofAlgebraFunctor I).IsEquivalence where

/-- **Algebraization of compatible systems of finite algebras** (Stacks, Lemma 30.23.1,
Tag 087W, algebra form): for a Noetherian `I`-adically complete ring `A`, finite commutative
`A`-algebras are equivalent to compatible systems of finite algebras over the thickenings
`A ⧸ I^(n+1)`, via `C ↦ (C ⧸ I^(n+1) C)ₙ`. -/
noncomputable def finiteAlgEquivalence : FiniteAlgCat.{u, v} A ≌ AdicAlgSystem.{u, v} I :=
  (ofAlgebraFunctor I).asEquivalence

end AdicAlgSystem
