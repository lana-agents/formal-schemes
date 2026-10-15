/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.AdicSystemModule
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.CategoryTheory.Equivalence

/-!
# Finite modules over a complete Noetherian ring are adic systems

Let `A` be a Noetherian ring that is `I`-adically complete. This file proves the algebraic form of
Stacks, Lemma 30.23.1 (Tag 087W) — the affine case of Grothendieck's existence theorem: the functor
`M ↦ (M ⧸ I^(n+1) M)ₙ` from finite `A`-modules to adic systems,
`AdicSystem.ofModuleFunctor`, is an equivalence of categories,
`AdicSystem.fgModuleCatEquivalence`. Its inverse takes an adic system to its limit.

Stacks states the lemma for `Coh(Spec A, I)`, systems of coherent sheaves on `Spec A`; the present
`AdicSystem` records the corresponding systems of modules of global sections, the dictionary
between coherent sheaves on an affine scheme and finite modules being the step this file does not
formalise.

## Main definitions and results

* `AdicSystem.Hom` and the category structure `AdicSystem.category`.
* `AdicSystem.ofModuleFunctor : FGModuleCat A ⥤ AdicSystem I`.
* `AdicSystem.limitIso`: every adic system is isomorphic to the system of its limit.
* `AdicSystem.fgModuleCatEquivalence : FGModuleCat A ≌ AdicSystem I`.
-/

universe u v

open CategoryTheory

variable {A : Type u} [CommRing A] {I : Ideal A}

namespace AdicSystem

/-- A morphism of adic systems: a compatible family of linear maps. -/
@[ext]
structure Hom (S T : AdicSystem.{u, v} I) where
  /-- The component at level `n`. -/
  app : ∀ n, S.obj n ⟶ T.obj n
  comm : ∀ n, S.map n ≫ app n = app (n + 1) ≫ T.map n

attribute [reassoc] Hom.comm

instance category : Category (AdicSystem.{u, v} I) where
  Hom := Hom
  id S := ⟨fun _ ↦ 𝟙 _, fun _ ↦ by simp⟩
  comp f g := ⟨fun n ↦ f.app n ≫ g.app n, fun n ↦ by
    rw [Hom.comm_assoc, Hom.comm, Category.assoc]⟩

@[ext]
theorem hom_ext {S T : AdicSystem.{u, v} I} {f g : S ⟶ T} (h : ∀ n, f.app n = g.app n) :
    f = g :=
  Hom.ext (funext h)

@[simp]
theorem id_app (S : AdicSystem.{u, v} I) (n : ℕ) : Hom.app (𝟙 S) n = 𝟙 _ := rfl

@[simp, reassoc]
theorem comp_app {S T U : AdicSystem.{u, v} I} (f : S ⟶ T) (g : T ⟶ U) (n : ℕ) :
    Hom.app (f ≫ g) n = f.app n ≫ g.app n := rfl

/-- An isomorphism of adic systems from levelwise isomorphisms compatible with the transition
maps. -/
@[simps]
def isoMk {S T : AdicSystem.{u, v} I} (e : ∀ n, S.obj n ≅ T.obj n)
    (comm : ∀ n, S.map n ≫ (e n).hom = (e (n + 1)).hom ≫ T.map n) : S ≅ T where
  hom := ⟨fun n ↦ (e n).hom, comm⟩
  inv := ⟨fun n ↦ (e n).inv, fun n ↦ by
    rw [Iso.comp_inv_eq, Category.assoc, comm, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp]⟩

variable (I)

/-- The level-`n` component of the functor `M ↦ (M ⧸ I^(n+1) M)ₙ` on a morphism. -/
def levelMap {M N : Type v} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) (n : ℕ) :
    (M ⧸ (I ^ (n + 1) • ⊤ : Submodule A M)) →ₗ[A] N ⧸ (I ^ (n + 1) • ⊤ : Submodule A N) :=
  Submodule.mapQ _ _ f (Submodule.smul_top_le_comap_smul_top _ f)

@[simp]
theorem levelMap_mk {M N : Type v} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) (n : ℕ) (x : M) :
    levelMap I f n (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) := rfl

section LevelMap

variable {M N P : Type v} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  [AddCommGroup P] [Module A P]

theorem factor_comp_levelMap (f : M →ₗ[A] N) (n : ℕ) :
    Submodule.factor (pow_succ_smul_le (M := N) I n) ∘ₗ levelMap I f (n + 1) =
      levelMap I f n ∘ₗ Submodule.factor (pow_succ_smul_le (M := M) I n) := by
  ext x
  rfl

theorem levelMap_id (n : ℕ) : levelMap I (LinearMap.id : M →ₗ[A] M) n = LinearMap.id := by
  ext x
  rfl

theorem levelMap_comp (f : M →ₗ[A] N) (g : N →ₗ[A] P) (n : ℕ) :
    levelMap I (g ∘ₗ f) n = levelMap I g n ∘ₗ levelMap I f n := by
  ext x
  rfl

end LevelMap

/-- The functor `M ↦ (M ⧸ I^(n+1) M)ₙ` from finite modules to adic systems. -/
def ofModuleFunctor : FGModuleCat.{v} A ⥤ AdicSystem.{u, v} I where
  obj M := ofModule I M
  map f := ⟨fun n ↦ ModuleCat.ofHom (levelMap I f.hom.hom n), fun n ↦
    ModuleCat.hom_ext (factor_comp_levelMap I f.hom.hom n).symm⟩
  map_id _ := hom_ext fun n ↦ ModuleCat.hom_ext (levelMap_id I n)
  map_comp f g := hom_ext fun n ↦ ModuleCat.hom_ext (levelMap_comp I f.hom.hom g.hom.hom n)

@[simp]
theorem ofModuleFunctor_obj (M : FGModuleCat.{v} A) : (ofModuleFunctor I).obj M = ofModule I M :=
  rfl

variable {I}

/-- Every adic system is isomorphic to the adic system of its limit (Stacks, Tag 09B8). -/
noncomputable def limitIso [IsPrecomplete I A] (S : AdicSystem.{u, v} I) :
    ofModule I S.limit ≅ S :=
  isoMk (fun n ↦ (S.quotEquiv n).toModuleIso) fun n ↦ by
    ext m
    exact (S.map_proj n m).symm

variable [IsNoetherianRing A] [IsAdicComplete I A]

instance : (ofModuleFunctor I).EssSurj where
  mem_essImage S := ⟨FGModuleCat.of A S.limit, ⟨limitIso S⟩⟩

instance : (ofModuleFunctor I).Faithful where
  map_injective {M N} f g h := by
    ext x
    apply toLimit_injective I N (IsAdicComplete.le_jacobson_bot I)
    refine Subtype.ext (funext fun n ↦ ?_)
    have := congrArg (fun φ : ofModule I M ⟶ ofModule I N ↦ (φ.app n).hom
      (Submodule.Quotient.mk x)) h
    exact this

/-- The map to the limit of the adic system of `N` determined by a morphism of adic systems. -/
def limitMap {M N : FGModuleCat.{v} A} (φ : ofModule I M ⟶ ofModule I N) :
    M →ₗ[A] (ofModule I N).limit :=
  LinearMap.codRestrict (ofModule I N).limit
    (LinearMap.pi fun n ↦ (φ.app n).hom ∘ₗ (I ^ (n + 1) • ⊤ : Submodule A M).mkQ) fun x n ↦ by
      exact (congrArg (fun ψ : (ofModule I M).obj (n + 1) ⟶ (ofModule I N).obj n ↦
        ψ.hom (Submodule.Quotient.mk x)) (φ.comm n)).symm

instance : (ofModuleFunctor I).Full where
  map_surjective {M N} φ := by
    let e := LinearEquiv.ofBijective (toLimit I N) (toLimit_bijective I N)
    refine ⟨FGModuleCat.ofHom (e.symm.toLinearMap ∘ₗ limitMap φ), ?_⟩
    ext n x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I ^ (n + 1) • ⊤ : Submodule A M) x
    have h : toLimit I N (e.symm (limitMap φ x)) = limitMap φ x := e.apply_symm_apply _
    exact congrArg (fun y ↦ (ofModule I N).proj n y) h

instance : (ofModuleFunctor I).IsEquivalence where

/-- **Affine Grothendieck existence** (Stacks, Lemma 30.23.1, Tag 087W, in its module form): for
a Noetherian `I`-adically complete ring `A`, finite `A`-modules are equivalent to adic systems of
finite modules over the thickenings `A ⧸ I^(n+1)`, via `M ↦ (M ⧸ I^(n+1) M)ₙ`. -/
noncomputable def fgModuleCatEquivalence : FGModuleCat.{v} A ≌ AdicSystem.{u, v} I :=
  (ofModuleFunctor I).asEquivalence

end AdicSystem
