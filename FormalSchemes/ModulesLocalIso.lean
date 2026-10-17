/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.Stalks

/-!
# Morphisms of sheaves of modules that are locally bijective on sections

A morphism of `𝒪_X`-modules which is bijective on the sections over all small enough opens around
every point is bijective on all sections (`Scheme.Modules.app_bijective_of_locally`), hence an
isomorphism (`Scheme.Modules.isIso_of_locally`).
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules}

/-- A morphism bijective on sections over all opens inside a neighbourhood of every point of `V`
is bijective on the sections over `V`. -/
lemma app_bijective_of_locally (φ : M ⟶ N) (V : X.Opens)
    (h : ∀ x ∈ V, ∃ U : X.Opens, x ∈ U ∧ ∀ W ≤ U, Function.Bijective (φ.app W)) :
    Function.Bijective (φ.app V) := by
  let PF : TopCat.Presheaf Ab X := M.presheaf
  let PG : TopCat.Presheaf Ab X := N.presheaf
  let β : PF ⟶ PG := φ.mapPresheaf
  let F : TopCat.Sheaf Ab X := ⟨PF, M.isSheaf⟩
  let G : TopCat.Sheaf Ab X := ⟨PG, N.isSheaf⟩
  let α : F ⟶ G := ObjectProperty.homMk β
  have nat : ∀ {W W' : Opens X} (i : W' ⟶ W) (s : ToType (PF.obj (op W))),
      β.app (op W') (PF.map i.op s) = PG.map i.op (β.app (op W) s) := fun i s ↦ by
    rw [← ConcreteCategory.comp_apply, β.naturality, ConcreteCategory.comp_apply]
  refine TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective α V fun x hx ↦ ⟨?_, ?_⟩
  · change Function.Injective ((TopCat.Presheaf.stalkFunctor Ab x).map β)
    refine (injective_iff_map_eq_zero _).2 fun y hy ↦ ?_
    obtain ⟨W, hxW, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq PF y
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hy
    obtain ⟨W', hxW', iU, iV, e⟩ := TopCat.Presheaf.germ_eq PG x hxW hxW _ 0
      (hy.trans (map_zero _).symm)
    obtain ⟨U, hxU, hU⟩ := h x hx
    let i1 : W' ⊓ U ⟶ W' := homOfLE inf_le_left
    have hs : β.app (op (W' ⊓ U)) (PF.map i1.op (PF.map iU.op s)) = β.app (op (W' ⊓ U)) 0 :=
      (nat i1 _).trans ((congrArg (PG.map i1.op) ((nat iU s).trans e)).trans
        ((congrArg (PG.map i1.op) (map_zero (PG.map iV.op).hom)).trans
          ((map_zero (PG.map i1.op).hom).trans (map_zero (β.app _).hom).symm)))
    have h0 := (hU _ inf_le_right).1 hs
    exact ((TopCat.Presheaf.germ_res_apply PF iU x hxW' s).symm.trans
      (TopCat.Presheaf.germ_res_apply PF i1 x (show x ∈ W' ⊓ U from ⟨hxW', hxU⟩) _).symm).trans
      ((congrArg (PF.germ _ x (show x ∈ W' ⊓ U from ⟨hxW', hxU⟩)) h0).trans (map_zero _))
  · change Function.Surjective ((TopCat.Presheaf.stalkFunctor Ab x).map β)
    intro z
    obtain ⟨W, hxW, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq PG z
    obtain ⟨U, hxU, hU⟩ := h x hx
    obtain ⟨s, hs⟩ := (hU (W ⊓ U) inf_le_right).2 (PG.map (homOfLE inf_le_left).op t)
    refine ⟨PF.germ _ x (show x ∈ W ⊓ U from ⟨hxW, hxU⟩) s, ?_⟩
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply _ x _ β s).trans
      ((congrArg (PG.germ _ x _) hs).trans (TopCat.Presheaf.germ_res_apply PG _ x _ t))

/-- A morphism of modules that is bijective on sections over all opens inside the members of an
open covering is an isomorphism. -/
lemma isIso_of_locally (φ : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∀ W ≤ U, Function.Bijective (φ.app W)) : IsIso φ := by
  rw [Hom.isIso_iff_isIso_app]
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  exact app_bijective_of_locally φ V fun x _ ↦ h x

end AlgebraicGeometry.Scheme.Modules
