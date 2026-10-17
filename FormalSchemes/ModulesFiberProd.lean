/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.SchemeTwoCech
import FormalSchemes.TwoSetTwist

/-!
# Fibre products of sheaves of modules, with explicit sections

For morphisms `φ : G₀ ⟶ H` and `ψ : G₁ ⟶ H` of `𝒪_X`-modules, `Scheme.Modules.fiberProd φ ψ` is
the sheaf `W ↦ {(a, b) ∈ G₀(W) × G₁(W) | φ a = ψ b}`, with its projections and the universal
morphism into it. The sections are definitionally the pairs, which makes the construction
convenient for gluing.
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {G₀ G₁ H : X.Modules} (φ : G₀ ⟶ H) (ψ : G₁ ⟶ H)

lemma app_res {M N : X.Modules} (χ : M ⟶ N) {U W : X.Opens} (h : W ≤ U) (s : Γ(M, U)) :
    χ.app W (M.presheaf.map (homOfLE h).op s) = N.presheaf.map (homOfLE h).op (χ.app U s) :=
  LinearMap.congr_fun (appℤ_comp_resℤ χ h) s

/-- The pairs `(a, b)` with `φ a = ψ b`. -/
noncomputable def fiberProdObj (W : X.Opens) :
    Submodule (X.ringCatSheaf.obj.obj (op W))
      ((_root_.PresheafOfModules.prod G₀.val G₁.val).obj (op W)) where
  carrier := {p | φ.app W (show Γ(G₀, W) from p.1) = ψ.app W (show Γ(G₁, W) from p.2)}
  add_mem' {p q} hp hq := by
    simp only [Set.mem_setOf_eq] at hp hq ⊢
    change φ.app W ((show Γ(G₀, W) from p.1) + (show Γ(G₀, W) from q.1)) =
      ψ.app W ((show Γ(G₁, W) from p.2) + (show Γ(G₁, W) from q.2))
    rw [map_add, map_add, hp, hq]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    change φ.app W (0 : Γ(G₀, W)) = ψ.app W (0 : Γ(G₁, W))
    rw [map_zero, map_zero]
  smul_mem' r p hp := by
    simp only [Set.mem_setOf_eq] at hp ⊢
    change φ.app W ((show Γ(X, W) from r) • (show Γ(G₀, W) from p.1)) =
      ψ.app W ((show Γ(X, W) from r) • (show Γ(G₁, W) from p.2))
    rw [Hom.app_smul, Hom.app_smul, hp]

/-- The fibre product as a family of submodules stable under restriction. -/
noncomputable def fiberProdSubmodule :
    (_root_.PresheafOfModules.prod G₀.val G₁.val).Submodule where
  obj W := fiberProdObj φ ψ W.unop
  map {W W'} f := by
    rintro ⟨a, b⟩ hp
    change φ.app W.unop a = ψ.app W.unop b at hp
    change φ.app W'.unop (G₀.presheaf.map (homOfLE (leOfHom f.unop)).op a) =
      ψ.app W'.unop (G₁.presheaf.map (homOfLE (leOfHom f.unop)).op b)
    rw [app_res, app_res, hp]

/-- The fibre product as a presheaf of modules. -/
noncomputable def fiberProdPresheaf : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj :=
  (fiberProdSubmodule φ ψ).toPresheafOfModules

lemma fiberProdPresheaf_isSheaf :
    TopCat.Presheaf.IsSheaf (X := X) (fiberProdPresheaf φ ψ).presheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι W sf hsf
  let a : ∀ i, Γ(G₀, W i) := fun i ↦ (sf i).1.1
  let b : ∀ i, Γ(G₁, W i) := fun i ↦ (sf i).1.2
  have hcond : ∀ i, φ.app (W i) (a i) = ψ.app (W i) (b i) := fun i ↦ (sf i).2
  have ha : TopCat.Presheaf.IsCompatible G₀.presheaf W a := fun i j ↦
    congrArg (fun x ↦ x.1.1) (hsf i j)
  have hb : TopCat.Presheaf.IsCompatible G₁.presheaf W b := fun i j ↦
    congrArg (fun x ↦ x.1.2) (hsf i j)
  obtain ⟨sa, hsa, usa⟩ := (TopCat.Sheaf.existsUnique_gluing ⟨G₀.presheaf, G₀.isSheaf⟩ W a ha)
  obtain ⟨sb, hsb, usb⟩ := (TopCat.Sheaf.existsUnique_gluing ⟨G₁.presheaf, G₁.isSheaf⟩ W b hb)
  have hs : φ.app (iSup W) sa = ψ.app (iSup W) sb := by
    refine TopCat.Sheaf.eq_of_locally_eq ⟨H.presheaf, H.isSheaf⟩ W _ _ fun i ↦ ?_
    have e1 := app_res φ (le_iSup W i) sa
    have e2 := app_res ψ (le_iSup W i) sb
    change H.presheaf.map (homOfLE (le_iSup W i)).op _ = H.presheaf.map (homOfLE (le_iSup W i)).op _
    rw [← e1, ← e2]
    have h1 : G₀.presheaf.map (homOfLE (le_iSup W i)).op sa = a i := hsa i
    have h2 : G₁.presheaf.map (homOfLE (le_iSup W i)).op sb = b i := hsb i
    rw [h1, h2, hcond i]
  refine ⟨⟨(sa, sb), hs⟩, fun i ↦ Subtype.ext (Prod.ext (hsa i) (hsb i)), fun s' hs' ↦ ?_⟩
  exact Subtype.ext (Prod.ext (usa _ fun i ↦ congrArg (fun x ↦ x.1.1) (hs' i))
    (usb _ fun i ↦ congrArg (fun x ↦ x.1.2) (hs' i)))

/-- **The fibre product** `G₀ ×_H G₁` of `𝒪_X`-modules, with sections the pairs `(a, b)` with
`φ a = ψ b`. -/
noncomputable def fiberProd : X.Modules where
  val := fiberProdPresheaf φ ψ
  isSheaf := fiberProdPresheaf_isSheaf φ ψ

/-- The first projection `G₀ ×_H G₁ ⟶ G₀`. -/
noncomputable def fiberProd.fst : fiberProd φ ψ ⟶ G₀ :=
  ⟨{ app W := ModuleCat.ofHom (LinearMap.fst _ _ _ ∘ₗ (fiberProdObj φ ψ W.unop).subtype)
     naturality _ := rfl }⟩

/-- The second projection `G₀ ×_H G₁ ⟶ G₁`. -/
noncomputable def fiberProd.snd : fiberProd φ ψ ⟶ G₁ :=
  ⟨{ app W := ModuleCat.ofHom (LinearMap.snd _ _ _ ∘ₗ (fiberProdObj φ ψ W.unop).subtype)
     naturality _ := rfl }⟩

variable {φ ψ}

/-- The morphism into the fibre product given by two morphisms agreeing in `H`. -/
noncomputable def fiberProd.lift {F : X.Modules} (α : F ⟶ G₀) (β : F ⟶ G₁)
    (h : α ≫ φ = β ≫ ψ) : F ⟶ fiberProd φ ψ :=
  ⟨{ app W := ModuleCat.ofHom (LinearMap.codRestrict (fiberProdObj φ ψ W.unop)
        ((α.val.app W).hom.prod (β.val.app W).hom) fun s ↦ by
          change (α ≫ φ).app W.unop s = (β ≫ ψ).app W.unop s
          rw [h])
     naturality f := by
       ext s
       exact Subtype.ext (Prod.ext (congrArg (fun g ↦ ModuleCat.Hom.hom g s) (α.val.naturality f))
         (congrArg (fun g ↦ ModuleCat.Hom.hom g s) (β.val.naturality f))) }⟩

variable {W : X.Opens}

lemma fiberProd.cond (p : Γ(fiberProd φ ψ, W)) :
    φ.app W ((fiberProd.fst φ ψ).app W p) = ψ.app W ((fiberProd.snd φ ψ).app W p) := p.2

lemma fiberProd.ext {p q : Γ(fiberProd φ ψ, W)}
    (h₀ : (fiberProd.fst φ ψ).app W p = (fiberProd.fst φ ψ).app W q)
    (h₁ : (fiberProd.snd φ ψ).app W p = (fiberProd.snd φ ψ).app W q) : p = q :=
  Subtype.ext (Prod.ext h₀ h₁)

/-- The section `(a, b)` of the fibre product. -/
def fiberProd.mk (a : Γ(G₀, W)) (b : Γ(G₁, W)) (h : φ.app W a = ψ.app W b) :
    Γ(fiberProd φ ψ, W) := ⟨(a, b), h⟩

@[simp] lemma fiberProd.fst_mk (a b h) :
    (fiberProd.fst φ ψ).app W (fiberProd.mk (W := W) a b h) = a := rfl

@[simp] lemma fiberProd.snd_mk (a b h) :
    (fiberProd.snd φ ψ).app W (fiberProd.mk (W := W) a b h) = b := rfl

@[simp] lemma fiberProd.fst_lift {F : X.Modules} (α : F ⟶ G₀) (β : F ⟶ G₁) (h) (s : Γ(F, W)) :
    (fiberProd.fst φ ψ).app W ((fiberProd.lift α β h).app W s) = α.app W s := rfl

@[simp] lemma fiberProd.snd_lift {F : X.Modules} (α : F ⟶ G₀) (β : F ⟶ G₁) (h) (s : Γ(F, W)) :
    (fiberProd.snd φ ψ).app W ((fiberProd.lift α β h).app W s) = β.app W s := rfl

lemma fiberProd.lift_fst {F : X.Modules} (α : F ⟶ G₀) (β : F ⟶ G₁) (h) :
    fiberProd.lift α β h ≫ fiberProd.fst φ ψ = α := rfl

lemma fiberProd.lift_snd {F : X.Modules} (α : F ⟶ G₀) (β : F ⟶ G₁) (h) :
    fiberProd.lift α β h ≫ fiberProd.snd φ ψ = β := rfl

end AlgebraicGeometry.Scheme.Modules
