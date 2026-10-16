/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.SchemeTwoCech
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward

/-!
# Twisting a sheaf of modules along a two-set covering

Let `X` be a scheme, `U`, `V` two opens and `τ ∈ Γ(X, U ∩ V)`. For an `𝒪_X`-module `M`, the
*twist* `M(τ)` is the `𝒪_X`-module whose sections over `W` are the pairs
`(s, t) ∈ M(U ∩ W) × M(V ∩ W)` with `s = τ · t` on `U ∩ V ∩ W`. When `τ` is a unit, `M(τ)` is
obtained by regluing `M|_U` and `M|_V` along multiplication by `τ` on the overlap; for `M = 𝒪_X`
these are the invertible sheaves trivialised on `U` and `V`, with transition function `τ`
(Stacks, Section 17.25, Tag 01CR, and Lemma 6.33.2, Tag 00AL, for gluing). On `ℙ¹_A`, with
`U = D₊(x₀)`, `V = D₊(x₁)` and `τ = (x₁/x₀)^d`, `𝒪(τ)` is Serre's twisting sheaf `𝒪(d)` and
`M(τ) = M ⊗ 𝒪(d)` (Stacks, Lemma 27.10.3, Tag 01MQ: `𝒪(d)` is trivialised on `D₊(x_k)` by `x_kᵈ`).

Main definitions:
* `PresheafOfModules.prod`: the sectionwise product of two presheaves of modules;
* `AlgebraicGeometry.Scheme.Modules.inter M U`: the presheaf of modules `W ↦ M(U ∩ W)`;
* `AlgebraicGeometry.Scheme.Modules.twist M U V τ`: the twist, as an `𝒪_X`-module.
-/

universe v u u₁ v₁

open CategoryTheory Opposite TopologicalSpace

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- The sectionwise product `X ↦ M(X) × N(X)` of two presheaves of modules. -/
@[simps obj]
noncomputable def prod (M N : PresheafOfModules.{v} R) : PresheafOfModules.{v} R where
  obj X := ModuleCat.of (R.obj X) (M.obj X × N.obj X)
  map {X Y} f := ModuleCat.semilinearMapAddEquiv _ _ _
    { toFun p := (M.map f p.1, N.map f p.2)
      map_add' p q := Prod.ext (map_add _ _ _) (map_add _ _ _)
      map_smul' r p := by simp }
  map_id X := by
    refine ModuleCat.hom_ext
      (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun p ↦ Prod.ext ?_ ?_))
    · change M.map (𝟙 X) p.1 = p.1
      simp
    · change N.map (𝟙 X) p.2 = p.2
      simp
  map_comp f g := by
    refine ModuleCat.hom_ext
      (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun p ↦ Prod.ext ?_ ?_))
    · exact M.map_comp_apply f g p.1
    · exact N.map_comp_apply f g p.2

@[simp]
lemma prod_map_apply (M N : PresheafOfModules.{v} R) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (p : M.obj X × N.obj X) : (prod M N).map f p = (M.map f p.1, N.map f p.2) := rfl

end PresheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Restriction maps compose: a restriction followed by a restriction is a restriction. -/
lemma presheaf_map_map (M : X.Modules) {U W T : X.Opens} (i : W ⟶ U) (j : T ⟶ W) (k : T ⟶ U)
    (s : Γ(M, U)) : M.presheaf.map j.op (M.presheaf.map i.op s) = M.presheaf.map k.op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

lemma ringCatSheaf_map_comp {a b c : X.Opensᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) (k : a ⟶ c) :
    X.ringCatSheaf.obj.map f ≫ X.ringCatSheaf.obj.map g = X.ringCatSheaf.obj.map k := by
  rw [← Functor.map_comp]
  congr 1

@[simp]
lemma presheaf_map_map_comp (M : X.Modules) {U W T : X.Opens} (i : W ⟶ U) (j : T ⟶ W)
    (s : Γ(M, U)) : M.presheaf.map j.op (M.presheaf.map i.op s) = M.presheaf.map (j ≫ i).op s :=
  presheaf_map_map M i j _ s

@[simp]
lemma scheme_presheaf_map_map_comp {U W T : X.Opens} (i : W ⟶ U) (j : T ⟶ W) (s : Γ(X, U)) :
    X.presheaf.map j.op (X.presheaf.map i.op s) = X.presheaf.map (j ≫ i).op s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

lemma presheaf_map_congr (M : X.Modules) {U W : X.Opens} (i j : W ⟶ U) (s : Γ(M, U)) :
    M.presheaf.map i.op s = M.presheaf.map j.op s := by
  rw [Subsingleton.elim i j]

lemma scheme_presheaf_map_congr {U W : X.Opens} (i j : W ⟶ U) (s : Γ(X, U)) :
    X.presheaf.map i.op s = X.presheaf.map j.op s := by
  rw [Subsingleton.elim i j]

/-- The functor `W ↦ U ∩ W` on the opens of `X`. -/
@[simps]
def interFunctor (U : X.Opens) : X.Opens ⥤ X.Opens where
  obj W := U ⊓ W
  map h := homOfLE (inf_le_inf_left U (leOfHom h))

/-- The restriction `𝒪_X(W) → 𝒪_X(U ∩ W)`, as a morphism of presheaves of rings. -/
@[simps]
noncomputable def interRingHom (U : X.Opens) :
    X.ringCatSheaf.obj ⟶ (interFunctor U).op ⋙ X.ringCatSheaf.obj where
  app W := X.ringCatSheaf.obj.map (homOfLE inf_le_right : U ⊓ W.unop ⟶ W.unop).op
  naturality W W' h := by
    simp only [Functor.comp_map, Functor.op_map]
    exact (ringCatSheaf_map_comp _ _ (h ≫ (homOfLE inf_le_right).op)).trans
      (ringCatSheaf_map_comp _ _ _).symm

/-- The presheaf of `𝒪_X`-modules `W ↦ M(U ∩ W)`. -/
noncomputable def inter (M : X.Modules) (U : X.Opens) :
    _root_.PresheafOfModules.{u} X.ringCatSheaf.obj :=
  (_root_.PresheafOfModules.pushforward (interRingHom U)).obj M.val

lemma inter_smul (M : X.Modules) (U : X.Opens) (W : X.Opens) (r : X.ringCatSheaf.obj.obj (op W))
    (s : (inter M U).obj (op W)) :
    r • s = (X.presheaf.map (homOfLE inf_le_right : U ⊓ W ⟶ W).op r • (show Γ(M, U ⊓ W) from s)) :=
  rfl

lemma inter_map (M : X.Modules) (U : X.Opens) {W W' : X.Opens} (h : W' ⟶ W)
    (s : (inter M U).obj (op W)) :
    (inter M U).map h.op s =
      M.presheaf.map (homOfLE (inf_le_inf_left U (leOfHom h))).op (show Γ(M, U ⊓ W) from s) :=
  rfl

variable (M : X.Modules) (U V : X.Opens) (τ : Γ(X, U ⊓ V))

/-- The sections `(s, t) ∈ M(U ∩ W) × M(V ∩ W)` with `s = τ t` on `U ∩ V ∩ W`. -/
noncomputable def twistObj (W : X.Opens) :
    Submodule (X.ringCatSheaf.obj.obj (op W))
      ((_root_.PresheafOfModules.prod (inter M U) (inter M V)).obj (op W)) where
  carrier := {p | M.presheaf.map (homOfLE (inf_le_inf_right W inf_le_left) :
      (U ⊓ V) ⊓ W ⟶ U ⊓ W).op (show Γ(M, U ⊓ W) from p.1) =
      X.presheaf.map (homOfLE inf_le_left : (U ⊓ V) ⊓ W ⟶ U ⊓ V).op τ •
        M.presheaf.map (homOfLE (inf_le_inf_right W inf_le_right) :
          (U ⊓ V) ⊓ W ⟶ V ⊓ W).op (show Γ(M, V ⊓ W) from p.2)}
  add_mem' {p q} hp hq := by
    simp only [Set.mem_setOf_eq] at hp hq ⊢
    change M.presheaf.map _ ((show Γ(M, U ⊓ W) from p.1) + (show Γ(M, U ⊓ W) from q.1)) =
      _ • M.presheaf.map _ ((show Γ(M, V ⊓ W) from p.2) + (show Γ(M, V ⊓ W) from q.2))
    rw [map_add, map_add, smul_add, hp, hq]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    change M.presheaf.map _ (0 : Γ(M, U ⊓ W)) = _ • M.presheaf.map _ (0 : Γ(M, V ⊓ W))
    rw [map_zero, map_zero, smul_zero]
  smul_mem' r p hp := by
    obtain ⟨a, b⟩ := p
    simp only [Set.mem_setOf_eq] at hp ⊢
    change M.presheaf.map _ (X.presheaf.map (homOfLE inf_le_right : U ⊓ W ⟶ W).op r •
        (show Γ(M, U ⊓ W) from a)) = _ • M.presheaf.map _
          (X.presheaf.map (homOfLE inf_le_right : V ⊓ W ⟶ W).op r • (show Γ(M, V ⊓ W) from b))
    rw [map_smul, map_smul, hp, smul_smul, smul_smul, mul_comm]
    congr 2
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp]
    rfl

/-- The twist, as a family of submodules of `W ↦ M(U ∩ W) × M(V ∩ W)` stable under
restriction. -/
noncomputable def twistSubmodule :
    (_root_.PresheafOfModules.prod (inter M U) (inter M V)).Submodule where
  obj W := twistObj M U V τ W.unop
  map {W W'} f := by
    rintro ⟨a, b⟩ hp
    change M.presheaf.map (homOfLE (inf_le_inf_right W.unop inf_le_left) :
        (U ⊓ V) ⊓ W.unop ⟶ U ⊓ W.unop).op a =
      X.presheaf.map (homOfLE inf_le_left : (U ⊓ V) ⊓ W.unop ⟶ U ⊓ V).op τ •
        M.presheaf.map (homOfLE (inf_le_inf_right W.unop inf_le_right) :
          (U ⊓ V) ⊓ W.unop ⟶ V ⊓ W.unop).op b at hp
    change M.presheaf.map (homOfLE (inf_le_inf_right W'.unop inf_le_left) :
        (U ⊓ V) ⊓ W'.unop ⟶ U ⊓ W'.unop).op
          (M.presheaf.map (homOfLE (inf_le_inf_left U (leOfHom f.unop))).op a) =
      X.presheaf.map (homOfLE inf_le_left : (U ⊓ V) ⊓ W'.unop ⟶ U ⊓ V).op τ •
        M.presheaf.map (homOfLE (inf_le_inf_right W'.unop inf_le_right) :
          (U ⊓ V) ⊓ W'.unop ⟶ V ⊓ W'.unop).op
            (M.presheaf.map (homOfLE (inf_le_inf_left V (leOfHom f.unop))).op b)
    have hc : (U ⊓ V) ⊓ W'.unop ≤ (U ⊓ V) ⊓ W.unop := inf_le_inf_left _ (leOfHom f.unop)
    rw [presheaf_map_map M _ _ (homOfLE (hc.trans (inf_le_inf_right _ inf_le_left))),
      ← presheaf_map_map M (homOfLE (inf_le_inf_right _ inf_le_left)) (homOfLE hc), hp,
      map_smul, presheaf_map_map M _ _ (homOfLE (hc.trans (inf_le_inf_right _ inf_le_right))),
      presheaf_map_map M _ _ (homOfLE (hc.trans (inf_le_inf_right _ inf_le_right)))]
    congr 1
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

/-- The twist `M(τ)` as a presheaf of `𝒪_X`-modules. -/
noncomputable def twistPresheaf : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj :=
  (twistSubmodule M U V τ).toPresheafOfModules

/-- A sheaf of `𝒪_X`-modules as a sheaf of abelian groups on the underlying space. -/
noncomputable def toTopSheaf (M : X.Modules) : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩

/-- Gluing sections of `M` over the opens `U ∩ W_i`. -/
lemma existsUnique_gluing_inter (M : X.Modules) (U : X.Opens) {ι : Type u} (W : ι → X.Opens)
    (a : ∀ i, Γ(M, U ⊓ W i))
    (h : ∀ i j, M.presheaf.map (homOfLE (inf_le_inf_left U inf_le_left) :
        U ⊓ (W i ⊓ W j) ⟶ U ⊓ W i).op (a i) =
      M.presheaf.map (homOfLE (inf_le_inf_left U inf_le_right) :
        U ⊓ (W i ⊓ W j) ⟶ U ⊓ W j).op (a j)) :
    ∃! s : Γ(M, U ⊓ iSup W), ∀ i,
      M.presheaf.map (homOfLE (inf_le_inf_left U (le_iSup W i))).op s = a i := by
  refine (toTopSheaf M).existsUnique_gluing' (fun i ↦ U ⊓ W i) (U ⊓ iSup W)
    (fun i ↦ homOfLE (inf_le_inf_left U (le_iSup W i))) (by rw [inf_iSup_eq]) a ?_
  intro i j
  have hij : (U ⊓ W i) ⊓ (U ⊓ W j) ≤ U ⊓ (W i ⊓ W j) := fun x hx ↦ ⟨hx.1.1, hx.1.2, hx.2.2⟩
  have := congr(M.presheaf.map (homOfLE hij).op $(h i j))
  rw [presheaf_map_map M _ _ (TopologicalSpace.Opens.infLELeft _ _),
    presheaf_map_map M _ _ (TopologicalSpace.Opens.infLERight _ _)] at this
  exact this

/-- Two sections of `M` over `U ∩ ⋃ W_i` agreeing on every `U ∩ W_i` are equal. -/
lemma eq_of_locally_eq_inter (M : X.Modules) (U : X.Opens) {ι : Type u} (W : ι → X.Opens)
    (s t : Γ(M, U ⊓ iSup W))
    (h : ∀ i, M.presheaf.map (homOfLE (inf_le_inf_left U (le_iSup W i))).op s =
      M.presheaf.map (homOfLE (inf_le_inf_left U (le_iSup W i))).op t) : s = t :=
  (toTopSheaf M).eq_of_locally_eq' (fun i ↦ U ⊓ W i) (U ⊓ iSup W)
    (fun i ↦ homOfLE (inf_le_inf_left U (le_iSup W i))) (by rw [inf_iSup_eq]) s t h

lemma twistPresheaf_isSheaf :
    TopCat.Presheaf.IsSheaf (X := X) (twistPresheaf M U V τ).presheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι W sf hsf
  let a : ∀ i, Γ(M, U ⊓ W i) := fun i ↦ (sf i).1.1
  let b : ∀ i, Γ(M, V ⊓ W i) := fun i ↦ (sf i).1.2
  have hcond : ∀ i, M.presheaf.map (homOfLE (inf_le_inf_right (W i) inf_le_left) :
      (U ⊓ V) ⊓ W i ⟶ U ⊓ W i).op (a i) =
      X.presheaf.map (homOfLE inf_le_left : (U ⊓ V) ⊓ W i ⟶ U ⊓ V).op τ •
        M.presheaf.map (homOfLE (inf_le_inf_right (W i) inf_le_right) :
          (U ⊓ V) ⊓ W i ⟶ V ⊓ W i).op (b i) := fun i ↦ (sf i).2
  have ha : ∀ i j, M.presheaf.map (homOfLE (inf_le_inf_left U inf_le_left) :
        U ⊓ (W i ⊓ W j) ⟶ U ⊓ W i).op (a i) =
      M.presheaf.map (homOfLE (inf_le_inf_left U inf_le_right) :
        U ⊓ (W i ⊓ W j) ⟶ U ⊓ W j).op (a j) := fun i j ↦ congrArg (fun x ↦ x.1.1) (hsf i j)
  have hb : ∀ i j, M.presheaf.map (homOfLE (inf_le_inf_left V inf_le_left) :
        V ⊓ (W i ⊓ W j) ⟶ V ⊓ W i).op (b i) =
      M.presheaf.map (homOfLE (inf_le_inf_left V inf_le_right) :
        V ⊓ (W i ⊓ W j) ⟶ V ⊓ W j).op (b j) := fun i j ↦ congrArg (fun x ↦ x.1.2) (hsf i j)
  obtain ⟨sa, hsa, usa⟩ := existsUnique_gluing_inter M U W a ha
  obtain ⟨sb, hsb, usb⟩ := existsUnique_gluing_inter M V W b hb
  have hs : M.presheaf.map (homOfLE (inf_le_inf_right (iSup W) inf_le_left) :
      (U ⊓ V) ⊓ iSup W ⟶ U ⊓ iSup W).op sa =
      X.presheaf.map (homOfLE inf_le_left : (U ⊓ V) ⊓ iSup W ⟶ U ⊓ V).op τ •
        M.presheaf.map (homOfLE (inf_le_inf_right (iSup W) inf_le_right) :
          (U ⊓ V) ⊓ iSup W ⟶ V ⊓ iSup W).op sb := by
    apply eq_of_locally_eq_inter M (U ⊓ V) W
    intro i
    have k1 : (U ⊓ V) ⊓ W i ≤ U ⊓ iSup W := inf_le_inf inf_le_left (le_iSup W i)
    have k2 : (U ⊓ V) ⊓ W i ≤ V ⊓ iSup W := inf_le_inf inf_le_right (le_iSup W i)
    rw [map_smul, presheaf_map_map M _ _ (homOfLE k1),
      ← presheaf_map_map M (homOfLE (inf_le_inf_left U (le_iSup W i)))
        (homOfLE (inf_le_inf_right (W i) inf_le_left)) (homOfLE k1), hsa i,
      presheaf_map_map M _ _ (homOfLE k2),
      ← presheaf_map_map M (homOfLE (inf_le_inf_left V (le_iSup W i)))
        (homOfLE (inf_le_inf_right (W i) inf_le_right)) (homOfLE k2), hsb i, hcond i]
    congr 1
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  refine ⟨⟨(sa, sb), hs⟩, fun i ↦ Subtype.ext (Prod.ext (hsa i) (hsb i)), fun s' hs' ↦ ?_⟩
  exact Subtype.ext (Prod.ext (usa _ fun i ↦ congrArg (fun x ↦ x.1.1) (hs' i))
    (usb _ fun i ↦ congrArg (fun x ↦ x.1.2) (hs' i)))

/-- **The twist `M(τ)`** of an `𝒪_X`-module `M` along the two opens `U`, `V` by
`τ ∈ Γ(X, U ∩ V)`: its sections over `W` are the pairs `(s, t) ∈ M(U ∩ W) × M(V ∩ W)` with
`s = τ t` on `U ∩ V ∩ W`. -/
noncomputable def twist : X.Modules where
  val := twistPresheaf M U V τ
  isSheaf := twistPresheaf_isSheaf M U V τ

variable {M U V τ}

section Sections

variable {W : X.Opens}

/-- The first component `s ∈ M(U ∩ W)` of a section `(s, t)` of the twist. -/
def twistFst (p : Γ(twist M U V τ, W)) : Γ(M, U ⊓ W) := p.1.1

/-- The second component `t ∈ M(V ∩ W)` of a section `(s, t)` of the twist. -/
def twistSnd (p : Γ(twist M U V τ, W)) : Γ(M, V ⊓ W) := p.1.2

lemma twist_cond (p : Γ(twist M U V τ, W)) :
    M.presheaf.map (homOfLE (inf_le_inf_right W inf_le_left) : (U ⊓ V) ⊓ W ⟶ U ⊓ W).op
      (twistFst p) =
    X.presheaf.map (homOfLE inf_le_left : (U ⊓ V) ⊓ W ⟶ U ⊓ V).op τ •
      M.presheaf.map (homOfLE (inf_le_inf_right W inf_le_right) : (U ⊓ V) ⊓ W ⟶ V ⊓ W).op
        (twistSnd p) := p.2

lemma twist_ext {p q : Γ(twist M U V τ, W)} (h₁ : twistFst p = twistFst q)
    (h₂ : twistSnd p = twistSnd q) : p = q :=
  Subtype.ext (Prod.ext h₁ h₂)

variable (τ) in
/-- The section `(s, t)` of the twist, for `s = τ t` on `U ∩ V ∩ W`. -/
def twistMk (a : Γ(M, U ⊓ W)) (b : Γ(M, V ⊓ W))
    (h : M.presheaf.map (homOfLE (inf_le_inf_right W inf_le_left) : (U ⊓ V) ⊓ W ⟶ U ⊓ W).op a =
      X.presheaf.map (homOfLE inf_le_left : (U ⊓ V) ⊓ W ⟶ U ⊓ V).op τ •
        M.presheaf.map (homOfLE (inf_le_inf_right W inf_le_right) :
          (U ⊓ V) ⊓ W ⟶ V ⊓ W).op b) : Γ(twist M U V τ, W) := ⟨(a, b), h⟩

@[simp] lemma twistFst_mk (a b h) : twistFst (twistMk (W := W) (M := M) τ a b h) = a := rfl
@[simp] lemma twistSnd_mk (a b h) : twistSnd (twistMk (W := W) (M := M) τ a b h) = b := rfl

@[simp] lemma twistFst_add (p q : Γ(twist M U V τ, W)) :
    twistFst (p + q) = twistFst p + twistFst q := rfl
@[simp] lemma twistSnd_add (p q : Γ(twist M U V τ, W)) :
    twistSnd (p + q) = twistSnd p + twistSnd q := rfl

@[simp] lemma twistFst_map {W' : X.Opens} (f : W' ⟶ W) (p : Γ(twist M U V τ, W)) :
    twistFst ((twist M U V τ).presheaf.map f.op p) =
      M.presheaf.map (homOfLE (inf_le_inf_left U (leOfHom f))).op (twistFst p) := rfl

@[simp] lemma twistSnd_map {W' : X.Opens} (f : W' ⟶ W) (p : Γ(twist M U V τ, W)) :
    twistSnd ((twist M U V τ).presheaf.map f.op p) =
      M.presheaf.map (homOfLE (inf_le_inf_left V (leOfHom f))).op (twistSnd p) := rfl

end Sections

/-- Over an open `W ⊆ V`, a section `(s, t)` of the twist is determined by `t`: the sections of
`M(τ)` over `W` are those of `M`. -/
noncomputable def twistAppEquivRight {W : X.Opens} (hW : W ≤ V) :
    Γ(twist M U V τ, W) ≃+ Γ(M, W) where
  toFun p := M.presheaf.map (homOfLE (le_inf hW le_rfl) : W ⟶ V ⊓ W).op (twistSnd p)
  invFun t := twistMk τ (X.presheaf.map (homOfLE (inf_le_inf_left U hW) :
      U ⊓ W ⟶ U ⊓ V).op τ •
      M.presheaf.map (homOfLE inf_le_right : U ⊓ W ⟶ W).op t)
      (M.presheaf.map (homOfLE inf_le_right : V ⊓ W ⟶ W).op t) (by
    rw [map_smul]
    simp only [presheaf_map_map_comp, scheme_presheaf_map_map_comp]
    rfl)
  left_inv p := by
    have hp := twist_cond p
    have hUW : U ⊓ W ≤ (U ⊓ V) ⊓ W := le_inf (le_inf inf_le_left
      ((inf_le_right : U ⊓ W ≤ W).trans hW)) inf_le_right
    apply twist_ext
    · have := congr(M.presheaf.map (homOfLE hUW).op $hp)
      rw [map_smul] at this
      simp only [presheaf_map_map_comp, scheme_presheaf_map_map_comp, twistFst_mk] at this ⊢
      rw [presheaf_map_congr M _ (𝟙 _)] at this
      simp only [op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] at this
      rw [this]
      congr 1
    · simp only [twistSnd_mk, presheaf_map_map_comp]
      rw [presheaf_map_congr M _ (𝟙 _)]
      simp
  right_inv t := by
    change M.presheaf.map _ (M.presheaf.map _ t) = t
    simp only [presheaf_map_map_comp]
    rw [presheaf_map_congr M _ (𝟙 _)]
    simp
  map_add' p q := by
    simp only [twistSnd_add, map_add]

lemma scheme_presheaf_map_mul_inv {T : X.Opens} (hτ : IsUnit τ) (k : T ⟶ U ⊓ V) :
    X.presheaf.map k.op τ * X.presheaf.map k.op (↑hτ.unit⁻¹ : Γ(X, U ⊓ V)) = 1 := by
  rw [← map_mul, IsUnit.mul_val_inv, map_one]

/-- Over an open `W ⊆ U`, if `τ` is a unit, a section `(s, t)` of the twist is determined by `s`:
the sections of `M(τ)` over `W` are those of `M`. -/
noncomputable def twistAppEquivLeft (hτ : IsUnit τ) {W : X.Opens} (hW : W ≤ U) :
    Γ(twist M U V τ, W) ≃+ Γ(M, W) where
  toFun p := M.presheaf.map (homOfLE (le_inf hW le_rfl) : W ⟶ U ⊓ W).op (twistFst p)
  invFun t := twistMk τ (M.presheaf.map (homOfLE inf_le_right : U ⊓ W ⟶ W).op t)
      (X.presheaf.map (homOfLE (le_inf ((inf_le_right : V ⊓ W ≤ W).trans hW) inf_le_left) :
        V ⊓ W ⟶ U ⊓ V).op (↑hτ.unit⁻¹ : Γ(X, U ⊓ V)) •
        M.presheaf.map (homOfLE inf_le_right : V ⊓ W ⟶ W).op t) (by
    rw [map_smul, smul_smul]
    simp only [presheaf_map_map_comp, scheme_presheaf_map_map_comp]
    rw [scheme_presheaf_map_congr (_ ≫ _) (homOfLE inf_le_left), scheme_presheaf_map_mul_inv,
      one_smul]
    rfl)
  left_inv p := by
    have hp := twist_cond p
    have hVW : V ⊓ W ≤ (U ⊓ V) ⊓ W := le_inf (le_inf ((inf_le_right : V ⊓ W ≤ W).trans hW)
      inf_le_left) inf_le_right
    apply twist_ext
    · simp only [twistFst_mk, presheaf_map_map_comp]
      rw [presheaf_map_congr M _ (𝟙 _)]
      simp
    · have := congr(M.presheaf.map (homOfLE hVW).op $hp)
      rw [map_smul] at this
      simp only [presheaf_map_map_comp, scheme_presheaf_map_map_comp, twistSnd_mk] at this ⊢
      rw [presheaf_map_congr M _ (homOfLE hVW ≫ homOfLE (inf_le_inf_right W inf_le_left)), this,
        smul_smul, presheaf_map_congr M _ (𝟙 _),
        scheme_presheaf_map_congr (homOfLE hVW ≫ homOfLE inf_le_left)
          (homOfLE (le_inf ((inf_le_right : V ⊓ W ≤ W).trans hW) inf_le_left)), mul_comm,
        scheme_presheaf_map_mul_inv]
      simp
  right_inv t := by
    change M.presheaf.map _ (M.presheaf.map _ t) = t
    simp only [presheaf_map_map_comp]
    rw [presheaf_map_congr M _ (𝟙 _)]
    simp
  map_add' p q := by
    simp only [twistFst_add, map_add]

/-! ### The Čech complex of the twist -/

variable (M) in
/-- Multiplication by `τ ∈ Γ(X, W)` on `Γ(M, W)`, as a `ℤ`-linear map. -/
noncomputable def smulℤ {W : X.Opens} (r : Γ(X, W)) : Γ(M, W) →ₗ[ℤ] Γ(M, W) :=
  (M.smul r).hom.toIntLinearMap

@[simp] lemma smulℤ_apply {W : X.Opens} (r : Γ(X, W)) (s : Γ(M, W)) : smulℤ M r s = r • s := rfl

/-- The twisted Čech differential: for the covering `(U, V)`, the Čech complex of `M(τ)` is
`Γ(M, U) × Γ(M, V) → Γ(M, U ∩ V)`, `(s, t) ↦ s| - τ t|`. -/
lemma twist_cech_square_left (hτ : IsUnit τ) :
    resℤ M (inf_le_left : U ⊓ V ≤ U) ∘ₗ
      ((twistAppEquivLeft (M := M) (V := V) hτ (le_refl U)).toIntLinearEquiv.toLinearMap) =
    ((twistAppEquivLeft (M := M) hτ (inf_le_left : U ⊓ V ≤ U)).toIntLinearEquiv.toLinearMap) ∘ₗ
      resℤ (twist M U V τ) inf_le_left := by
  refine LinearMap.ext fun p ↦ ?_
  change M.presheaf.map _ (M.presheaf.map _ (twistFst p)) =
    M.presheaf.map _ (twistFst ((twist M U V τ).presheaf.map _ p))
  rw [twistFst_map]
  simp only [presheaf_map_map_comp]
  exact presheaf_map_congr M _ _ _

lemma twist_cech_square_right (hτ : IsUnit τ) :
    (smulℤ M τ ∘ₗ resℤ M (inf_le_right : U ⊓ V ≤ V)) ∘ₗ
      ((twistAppEquivRight (M := M) (U := U) (τ := τ) (le_refl V)).toIntLinearEquiv.toLinearMap) =
    ((twistAppEquivLeft (M := M) hτ (inf_le_left : U ⊓ V ≤ U)).toIntLinearEquiv.toLinearMap) ∘ₗ
      resℤ (twist M U V τ) inf_le_right := by
  refine LinearMap.ext fun p ↦ ?_
  change τ • M.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op
      (M.presheaf.map (homOfLE (le_inf le_rfl le_rfl) : V ⟶ V ⊓ V).op (twistSnd p)) =
    M.presheaf.map (homOfLE (le_inf inf_le_left le_rfl) : U ⊓ V ⟶ U ⊓ (U ⊓ V)).op
      (twistFst ((twist M U V τ).presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op p))
  rw [twistFst_map]
  have hp := congr(M.presheaf.map (homOfLE (le_inf le_rfl inf_le_right) :
    U ⊓ V ⟶ (U ⊓ V) ⊓ V).op $(twist_cond p))
  rw [map_smul] at hp
  simp only [presheaf_map_map_comp, scheme_presheaf_map_map_comp] at hp ⊢
  rw [presheaf_map_congr M _ (homOfLE (le_inf le_rfl inf_le_right) ≫
    homOfLE (inf_le_inf_right V inf_le_left)), hp]
  congr 1
  rw [scheme_presheaf_map_congr _ (𝟙 _)]
  simp

/-- **Čech `H⁰` of a twist.** For a unit `τ`, the Čech `H⁰` of `M(τ)` for the covering `(U, V)` is
the kernel of `(s, t) ↦ s| - τ t|` on `Γ(M, U) × Γ(M, V)`. -/
noncomputable def twistCechH0Equiv (hτ : IsUnit τ) :
    cechH0 (twist M U V τ) U V ≃ₗ[ℤ]
      TwoCech.H0 (resℤ M (inf_le_left : U ⊓ V ≤ U))
        (smulℤ M τ ∘ₗ resℤ M (inf_le_right : U ⊓ V ≤ V)) :=
  TwoCech.equivH0 (twistAppEquivLeft (M := M) (V := V) hτ (le_refl U)).toIntLinearEquiv
    (twistAppEquivRight (M := M) (U := U) (τ := τ) (le_refl V)).toIntLinearEquiv
    (twistAppEquivLeft (M := M) hτ (inf_le_left : U ⊓ V ≤ U)).toIntLinearEquiv
    (twist_cech_square_left hτ) (twist_cech_square_right hτ)

/-- **Čech `H¹` of a twist.** For a unit `τ`, the Čech `H¹` of `M(τ)` for the covering `(U, V)` is
the cokernel of `(s, t) ↦ s| - τ t|`. -/
noncomputable def twistCechH1Equiv (hτ : IsUnit τ) :
    cechH1 (twist M U V τ) U V ≃ₗ[ℤ]
      TwoCech.H1 (resℤ M (inf_le_left : U ⊓ V ≤ U))
        (smulℤ M τ ∘ₗ resℤ M (inf_le_right : U ⊓ V ≤ V)) :=
  TwoCech.equivH1 (twistAppEquivLeft (M := M) (V := V) hτ (le_refl U)).toIntLinearEquiv
    (twistAppEquivRight (M := M) (U := U) (τ := τ) (le_refl V)).toIntLinearEquiv
    (twistAppEquivLeft (M := M) hτ (inf_le_left : U ⊓ V ≤ U)).toIntLinearEquiv
    (twist_cech_square_left hτ) (twist_cech_square_right hτ)

end AlgebraicGeometry.Scheme.Modules
