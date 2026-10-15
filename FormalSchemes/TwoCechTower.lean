/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ModuleTower
import FormalSchemes.TwoCech

/-!
# Two-set Čech cohomology along a tower

Let `fₙ : Pₙ → Rₙ`, `gₙ : Qₙ → Rₙ` be compatible two-set Čech data along a tower, e.g. the
restriction maps of a quasi-coherent module `F` over two affines `U`, `V` and `U ∩ V` of the
thickenings `Xₙ` of a scheme over an adic ring. This file compares the Čech cohomology of the
limit with the limit of the Čech cohomology:

* `TwoCechTower.limH0Equiv`: `Ȟ⁰` commutes with `lim` (left exactness);
* `TwoCechTower.toLimH1_bijective`: if the transition maps of `Pₙ` and `Qₙ` are surjective and
  the tower `Ȟ⁰ₙ` is Mittag-Leffler, then `Ȟ¹` commutes with `lim` (Stacks, Lemma 10.86.4,
  Tag 0598, applied twice).

The surjectivity hypothesis holds for sections of the thickenings of a quasi-coherent module on
affines (`AlgebraicGeometry.surjective_app_of_isAffineOpen`), and the Mittag-Leffler hypothesis
holds when the `Ȟ⁰ₙ` are Artinian (`ModuleTower.isMittagLeffler_of_isArtinian`), e.g. finite
modules over `A ⧸ 𝔪^(n+1)` for a Noetherian local ring `(A, 𝔪)`. Together these are the
algebraic part of the theorem on formal functions in degrees `0` and `1` for a scheme covered by
two affines with affine intersection (Stacks, Lemma 30.20.6, Tag 087U).
-/

universe u v

open CategoryTheory Opposite

namespace ModuleTower

variable {A : Type u} [CommRing A]

/-! ### Subtowers, quotient towers and products -/

/-- A family of submodules `Sₙ ⊆ F(n)` stable under the transition maps is a tower. -/
@[simps]
def subTower (F : ℕᵒᵖ ⥤ ModuleCat.{v} A) (S : ∀ n, Submodule A (F.obj (op n)))
    (hS : ∀ {X Y : ℕᵒᵖ} (h : X ⟶ Y), ∀ x ∈ S X.unop, (F.map h).hom x ∈ S Y.unop) :
    ℕᵒᵖ ⥤ ModuleCat.{v} A where
  obj X := ModuleCat.of A (S X.unop)
  map h := ModuleCat.ofHom ((F.map h).hom.restrict fun x hx ↦ hS h x hx)
  map_id X := by ext x; exact congrArg (fun φ ↦ (ModuleCat.Hom.hom φ) x.1) (F.map_id X)
  map_comp f g := by ext x; exact congrArg (fun φ ↦ (ModuleCat.Hom.hom φ) x.1) (F.map_comp f g)

/-- The inclusion of a subtower. -/
@[simps]
def subTowerι (F : ℕᵒᵖ ⥤ ModuleCat.{v} A) (S : ∀ n, Submodule A (F.obj (op n)))
    (hS : ∀ {X Y : ℕᵒᵖ} (h : X ⟶ Y), ∀ x ∈ S X.unop, (F.map h).hom x ∈ S Y.unop) :
    subTower F S hS ⟶ F where
  app X := ModuleCat.ofHom (S X.unop).subtype

/-- The quotient of a tower by a family of submodules stable under the transition maps. -/
@[simps]
def quotTower (F : ℕᵒᵖ ⥤ ModuleCat.{v} A) (S : ∀ n, Submodule A (F.obj (op n)))
    (hS : ∀ {X Y : ℕᵒᵖ} (h : X ⟶ Y), ∀ x ∈ S X.unop, (F.map h).hom x ∈ S Y.unop) :
    ℕᵒᵖ ⥤ ModuleCat.{v} A where
  obj X := ModuleCat.of A (F.obj X ⧸ S X.unop)
  map h := ModuleCat.ofHom ((S _).mapQ (S _) (F.map h).hom fun x hx ↦ hS h x hx)
  map_id X := by
    ext x
    exact congrArg Submodule.Quotient.mk (congrArg (fun φ ↦ (ModuleCat.Hom.hom φ) x) (F.map_id X))
  map_comp f g := by
    ext x
    exact congrArg Submodule.Quotient.mk
      (congrArg (fun φ ↦ (ModuleCat.Hom.hom φ) x) (F.map_comp f g))

/-- The projection onto a quotient tower. -/
@[simps]
def quotTowerπ (F : ℕᵒᵖ ⥤ ModuleCat.{v} A) (S : ∀ n, Submodule A (F.obj (op n)))
    (hS : ∀ {X Y : ℕᵒᵖ} (h : X ⟶ Y), ∀ x ∈ S X.unop, (F.map h).hom x ∈ S Y.unop) :
    F ⟶ quotTower F S hS where
  app X := ModuleCat.ofHom (S X.unop).mkQ

lemma nat_apply {F G : ℕᵒᵖ ⥤ ModuleCat.{v} A} (α : F ⟶ G) {X Y : ℕᵒᵖ} (h : X ⟶ Y)
    (x : F.obj X) : (α.app Y).hom ((F.map h).hom x) = (G.map h).hom ((α.app X).hom x) :=
  congrArg (fun φ ↦ φ.hom x) (α.naturality h)

/-- The levelwise product of two towers. -/
@[simps]
def prodTower (P Q : ℕᵒᵖ ⥤ ModuleCat.{v} A) : ℕᵒᵖ ⥤ ModuleCat.{v} A where
  obj X := ModuleCat.of A (P.obj X × Q.obj X)
  map h := ModuleCat.ofHom ((P.map h).hom.prodMap (Q.map h).hom)
  map_id X := by ext x <;> simp
  map_comp f g := by ext x <;> simp

/-- The first projection of a product tower. -/
@[simps]
def fstTower (P Q : ℕᵒᵖ ⥤ ModuleCat.{v} A) : prodTower P Q ⟶ P where
  app X := ModuleCat.ofHom (LinearMap.fst A _ _)

/-- The second projection of a product tower. -/
@[simps]
def sndTower (P Q : ℕᵒᵖ ⥤ ModuleCat.{v} A) : prodTower P Q ⟶ Q where
  app X := ModuleCat.ofHom (LinearMap.snd A _ _)

end ModuleTower

namespace TwoCechTower

open ModuleTower

variable {A : Type u} [CommRing A] {P Q R : ℕᵒᵖ ⥤ ModuleCat.{v} A} (f : P ⟶ R) (g : Q ⟶ R)

/-- The levelwise Čech differential, as a morphism of towers. -/
@[simps]
def dTower : prodTower P Q ⟶ R where
  app X := ModuleCat.ofHom (TwoCech.d (f.app X).hom (g.app X).hom)
  naturality X Y h := ModuleCat.hom_ext (LinearMap.ext fun x ↦ by
    change TwoCech.d _ _ ((P.map h).hom x.1, (Q.map h).hom x.2) = (R.map h).hom (TwoCech.d _ _ x)
    rw [TwoCech.d_apply, TwoCech.d_apply, map_sub, nat_apply, nat_apply])

lemma dTower_mapsTo_ker {X Y : ℕᵒᵖ} (h : X ⟶ Y) :
    ∀ x ∈ LinearMap.ker ((dTower f g).app (op X.unop)).hom,
      ((prodTower P Q).map h).hom x ∈ LinearMap.ker ((dTower f g).app (op Y.unop)).hom := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  refine (nat_apply (dTower f g) h x).trans ?_
  rw [show ((dTower f g).app X).hom x = 0 from hx, map_zero]

lemma dTower_mapsTo_range {X Y : ℕᵒᵖ} (h : X ⟶ Y) :
    ∀ x ∈ LinearMap.range ((dTower f g).app (op X.unop)).hom,
      (R.map h).hom x ∈ LinearMap.range ((dTower f g).app (op Y.unop)).hom := by
  rintro _ ⟨y, rfl⟩
  refine ⟨((prodTower P Q).map h).hom y, ?_⟩
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, (dTower f g).naturality]
  rfl

/-- The tower of Čech `H⁰`s. -/
abbrev H0Tower : ℕᵒᵖ ⥤ ModuleCat.{v} A :=
  subTower (prodTower P Q) (fun n ↦ LinearMap.ker ((dTower f g).app (op n)).hom)
    (dTower_mapsTo_ker f g)

/-- The tower of images of the Čech differentials. -/
abbrev imTower : ℕᵒᵖ ⥤ ModuleCat.{v} A :=
  subTower R (fun n ↦ LinearMap.range ((dTower f g).app (op n)).hom) (dTower_mapsTo_range f g)

/-- The tower of Čech `H¹`s. -/
abbrev H1Tower : ℕᵒᵖ ⥤ ModuleCat.{v} A :=
  quotTower R (fun n ↦ LinearMap.range ((dTower f g).app (op n)).hom) (dTower_mapsTo_range f g)

/-- The corestriction of the differential to its image, as a morphism of towers. -/
@[simps]
def toImTower : prodTower P Q ⟶ imTower f g where
  app X := ModuleCat.ofHom (LinearMap.rangeRestrict ((dTower f g).app (op X.unop)).hom)
  naturality X Y h := by
    ext x
    exact Subtype.ext (nat_apply (dTower f g) h x)

/-! ### `Ȟ⁰` commutes with limits -/

/-- The map from the limit of the `Ȟ⁰`s to the `Ȟ⁰` of the limit. -/
def toH0Lim : limit (H0Tower f g) →ₗ[A] TwoCech.H0 (limMap f) (limMap g) :=
  LinearMap.codRestrict _
    ((limMap (subTowerι _ _ _ ≫ fstTower P Q)).prod (limMap (subTowerι _ _ _ ≫ sndTower P Q)))
    fun x ↦ by
      rw [TwoCech.mem_H0]
      ext n
      have h : TwoCech.d (f.app (op n)).hom (g.app (op n)).hom (x.1 n).1 = 0 := (x.1 n).2
      rw [TwoCech.d_apply, sub_eq_zero] at h
      exact h

lemma toH0Lim_bijective : Function.Bijective (toH0Lim f g) := by
  constructor
  · intro x y h
    ext n : 2
    have h1 := congrArg (fun z ↦ (z.1.1 : limit P).1 n) h
    have h2 := congrArg (fun z ↦ (z.1.2 : limit Q).1 n) h
    exact Subtype.ext (Prod.ext h1 h2)
  · rintro ⟨⟨p, q⟩, hpq⟩
    rw [TwoCech.mem_H0] at hpq
    refine ⟨⟨fun n ↦ ⟨(p.1 n, q.1 n), ?_⟩, fun n ↦ ?_⟩, rfl⟩
    · change TwoCech.d (f.app (op n)).hom (g.app (op n)).hom (p.1 n, q.1 n) = 0
      rw [TwoCech.d_apply, sub_eq_zero]
      exact congrArg (fun z : limit R ↦ z.1 n) hpq
    · exact Subtype.ext (Prod.ext (p.2 n) (q.2 n))

/-- **`Ȟ⁰` commutes with limits**: `lim Ȟ⁰(Pₙ, Qₙ; Rₙ) ≃ Ȟ⁰(lim P, lim Q; lim R)`. -/
noncomputable def limH0Equiv : limit (H0Tower f g) ≃ₗ[A] TwoCech.H0 (limMap f) (limMap g) :=
  LinearEquiv.ofBijective _ (toH0Lim_bijective f g)

/-! ### `Ȟ¹` commutes with limits under Mittag-Leffler hypotheses -/

/-- The map from the `Ȟ¹` of the limit to the limit of the `Ȟ¹`s. -/
def toLimH1 : TwoCech.H1 (limMap f) (limMap g) →ₗ[A] limit (H1Tower f g) :=
  (LinearMap.range (TwoCech.d (limMap f) (limMap g))).liftQ (limMap (quotTowerπ _ _ _)) <| by
    rintro _ ⟨⟨p, q⟩, rfl⟩
    rw [LinearMap.mem_ker]
    ext n
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨(p.1 n, q.1 n), rfl⟩

@[simp]
lemma toLimH1_mk (r : limit R) :
    toLimH1 f g (Submodule.Quotient.mk r) = limMap (quotTowerπ _ _ _) r := rfl

variable {f g}

/-- If the transition maps of `P` and `Q` are surjective, so are those of the images of the
differentials. -/
lemma imTower_tr_surjective (hP : ∀ n : ℕ, Function.Surjective (tr P n.le_succ))
    (hQ : ∀ n : ℕ, Function.Surjective (tr Q n.le_succ)) (n : ℕ) :
    Function.Surjective (tr (imTower f g) n.le_succ) := by
  rintro ⟨_, ⟨⟨p, q⟩, rfl⟩⟩
  obtain ⟨p', rfl⟩ := hP n p
  obtain ⟨q', rfl⟩ := hQ n q
  refine ⟨⟨_, ⟨(p', q'), rfl⟩⟩, Subtype.ext ?_⟩
  exact (nat_apply (dTower f g) (homOfLE n.le_succ).op (p', q')).symm

/-- **`Ȟ¹` commutes with limits**: if the transition maps of `P` and `Q` are surjective and the
tower of `Ȟ⁰`s is Mittag-Leffler, then `Ȟ¹(lim P, lim Q; lim R) → lim Ȟ¹(Pₙ, Qₙ; Rₙ)` is
bijective (Stacks, Lemma 10.86.4, Tag 0598). -/
theorem toLimH1_bijective (hP : ∀ n : ℕ, Function.Surjective (tr P n.le_succ))
    (hQ : ∀ n : ℕ, Function.Surjective (tr Q n.le_succ)) (hML : IsMittagLeffler (H0Tower f g)) :
    Function.Bijective (toLimH1 f g) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using Submodule.Quotient.induction_on with | H r => ?_
    rw [toLimH1_mk] at hx
    have hr n : r.1 n ∈ LinearMap.range ((dTower f g).app (op n)).hom :=
      (Submodule.Quotient.mk_eq_zero _).mp (congrArg (fun z : limit (H1Tower f g) ↦ z.1 n) hx)
    let r' : limit (imTower f g) := ⟨fun n ↦ ⟨r.1 n, hr n⟩, fun n ↦ Subtype.ext (r.2 n)⟩
    obtain ⟨z, hz⟩ := limMap_surjective (subTowerι _ _ _) (toImTower f g)
      (fun n x ↦ by
        change (LinearMap.rangeRestrict _ x = 0) ↔ _
        rw [← Subtype.coe_inj, LinearMap.codRestrict_apply, Submodule.coe_zero]
        exact ⟨fun h ↦ ⟨⟨x, h⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩)
      (fun n ↦ LinearMap.surjective_rangeRestrict _) hML r'
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨(limMap (fstTower P Q) z, limMap (sndTower P Q) z), ?_⟩
    ext n
    exact congrArg (fun w : limit (imTower f g) ↦ (w.1 n).1) hz
  · intro y
    obtain ⟨r, hr⟩ := limMap_surjective (subTowerι _ _ _) (quotTowerπ _ _ _)
      (fun n x ↦ by
        change (Submodule.mkQ _ x = 0) ↔ _
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact ⟨fun h ↦ ⟨⟨x, h⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩)
      (fun n ↦ Submodule.mkQ_surjective _)
      (isMittagLeffler_of_surjective (imTower_tr_surjective hP hQ)) y
    exact ⟨Submodule.Quotient.mk r, hr⟩

end TwoCechTower
