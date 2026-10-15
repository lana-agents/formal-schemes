/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.AdicSystem
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.Order.Category.Preord
import Mathlib.RingTheory.Artinian.Module

/-!
# Inverse limits of towers of modules and the Mittag-Leffler condition

A tower of `A`-modules is a functor `ℕᵒᵖ ⥤ ModuleCat A`. Its limit `ModuleTower.limit F` is the
submodule of compatible families of `∀ n, F(n)`. This file proves the exactness properties of
`lim` needed to pass cohomology to the limit along the thickenings `X_n` of a formal scheme
(Stacks, Section 10.86, Tag 0594, "Mittag-Leffler systems"; Stacks, Lemma 10.86.4, Tag 0598):

* `ModuleTower.limMap_injective`, `ModuleTower.exact_limMap`: `lim` is left exact;
* `ModuleTower.limMap_surjective`: for a levelwise short exact sequence `0 → K → M → N → 0` of
  towers in which `K` is Mittag-Leffler (`CategoryTheory.Functor.IsMittagLeffler` of the
  underlying system of sets), `lim M → lim N` is surjective;
* `ModuleTower.isMittagLeffler_of_isArtinian`: a tower of Artinian modules is Mittag-Leffler —
  e.g. finite modules over `A ⧸ I^(n+1)` with `A ⧸ I` Artinian, the case of a complete local
  Noetherian base and its maximal ideal.

The proof of `limMap_surjective` follows Stacks 0598: the set of lifts of a compatible family that
remain liftable to every higher level is nonempty at every level and maps onto the previous one.
-/

universe u v

open CategoryTheory Opposite

namespace ModuleTower

variable {A : Type u} [CommRing A]

/-- The transition map `F(m) → F(n)` of a tower for `n ≤ m`. -/
abbrev tr (F : ℕᵒᵖ ⥤ ModuleCat.{v} A) {n m : ℕ} (h : n ≤ m) : F.obj (op m) →ₗ[A] F.obj (op n) :=
  (F.map (homOfLE h).op).hom

lemma tr_tr (F : ℕᵒᵖ ⥤ ModuleCat.{v} A) {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k)
    (x : F.obj (op k)) : tr F h (tr F h' x) = tr F (h.trans h') x := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← F.map_comp]
  rfl

lemma tr_self (F : ℕᵒᵖ ⥤ ModuleCat.{v} A) {n : ℕ} (x : F.obj (op n)) :
    tr F (le_refl n) x = x := by
  change (F.map (𝟙 _)).hom x = x
  rw [F.map_id]
  rfl

/-- The inverse limit of a tower of modules, as a submodule of the product. -/
def limit (F : ℕᵒᵖ ⥤ ModuleCat.{v} A) : Submodule A (∀ n, F.obj (op n)) where
  carrier := {x | ∀ n, tr F n.le_succ (x (n + 1)) = x n}
  add_mem' {x y} hx hy n := by simp [hx n, hy n]
  zero_mem' n := by simp
  smul_mem' c x hx n := by simp [hx n]

lemma tr_limit (F : ℕᵒᵖ ⥤ ModuleCat.{v} A) (x : limit F) {n m : ℕ} (h : n ≤ m) :
    tr F h (x.1 m) = x.1 n := by
  induction m, h using Nat.le_induction with
  | base => exact tr_self F _
  | succ m hm ih => rw [← tr_tr F hm m.le_succ, x.2 m, ih]

lemma app_tr {F G : ℕᵒᵖ ⥤ ModuleCat.{v} A} (α : F ⟶ G) {n m : ℕ} (h : n ≤ m)
    (x : F.obj (op m)) : (α.app (op n)).hom (tr F h x) = tr G h ((α.app (op m)).hom x) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, α.naturality]
  rfl

/-- The map of limits induced by a morphism of towers. -/
def limMap {F G : ℕᵒᵖ ⥤ ModuleCat.{v} A} (α : F ⟶ G) : limit F →ₗ[A] limit G where
  toFun x := ⟨fun n ↦ (α.app (op n)).hom (x.1 n), fun n ↦ by
    rw [← app_tr, x.2 n]⟩
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

@[simp]
lemma limMap_apply {F G : ℕᵒᵖ ⥤ ModuleCat.{v} A} (α : F ⟶ G) (x : limit F) (n : ℕ) :
    (limMap α x).1 n = (α.app (op n)).hom (x.1 n) := rfl

/-- `lim` preserves injectivity. -/
lemma limMap_injective {F G : ℕᵒᵖ ⥤ ModuleCat.{v} A} (α : F ⟶ G)
    (hα : ∀ n, Function.Injective (α.app (op n)).hom) : Function.Injective (limMap α) := by
  intro x y h
  ext n
  exact hα n (congrArg (fun z : limit G ↦ z.1 n) h)

/-- `lim` is left exact: a levelwise exact sequence `K → M → N` with `K → M` injective gives an
exact sequence of limits. -/
lemma exact_limMap {K M N : ℕᵒᵖ ⥤ ModuleCat.{v} A} (ι : K ⟶ M) (π : M ⟶ N)
    (hι : ∀ n, Function.Injective (ι.app (op n)).hom)
    (hex : ∀ n, Function.Exact (ι.app (op n)).hom (π.app (op n)).hom) :
    Function.Exact (limMap ι) (limMap π) := by
  intro x
  constructor
  · intro hx
    have h n : ∃ k, (ι.app (op n)).hom k = x.1 n :=
      (hex n (x.1 n)).mp (congrArg (fun z : limit N ↦ z.1 n) hx)
    choose k hk using h
    refine ⟨⟨k, fun n ↦ hι n ?_⟩, ?_⟩
    · rw [app_tr, hk, hk]
      exact x.2 n
    · ext n
      exact hk n
  · rintro ⟨k, rfl⟩
    ext n
    exact (hex n _).mpr ⟨k.1 n, rfl⟩

section MittagLeffler

/-- The tower of underlying sets satisfies the Mittag-Leffler condition. -/
abbrev IsMittagLeffler (F : ℕᵒᵖ ⥤ ModuleCat.{v} A) : Prop :=
  (F ⋙ forget (ModuleCat.{v} A)).IsMittagLeffler

/-- The Mittag-Leffler condition, unfolded: for each `n` there is `N ≥ n` such that the image of
`F(N)` in `F(n)` lies in the image of every `F(m)`, `m ≥ n`. -/
lemma IsMittagLeffler.exists {F : ℕᵒᵖ ⥤ ModuleCat.{v} A} (hF : IsMittagLeffler F) (n : ℕ) :
    ∃ N, ∃ hN : n ≤ N, ∀ m (hm : n ≤ m), ∀ z : F.obj (op N),
      ∃ w : F.obj (op m), tr F hm w = tr F hN z := by
  obtain ⟨⟨N⟩, f, hf⟩ := hF (op n)
  have hN : n ≤ N := leOfHom f.unop
  refine ⟨N, hN, fun m hm z ↦ ?_⟩
  obtain ⟨w, hw⟩ := hf (homOfLE hm).op ⟨z, rfl⟩
  exact ⟨w, hw.trans (by rfl)⟩

/-- A tower with surjective transition maps is Mittag-Leffler. -/
lemma isMittagLeffler_of_surjective {F : ℕᵒᵖ ⥤ ModuleCat.{v} A}
    (hF : ∀ n : ℕ, Function.Surjective (tr F n.le_succ)) : IsMittagLeffler F := by
  apply Functor.isMittagLeffler_of_surjective
  rintro ⟨m⟩ ⟨n⟩ f
  have h : n ≤ m := leOfHom f.unop
  change Function.Surjective (tr F h)
  induction m, h using Nat.le_induction with
  | base => intro x; exact ⟨x, tr_self F x⟩
  | succ m hm ih =>
    intro x
    obtain ⟨y, rfl⟩ := ih (homOfLE hm).op x
    obtain ⟨z, rfl⟩ := hF m y
    exact ⟨z, (tr_tr F hm m.le_succ z).symm⟩

/-- A tower of Artinian modules is Mittag-Leffler: the images of `F(m)` in `F(n)` form a
decreasing chain of submodules. -/
lemma isMittagLeffler_of_isArtinian {F : ℕᵒᵖ ⥤ ModuleCat.{v} A}
    [∀ n, IsArtinian A (F.obj (op n))] : IsMittagLeffler F := by
  rintro ⟨n⟩
  let r : ℕ →o (Submodule A (F.obj (op n)))ᵒᵈ :=
    ⟨fun m ↦ OrderDual.toDual (LinearMap.range (tr F (le_max_left n m))), fun a b hab ↦ by
      change LinearMap.range _ ≤ LinearMap.range _
      rintro _ ⟨z, rfl⟩
      exact ⟨tr F (max_le_max le_rfl hab) z, tr_tr F _ _ z⟩⟩
  obtain ⟨k, hk⟩ := IsArtinian.monotone_stabilizes r
  refine ⟨op (max n k), (homOfLE (le_max_left n k)).op, ?_⟩
  rintro ⟨m⟩ g _ ⟨z, rfl⟩
  have hm : n ≤ m := leOfHom g.unop
  by_cases hkm : max n k ≤ m
  · have hz : tr F (le_max_left n k) z ∈ LinearMap.range (tr F (le_max_left n m)) := by
      change _ ∈ OrderDual.ofDual (r m)
      rw [← hk m ((le_max_right n k).trans hkm)]
      exact ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := hz
    refine ⟨tr F (le_max_right n m) w, ?_⟩
    change tr F hm (tr F _ w) = tr F _ z
    rw [tr_tr]
    exact hw
  · refine ⟨tr F (by omega : m ≤ max n k) z, ?_⟩
    change tr F hm (tr F _ z) = tr F _ z
    exact tr_tr F _ _ z

/-- **Mittag-Leffler**: for a levelwise short exact sequence `0 → K → M → N → 0` of towers with `K`
Mittag-Leffler, `lim M → lim N` is surjective (Stacks, Lemma 10.86.4, Tag 0598). -/
theorem limMap_surjective {K M N : ℕᵒᵖ ⥤ ModuleCat.{v} A} (ι : K ⟶ M) (π : M ⟶ N)
    (hex : ∀ n, Function.Exact (ι.app (op n)).hom (π.app (op n)).hom)
    (hπ : ∀ n, Function.Surjective (π.app (op n)).hom) (hK : IsMittagLeffler K) :
    Function.Surjective (limMap π) := by
  intro y
  -- `L n` : lifts of `y n`
  let L : ∀ n, Set (M.obj (op n)) := fun n ↦ {x | (π.app (op n)).hom x = y.1 n}
  have hL {n m} (h : n ≤ m) {z} (hz : z ∈ L m) : tr M h z ∈ L n := by
    change (π.app (op n)).hom _ = _
    rw [app_tr, hz, tr_limit]
  -- the key lemma: images of lifts from a Mittag-Leffler level lie in all images of lifts
  have key (n : ℕ) : ∃ N, ∃ hN : n ≤ N, ∀ k (hk : N ≤ k), ∀ m (hm : n ≤ m), ∀ z ∈ L k,
      ∃ w ∈ L m, tr M hm w = tr M (hN.trans hk) z := by
    obtain ⟨N, hN, hML⟩ := hK.exists n
    refine ⟨N, hN, fun k hk m hm z hz ↦ ?_⟩
    obtain ⟨z', hz'⟩ := hπ (max m k) (y.1 (max m k))
    have hdiff : tr M (le_max_right m k) z' - z ∈ Set.range (ι.app (op k)).hom := by
      refine (hex k _).mp ?_
      rw [map_sub, sub_eq_zero]
      exact (hL (le_max_right m k) hz').trans hz.symm
    obtain ⟨κ, hκ⟩ := hdiff
    obtain ⟨κ', hκ'⟩ := hML (max m k) (hm.trans (le_max_left m k)) (tr K hk κ)
    refine ⟨tr M (le_max_left m k) (z' - (ι.app (op (max m k))).hom κ'), hL _ ?_, ?_⟩
    · change (π.app _).hom _ = _
      rw [map_sub, hz', (hex _ _).mpr ⟨κ', rfl⟩, sub_zero]
    · have e1 : (ι.app (op n)).hom (tr K (hm.trans (le_max_left m k)) κ') =
          tr M (hN.trans hk) ((ι.app (op k)).hom κ) := by
        rw [hκ', tr_tr, app_tr]
      rw [tr_tr, map_sub, ← app_tr, e1, hκ, map_sub, tr_tr]
      exact sub_sub_cancel _ _
  -- `D n` : lifts liftable to every higher level
  let D : ∀ n, Set (M.obj (op n)) := fun n ↦
    {x | x ∈ L n ∧ ∀ m (hm : n ≤ m), ∃ w ∈ L m, tr M hm w = x}
  have hD_of {n} (N : ℕ) (hN : n ≤ N)
      (hkey : ∀ k (hk : N ≤ k), ∀ m (hm : n ≤ m), ∀ z ∈ L k,
        ∃ w ∈ L m, tr M hm w = tr M (hN.trans hk) z)
      {k} (hk : N ≤ k) {z} (hz : z ∈ L k) : tr M (hN.trans hk) z ∈ D n :=
    ⟨hL _ hz, fun m hm ↦ hkey k hk m hm z hz⟩
  have hD_ne (n : ℕ) : (D n).Nonempty := by
    obtain ⟨N, hN, hkey⟩ := key n
    obtain ⟨z, hz⟩ := hπ N (y.1 N)
    exact ⟨_, hD_of N hN hkey le_rfl hz⟩
  have hD_surj (n : ℕ) (a : D n) : ∃ b : D (n + 1), tr M n.le_succ b.1 = a.1 := by
    obtain ⟨N, hN, hkey⟩ := key (n + 1)
    obtain ⟨z, hz, hza⟩ := a.2.2 N (n.le_succ.trans hN)
    refine ⟨⟨_, hD_of N hN hkey le_rfl hz⟩, ?_⟩
    rw [tr_tr]
    exact hza
  let f : ∀ k, D (k + 1) → D k := fun k b ↦ ⟨tr M k.le_succ b.1, by
    refine ⟨hL _ b.2.1, fun m hm ↦ ?_⟩
    obtain ⟨w, hw, hwb⟩ := b.2.2 (max m (k + 1)) (le_max_right _ _)
    refine ⟨tr M (le_max_left m (k + 1)) w, hL _ hw, ?_⟩
    rw [tr_tr, ← hwb, tr_tr]⟩
  have hf : ∀ k, Function.Surjective (f k) := fun k a ↦ by
    obtain ⟨b, hb⟩ := hD_surj k a
    exact ⟨b, Subtype.ext hb⟩
  obtain ⟨s, hs, -⟩ :=
    AdicSystem.exists_section_of_surjective 0 (X := fun k ↦ ↥(D k)) f hf
      ⟨(hD_ne 0).some, (hD_ne 0).some_mem⟩
  refine ⟨⟨fun n ↦ (s n).1, fun n ↦ congrArg Subtype.val (hs n)⟩, ?_⟩
  ext n
  exact (s n).2.1

end MittagLeffler

end ModuleTower
