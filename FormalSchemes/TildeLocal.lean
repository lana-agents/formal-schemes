/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.QcohSpecSections

/-!
# `M ↦ M^~` turns localisations into isomorphisms over basic opens

If `g : M → M'` is a localisation at `c ∈ R`, then `g^~ : M^~ → M'^~` is an isomorphism over
every open of `Spec R` contained in `D(c)` (`AlgebraicGeometry.tilde_map_app_bijective`).
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

section

variable {R : Type*} [CommRing R] {M M' M'' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']

/-- A localisation at `c` followed by a localisation at `c'`, with `c' ^ n ∈ (c)`, is a
localisation at `c'`. -/
lemma isLocalizedModule_comp_powers (c c' : R) (hc : c' ∈ (Ideal.span {c}).radical)
    (g : M →ₗ[R] M') (h : M' →ₗ[R] M'') [IsLocalizedModule (.powers c) g]
    [IsLocalizedModule (.powers c') h] : IsLocalizedModule (.powers c') (h ∘ₗ g) := by
  obtain ⟨n, hn⟩ := hc
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hn
  refine ⟨IsLocalizedModule.map_units h, fun y ↦ ?_, fun {x y} hxy ↦ ?_⟩
  · obtain ⟨⟨m', ⟨_, k, rfl⟩⟩, hk⟩ := IsLocalizedModule.surj (.powers c') h y
    obtain ⟨⟨m, ⟨_, j, rfl⟩⟩, hj⟩ := IsLocalizedModule.surj (.powers c) g m'
    refine ⟨⟨a ^ j • m, ⟨c' ^ (n * j + k), n * j + k, rfl⟩⟩, ?_⟩
    simp only [Submonoid.smul_def] at hk hj ⊢
    rw [LinearMap.comp_apply, map_smul, map_smul, ← hj, map_smul, ← hk, smul_smul, smul_smul,
      ← mul_pow, ha, pow_add, pow_mul, mul_smul]
  · obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalizedModule.exists_of_eq (S := .powers c') (f := h) hxy
    simp only [Submonoid.smul_def] at hk
    rw [← map_smul, ← map_smul] at hk
    obtain ⟨⟨_, j, rfl⟩, hj⟩ := IsLocalizedModule.exists_of_eq (S := .powers c) (f := g) hk
    simp only [Submonoid.smul_def] at hj
    refine ⟨⟨c' ^ (n * j + k), n * j + k, rfl⟩, ?_⟩
    simp only [Submonoid.smul_def]
    rw [pow_add, pow_mul, ← ha, mul_pow, mul_smul, mul_smul, mul_smul, mul_smul, hj]

end

variable {R : CommRingCat.{u}}

/-- Over a basic open `D(c') ⊆ D(c)`, `g^~` is bijective for a localisation `g` at `c`. -/
lemma tilde_map_app_basicOpen_bijective {M M' : ModuleCat.{u} R} (g : M ⟶ M') (c : R)
    [IsLocalizedModule (.powers c) g.hom] (c' : R)
    (hc : PrimeSpectrum.basicOpen c' ≤ PrimeSpectrum.basicOpen c) :
    Function.Bijective ((modulesSpecToSheaf.map (tilde.map g)).1.app
      (op (PrimeSpectrum.basicOpen c'))) := by
  have h2 : IsLocalizedModule (.powers c') (tilde.toOpen M (PrimeSpectrum.basicOpen c') ≫
      (modulesSpecToSheaf.map (tilde.map g)).1.app (op (PrimeSpectrum.basicOpen c'))).hom := by
    rw [tilde.toOpen_map_app, ModuleCat.hom_comp]
    exact isLocalizedModule_comp_powers c c' ((PrimeSpectrum.basicOpen_le_basicOpen_iff _ _).1 hc)
      g.hom _
  have := ModuleCat.isIso_of_isLocalizedModule_comp (inferInstance : IsLocalizedModule (.powers c')
    (tilde.toOpen M (PrimeSpectrum.basicOpen c')).hom) h2
  exact ConcreteCategory.bijective_of_isIso _

/-- **`g^~` is an isomorphism over `D(c)`**: for a localisation `g` at `c`, `g^~` is bijective on
the sections over every open contained in `D(c)`. -/
lemma tilde_map_app_bijective {M M' : ModuleCat.{u} R} (g : M ⟶ M') (c : R)
    [IsLocalizedModule (.powers c) g.hom] (V : (Spec R).Opens)
    (hV : V ≤ PrimeSpectrum.basicOpen c) : Function.Bijective ((tilde.map g).app V) := by
  let PF : TopCat.Presheaf Ab (Spec R) := (tilde M).presheaf
  let PG : TopCat.Presheaf Ab (Spec R) := (tilde M').presheaf
  let β : PF ⟶ PG := (tilde.map g).mapPresheaf
  let F : TopCat.Sheaf Ab (Spec R) := ⟨PF, (tilde M).isSheaf⟩
  let G : TopCat.Sheaf Ab (Spec R) := ⟨PG, (tilde M').isSheaf⟩
  let α : F ⟶ G := ObjectProperty.homMk β
  have nat : ∀ {W W' : Opens (Spec R)} (i : W' ⟶ W) (s : ToType (PF.obj (op W))),
      β.app (op W') (PF.map i.op s) = PG.map i.op (β.app (op W) s) := fun i s ↦ by
    rw [← ConcreteCategory.comp_apply, β.naturality, ConcreteCategory.comp_apply]
  have hbas : ∀ (x : Spec R) (W : (Spec R).Opens), x ∈ W → x ∈ V → ∃ c' : R,
      x ∈ PrimeSpectrum.basicOpen c' ∧ PrimeSpectrum.basicOpen c' ≤ W ⊓ PrimeSpectrum.basicOpen c
      := by
    intro x W hxW hxV
    obtain ⟨_, ⟨c', rfl⟩, hx, hle⟩ := (Opens.isBasis_iff_nbhd.1 PrimeSpectrum.isBasis_basic_opens)
      (show x ∈ W ⊓ PrimeSpectrum.basicOpen c from ⟨hxW, hV hxV⟩)
    exact ⟨c', hx, hle⟩
  have hD : ∀ c' : R, PrimeSpectrum.basicOpen c' ≤ PrimeSpectrum.basicOpen c →
      Function.Bijective (β.app (op (PrimeSpectrum.basicOpen c'))) :=
    fun c' hc' ↦ tilde_map_app_basicOpen_bijective g c c' hc'
  refine TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective α V fun x hx ↦ ⟨?_, ?_⟩
  · change Function.Injective ((TopCat.Presheaf.stalkFunctor Ab x).map β)
    refine (injective_iff_map_eq_zero _).2 fun y hy ↦ ?_
    obtain ⟨W, hxW, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq PF y
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hy
    obtain ⟨W', hxW', iU, iV, e⟩ := TopCat.Presheaf.germ_eq PG x hxW hxW _ 0
      (hy.trans (map_zero _).symm)
    obtain ⟨c', hx', hle⟩ := hbas x W' hxW' hx
    let i1 : PrimeSpectrum.basicOpen c' ⟶ W' := homOfLE (hle.trans inf_le_left)
    have hs : β.app (op (PrimeSpectrum.basicOpen c')) (PF.map i1.op (PF.map iU.op s)) =
        β.app (op (PrimeSpectrum.basicOpen c')) 0 :=
      (nat i1 _).trans ((congrArg (PG.map i1.op) ((nat iU s).trans e)).trans
        ((congrArg (PG.map i1.op) (map_zero (PG.map iV.op).hom)).trans
          ((map_zero (PG.map i1.op).hom).trans (map_zero (β.app _).hom).symm)))
    have h0 := (hD c' (hle.trans inf_le_right)).1 hs
    exact ((TopCat.Presheaf.germ_res_apply PF iU x hxW' s).symm.trans
      (TopCat.Presheaf.germ_res_apply PF i1 x hx' _).symm).trans
      ((congrArg (PF.germ _ x hx') h0).trans (map_zero _))
  · change Function.Surjective ((TopCat.Presheaf.stalkFunctor Ab x).map β)
    intro z
    obtain ⟨W, hxW, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq PG z
    obtain ⟨c', hx', hle⟩ := hbas x W hxW hx
    obtain ⟨s, hs⟩ := (hD c' (hle.trans inf_le_right)).2
      (PG.map (homOfLE (hle.trans inf_le_left)).op t)
    refine ⟨PF.germ _ x hx' s, ?_⟩
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply _ x hx' β s).trans
      ((congrArg (PG.germ _ x hx') hs).trans (TopCat.Presheaf.germ_res_apply PG _ x hx' t))

end AlgebraicGeometry
