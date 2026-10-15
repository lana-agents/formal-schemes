/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Sections of quasi-coherent modules on an affine scheme

For a quasi-coherent `𝒪_{Spec R}`-module `M`, the restriction map `Γ(M, Spec R) → Γ(M, D(f))` is
a localization away from `f` (`AlgebraicGeometry.isLocalizedModule_res_basicOpen`): quasi-coherent
modules on `Spec R` are of the form `M^~` (Stacks, Lemma 26.7.4, Tag 01IA; Mathlib's
`Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent`), and `M^~(D(f)) = M_f` (Stacks,
Lemma 26.5.4 (4), Tag 01HV).

The main result is that the global sections functor on `Spec R` takes a locally surjective map of
quasi-coherent modules to a surjection
(`AlgebraicGeometry.surjective_specApp_top_of_isLocallySurjective`).
This is the degree-one part of the vanishing of higher cohomology of quasi-coherent sheaves on
affine schemes (Stacks, Lemma 30.2.2, Tag 01XB): the obstruction to lifting a global section of
`N` to `M` along a surjection `M → N` with quasi-coherent kernel lies in `H¹` of the kernel.
The proof given here does not go through cohomology: a local lift on `D(f)` shows that a power of
`f` times the section lifts, and the `f` for which this happens generate the unit ideal.
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}}

/-- The `R`-linear restriction map `Γ(M, U) → Γ(M, V)` of the sheaf of `R`-modules underlying an
`𝒪_{Spec R}`-module. -/
noncomputable def specRes (M : (Spec R).Modules) {U V : (Spec R).Opens} (h : V ≤ U) :
    (modulesSpecToSheaf.obj M).obj.obj (op U) →ₗ[R]
      (modulesSpecToSheaf.obj M).obj.obj (op V) :=
  ((modulesSpecToSheaf.obj M).obj.map (homOfLE h).op).hom

/-- For a quasi-coherent `𝒪_{Spec R}`-module `M`, the restriction `Γ(M, Spec R) → Γ(M, D(f))` is
a localization away from `f`. -/
instance isLocalizedModule_res_basicOpen (M : (Spec R).Modules) [M.IsQuasicoherent] (f : R) :
    IsLocalizedModule (Submonoid.powers f)
      (specRes M (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)) := by
  have h := Scheme.Modules.toOpen_fromTildeΓ_app M (PrimeSpectrum.basicOpen f)
  have := IsLocalizedModule.of_linearEquiv (Submonoid.powers f)
    (tilde.toOpen ((modulesSpecToSheaf.obj M).presheaf.obj (op ⊤))
      (PrimeSpectrum.basicOpen f)).hom
    (asIso ((modulesSpecToSheaf.map M.fromTildeΓ).1.app
      (op (PrimeSpectrum.basicOpen f)))).toLinearEquiv
  unfold specRes
  erw [← h]
  exact this

/-- The `R`-linear map on sections over `W` of a morphism of `𝒪_{Spec R}`-modules. -/
noncomputable def specApp {M N : (Spec R).Modules} (φ : M ⟶ N) (W : (Spec R).Opens) :
    (modulesSpecToSheaf.obj M).obj.obj (op W) →ₗ[R] (modulesSpecToSheaf.obj N).obj.obj (op W) :=
  ((modulesSpecToSheaf.map φ).1.app (op W)).hom

lemma specApp_specRes {M N : (Spec R).Modules} (φ : M ⟶ N) {U V : (Spec R).Opens} (h : V ≤ U)
    (x : (modulesSpecToSheaf.obj M).obj.obj (op U)) :
    specApp φ V (specRes M h x) = specRes N h (specApp φ U x) :=
  congrArg (fun g ↦ ModuleCat.Hom.hom g x)
    ((modulesSpecToSheaf.map φ).1.naturality (homOfLE h).op)

/-- On `Spec R`, a locally surjective morphism of quasi-coherent modules is surjective on global
sections. This is the consequence of Stacks, Lemma 30.2.2 (Tag 01XB) for `H¹`, proved directly:
if `s` lifts on `D(f)`, then some `f ^ n • s` lifts globally, and the `f` that occur generate the
unit ideal. -/
theorem surjective_specApp_top_of_isLocallySurjective {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N)
    (hφ : TopCat.Presheaf.IsLocallySurjective φ.mapPresheaf) :
    Function.Surjective (specApp φ ⊤) := by
  intro s
  let J : Ideal R := Submodule.comap (LinearMap.toSpanSingleton R _ s)
    (LinearMap.range (specApp φ ⊤))
  suffices hJ : J = ⊤ by
    obtain ⟨m, hm⟩ : (1 : R) ∈ J := hJ ▸ Submodule.mem_top
    exact ⟨m, by simpa using hm⟩
  by_contra hJ
  obtain ⟨P, hP, hJP⟩ := Ideal.exists_le_maximal J hJ
  let x : PrimeSpectrum R := ⟨P, hP.isPrime⟩
  obtain ⟨V, hV, ⟨t, ht⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff _).mp hφ ⊤ s x trivial
  obtain ⟨_, ⟨f, rfl⟩, hxf, hfV⟩ :=
    Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens hxV
  have hfV' : PrimeSpectrum.basicOpen f ≤ V := hfV
  -- the restriction of the local lift to `D(f)`
  let t' := specRes M hfV' t
  have ht' : specApp φ _ t' = specRes N (le_top : PrimeSpectrum.basicOpen f ≤ ⊤) s := by
    refine (specApp_specRes φ hfV' t).trans ((congrArg (specRes N hfV') ht).trans ?_)
    change (N.presheaf.map _ ≫ N.presheaf.map _) s = _
    rw [← Functor.map_comp]
    rfl
  obtain ⟨⟨m, c⟩, hmc⟩ := IsLocalizedModule.surj (Submonoid.powers f)
    (specRes M (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)) t'
  have h1 : specRes N (le_top : PrimeSpectrum.basicOpen f ≤ ⊤) ((c : R) • s) =
      specRes N (le_top : PrimeSpectrum.basicOpen f ≤ ⊤) (specApp φ ⊤ m) := by
    have e1 := (specRes N (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).map_smul (c : R) s
    have e2 := (specApp φ (PrimeSpectrum.basicOpen f)).map_smul (c : R) t'
    exact e1.trans ((congrArg _ ht'.symm).trans (e2.symm.trans
      ((congrArg _ hmc).trans (specApp_specRes φ _ m))))
  obtain ⟨c', hc'⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f) h1
  obtain ⟨a, ha⟩ := c.2
  obtain ⟨b, hb⟩ := c'.2
  have hmem : f ^ (b + a) ∈ J := by
    refine ⟨(c' : R) • m, ?_⟩
    have e3 := (specApp φ ⊤).map_smul (c' : R) m
    refine e3.trans (hc'.symm.trans ?_)
    change _ = (f ^ (b + a)) • s
    simp only at ha hb
    rw [pow_add, mul_smul, hb, ha]
    rfl
  exact hxf (hP.isPrime.mem_of_pow_mem _ (hJP hmem))

/-! ### Affine opens of an arbitrary scheme -/

/-- Restriction along an open immersion preserves local surjectivity of a morphism of modules. -/
lemma isLocallySurjective_restrict {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g]
    {M N : X.Modules} (φ : M ⟶ N) (hφ : TopCat.Presheaf.IsLocallySurjective φ.mapPresheaf) :
    TopCat.Presheaf.IsLocallySurjective
      ((Scheme.Modules.restrictFunctor g).map φ).mapPresheaf := by
  rw [TopCat.Presheaf.isLocallySurjective_iff] at hφ ⊢
  intro W t y hy
  obtain ⟨V, hVW, ⟨s, hs⟩, hyV⟩ := hφ (g ''ᵁ W) t (g y) (g.apply_mem_image_iff.mpr hy)
  have hle : g ⁻¹ᵁ V ≤ W := (g.preimage_mono hVW).trans_eq (g.preimage_image_eq W)
  refine ⟨g ⁻¹ᵁ V, hle, ⟨M.presheaf.map (homOfLE (g.image_preimage_le V)).op s, ?_⟩, hyV⟩
  change φ.app _ (M.presheaf.map _ s) = N.presheaf.map _ t
  rw [← Scheme.Modules.mapPresheaf_app, ← ConcreteCategory.comp_apply, NatTrans.naturality,
    ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app]
  refine (congrArg (N.presheaf.map (homOfLE (g.image_preimage_le V)).op) hs).trans ?_
  change (N.presheaf.map _ ≫ N.presheaf.map _) t = _
  rw [← Functor.map_comp]
  rfl

/-- On an affine open `U` of a scheme, a locally surjective morphism of quasi-coherent modules is
surjective on sections over `U` (the `H¹` part of Stacks, Lemma 30.2.2, Tag 01XB). -/
theorem surjective_app_of_isAffineOpen {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N)
    (hφ : TopCat.Presheaf.IsLocallySurjective φ.mapPresheaf) {U : X.Opens}
    (hU : IsAffineOpen U) : Function.Surjective (φ.app U) := by
  have key := surjective_specApp_top_of_isLocallySurjective
    ((Scheme.Modules.restrictFunctor hU.fromSpec).map φ)
    (isLocallySurjective_restrict hU.fromSpec φ hφ)
  have hU' : hU.fromSpec ''ᵁ ⊤ = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, IsAffineOpen.opensRange_fromSpec]
  have : Function.Surjective (φ.app (hU.fromSpec ''ᵁ ⊤)) := key
  rwa [hU'] at this

end AlgebraicGeometry
