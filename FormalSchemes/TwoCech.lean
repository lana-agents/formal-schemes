/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Algebra.Module.SnakeLemma
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The Čech complex of a two-set covering, algebraically

Let `X = U ∪ V` be covered by two opens and let `F` be a sheaf of modules. The ordered Čech
complex of the covering `(U, V)` (Stacks, Definition 20.23.2, Tag 01FI) has only two nonzero
terms, because there is no strictly increasing triple of indices in `{0, 1}`:
`F(U) × F(V) → F(U ∩ V)`, `(s, t) ↦ s|_{U ∩ V} - t|_{U ∩ V}`. So its cohomology is the kernel
`H⁰` and the cokernel `H¹` of a single map, and vanishes in degrees `≥ 2`.

This file isolates the algebra of that situation: two linear maps `f : P → R` and `g : Q → R`
(the two restriction maps), the differential `TwoCech.d f g : P × Q → R`, and
* `TwoCech.H0 f g`, its kernel, and `TwoCech.H1 f g`, its cokernel;
* the maps `TwoCech.mapH0`, `TwoCech.mapH1` induced by a morphism of such data;
* for a short exact sequence of such data, the connecting map `TwoCech.δ` and the six-term exact
  sequence `0 → H⁰' → H⁰ → H⁰'' → H¹' → H¹ → H¹'' → 0` (`TwoCech.mapH0_injective`,
  `TwoCech.exact_mapH0`, `TwoCech.exact_mapH0_δ`, `TwoCech.exact_δ_mapH1`,
  `TwoCech.exact_mapH1`, `TwoCech.mapH1_surjective`).

Applied to the sections of a short exact sequence of quasi-coherent modules on a scheme covered
by two affine opens with affine intersection, this is the Mayer–Vietoris sequence (Stacks,
Lemma 20.8.2, Tag 01EB) together with the vanishing of `H²`: the functor `H¹` is right exact,
which is the cohomological input of the Grothendieck existence theorem for curves.
-/

universe u

open Function

namespace TwoCech

variable {A : Type*} [CommRing A]
variable {P Q R : Type*} [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
  [AddCommGroup R] [Module A R]

/-- The Čech differential `(s, t) ↦ f s - g t` of a two-set covering whose restriction maps
are `f` and `g` (Stacks, Definition 20.23.2, Tag 01FI). -/
def d (f : P →ₗ[A] R) (g : Q →ₗ[A] R) : P × Q →ₗ[A] R := f.coprod (-g)

@[simp]
lemma d_apply (f : P →ₗ[A] R) (g : Q →ₗ[A] R) (x : P × Q) : d f g x = f x.1 - g x.2 := by
  simp [d, sub_eq_add_neg]

/-- Čech `H⁰` of a two-set covering: pairs of sections agreeing on the overlap. -/
abbrev H0 (f : P →ₗ[A] R) (g : Q →ₗ[A] R) : Submodule A (P × Q) := LinearMap.ker (d f g)

/-- Čech `H¹` of a two-set covering: sections on the overlap modulo differences of sections on
the two opens. -/
abbrev H1 (f : P →ₗ[A] R) (g : Q →ₗ[A] R) : Type _ := R ⧸ LinearMap.range (d f g)

lemma mem_H0 {f : P →ₗ[A] R} {g : Q →ₗ[A] R} {x : P × Q} : x ∈ H0 f g ↔ f x.1 = g x.2 := by
  simp [sub_eq_zero]

variable {P' Q' R' : Type*} [AddCommGroup P'] [Module A P'] [AddCommGroup Q'] [Module A Q']
  [AddCommGroup R'] [Module A R']
variable {f : P →ₗ[A] R} {g : Q →ₗ[A] R} {f' : P' →ₗ[A] R'} {g' : Q' →ₗ[A] R'}

/-- A morphism of two-set Čech data commutes with the differentials. -/
lemma d_comp (α : P →ₗ[A] P') (β : Q →ₗ[A] Q') (γ : R →ₗ[A] R')
    (hf : f' ∘ₗ α = γ ∘ₗ f) (hg : g' ∘ₗ β = γ ∘ₗ g) :
    d f' g' ∘ₗ α.prodMap β = γ ∘ₗ d f g := by
  refine LinearMap.ext fun x ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.prodMap_apply, d_apply, map_sub]
  rw [← LinearMap.comp_apply f' α, hf, ← LinearMap.comp_apply g' β, hg]
  rfl

/-- The map on `H⁰` induced by a morphism of two-set Čech data. -/
def mapH0 (α : P →ₗ[A] P') (β : Q →ₗ[A] Q') (γ : R →ₗ[A] R')
    (hf : f' ∘ₗ α = γ ∘ₗ f) (hg : g' ∘ₗ β = γ ∘ₗ g) : H0 f g →ₗ[A] H0 f' g' :=
  (α.prodMap β).restrict fun x hx ↦ by
    simp only [LinearMap.mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply, d_comp α β γ hf hg, LinearMap.comp_apply, hx, map_zero]

@[simp]
lemma mapH0_apply (α : P →ₗ[A] P') (β : Q →ₗ[A] Q') (γ : R →ₗ[A] R')
    (hf : f' ∘ₗ α = γ ∘ₗ f) (hg : g' ∘ₗ β = γ ∘ₗ g) (x : H0 f g) :
    (mapH0 α β γ hf hg x : P' × Q') = (α x.1.1, β x.1.2) := rfl

/-- The map on `H¹` induced by a morphism of two-set Čech data. -/
def mapH1 (α : P →ₗ[A] P') (β : Q →ₗ[A] Q') (γ : R →ₗ[A] R')
    (hf : f' ∘ₗ α = γ ∘ₗ f) (hg : g' ∘ₗ β = γ ∘ₗ g) : H1 f g →ₗ[A] H1 f' g' :=
  (LinearMap.range (d f g)).mapQ (LinearMap.range (d f' g')) γ fun x hx ↦ by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨α.prodMap β y, by rw [← LinearMap.comp_apply, d_comp α β γ hf hg,
      LinearMap.comp_apply]⟩

@[simp]
lemma mapH1_mk (α : P →ₗ[A] P') (β : Q →ₗ[A] Q') (γ : R →ₗ[A] R')
    (hf : f' ∘ₗ α = γ ∘ₗ f) (hg : g' ∘ₗ β = γ ∘ₗ g) (x : R) :
    mapH1 α β γ hf hg (Submodule.Quotient.mk x) = Submodule.Quotient.mk (γ x) := rfl

/-! ### Short exact sequences of two-set Čech data -/

section SES

variable {P'' Q'' R'' : Type*} [AddCommGroup P''] [Module A P''] [AddCommGroup Q'']
  [Module A Q''] [AddCommGroup R''] [Module A R'']
  {f'' : P'' →ₗ[A] R''} {g'' : Q'' →ₗ[A] R''}
  (α₁ : P' →ₗ[A] P) (β₁ : Q' →ₗ[A] Q) (γ₁ : R' →ₗ[A] R)
  (α₂ : P →ₗ[A] P'') (β₂ : Q →ₗ[A] Q'') (γ₂ : R →ₗ[A] R'')
  (hf₁ : f ∘ₗ α₁ = γ₁ ∘ₗ f') (hg₁ : g ∘ₗ β₁ = γ₁ ∘ₗ g')
  (hf₂ : f'' ∘ₗ α₂ = γ₂ ∘ₗ f) (hg₂ : g'' ∘ₗ β₂ = γ₂ ∘ₗ g)

lemma exact_prodMap (hα : Exact α₁ α₂) (hβ : Exact β₁ β₂) :
    Exact (α₁.prodMap β₁) (α₂.prodMap β₂) := by
  rintro ⟨x, y⟩
  simp only [LinearMap.prodMap_apply, Set.mem_range, Prod.ext_iff]
  constructor
  · rintro ⟨hx, hy⟩
    obtain ⟨a, rfl⟩ := (hα x).mp hx
    obtain ⟨b, rfl⟩ := (hβ y).mp hy
    exact ⟨(a, b), rfl, rfl⟩
  · rintro ⟨⟨a, b⟩, rfl, rfl⟩
    exact ⟨hα.apply_apply_eq_zero a, hβ.apply_apply_eq_zero b⟩

include hf₁ hg₁ in
/-- `H⁰` is left exact, first half: `H⁰' → H⁰` is injective. -/
lemma mapH0_injective (hα : Injective α₁) (hβ : Injective β₁) :
    Injective (mapH0 α₁ β₁ γ₁ hf₁ hg₁) := by
  intro x y h
  have h' := congrArg Subtype.val h
  simp only [mapH0_apply, Prod.mk.injEq] at h'
  exact Subtype.ext (Prod.ext (hα h'.1) (hβ h'.2))

include hf₁ hg₁ hf₂ hg₂ in
/-- `H⁰` is left exact, second half: `H⁰' → H⁰ → H⁰''` is exact. -/
lemma exact_mapH0 (hα : Exact α₁ α₂) (hβ : Exact β₁ β₂) (hγ : Injective γ₁) :
    Exact (mapH0 α₁ β₁ γ₁ hf₁ hg₁) (mapH0 α₂ β₂ γ₂ hf₂ hg₂) := by
  rintro ⟨⟨x, y⟩, hxy⟩
  constructor
  · intro h
    have h' := congrArg Subtype.val h
    simp only [mapH0_apply, Submodule.coe_zero, Prod.mk_eq_zero] at h'
    obtain ⟨a, rfl⟩ := (hα x).mp h'.1
    obtain ⟨b, rfl⟩ := (hβ y).mp h'.2
    refine ⟨⟨(a, b), ?_⟩, rfl⟩
    rw [mem_H0] at hxy ⊢
    apply hγ
    rw [← LinearMap.comp_apply, ← hf₁, ← LinearMap.comp_apply γ₁, ← hg₁]
    exact hxy
  · rintro ⟨⟨⟨a, b⟩, _⟩, h⟩
    rw [← h]
    ext <;> simp [hα.apply_apply_eq_zero, hβ.apply_apply_eq_zero]

lemma prodMap_surjective (hα₂ : Surjective α₂) (hβ₂ : Surjective β₂) :
    Surjective (α₂.prodMap β₂) := fun x ↦ by
  obtain ⟨a, ha⟩ := hα₂ x.1
  obtain ⟨b, hb⟩ := hβ₂ x.2
  exact ⟨(a, b), Prod.ext ha hb⟩

section Connecting

variable (hα : Exact α₁ α₂) (hβ : Exact β₁ β₂) (hγ : Exact γ₁ γ₂)
  (hα₂ : Surjective α₂) (hβ₂ : Surjective β₂) (hγ₁ : Injective γ₁)

/-- The connecting map `H⁰'' → H¹'` of a short exact sequence of two-set Čech data, given by
the snake lemma (`SnakeLemma.δ'`): lift a pair of sections agreeing on the overlap, take the
difference of the lifts on the overlap, and observe it comes from the sub. -/
noncomputable def δ : H0 f'' g'' →ₗ[A] H1 f' g' :=
  SnakeLemma.δ' (d f' g') (d f g) (d f'' g'') (α₁.prodMap β₁) (α₂.prodMap β₂)
    (exact_prodMap α₁ β₁ α₂ β₂ hα hβ) γ₁ γ₂ hγ (d_comp α₁ β₁ γ₁ hf₁ hg₁).symm
    (d_comp α₂ β₂ γ₂ hf₂ hg₂).symm (H0 f'' g'').subtype
    (LinearMap.exact_subtype_ker_map _) (LinearMap.range (d f' g')).mkQ
    (LinearMap.exact_map_mkQ_range _) (prodMap_surjective α₂ β₂ hα₂ hβ₂) hγ₁

lemma δ_eq (x : H0 f'' g'') (y : P × Q) (hy : (α₂ y.1, β₂ y.2) = (x : P'' × Q'')) (z : R')
    (hz : γ₁ z = d f g y) :
    δ α₁ β₁ γ₁ α₂ β₂ γ₂ hf₁ hg₁ hf₂ hg₂ hα hβ hγ hα₂ hβ₂ hγ₁ x = Submodule.Quotient.mk z :=
  SnakeLemma.δ'_eq (x := x) (y := y) (hy := by simpa using hy) (z := z) (hz := hz) ..

/-- Exactness of `H⁰ → H⁰'' → H¹'`. -/
lemma exact_mapH0_δ :
    Exact (mapH0 α₂ β₂ γ₂ hf₂ hg₂) (δ α₁ β₁ γ₁ α₂ β₂ γ₂ hf₁ hg₁ hf₂ hg₂ hα hβ hγ hα₂ hβ₂ hγ₁) :=
  SnakeLemma.exact_δ'_right _ _ _ _ _ _ _ _ _ _ _ (H0 f g).subtype
    (LinearMap.exact_subtype_ker_map _) _ _ _ _ _ _ _ (LinearMap.ext fun _ ↦ rfl)
    (Submodule.injective_subtype _)

/-- Exactness of `H⁰'' → H¹' → H¹`. -/
lemma exact_δ_mapH1 :
    Exact (δ α₁ β₁ γ₁ α₂ β₂ γ₂ hf₁ hg₁ hf₂ hg₂ hα hβ hγ hα₂ hβ₂ hγ₁)
      (mapH1 α₁ β₁ γ₁ hf₁ hg₁) :=
  SnakeLemma.exact_δ'_left _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (LinearMap.range (d f g)).mkQ
    (LinearMap.exact_map_mkQ_range _) _ _ _ (LinearMap.ext fun _ ↦ rfl)
    (Submodule.mkQ_surjective _)

end Connecting

include hf₂ hg₂ in
/-- Exactness of `H¹' → H¹ → H¹''`. -/
lemma exact_mapH1 (hα₂ : Surjective α₂) (hβ₂ : Surjective β₂) (hγ : Exact γ₁ γ₂) :
    Exact (mapH1 α₁ β₁ γ₁ hf₁ hg₁) (mapH1 α₂ β₂ γ₂ hf₂ hg₂) := by
  intro x
  induction x using Submodule.Quotient.induction_on with | H x => ?_
  simp only [mapH1_mk, Submodule.Quotient.mk_eq_zero, Set.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨y', rfl⟩ := prodMap_surjective α₂ β₂ hα₂ hβ₂ y
    rw [← LinearMap.comp_apply, d_comp α₂ β₂ γ₂ hf₂ hg₂, LinearMap.comp_apply] at hy
    obtain ⟨z, hz⟩ := (hγ (x - d f g y')).mp (by rw [map_sub, hy, sub_self])
    refine ⟨Submodule.Quotient.mk z, ?_⟩
    rw [mapH1_mk, hz, Submodule.Quotient.eq]
    exact ⟨-y', by simp [neg_add_eq_sub]⟩
  · rintro ⟨y, hy⟩
    induction y using Submodule.Quotient.induction_on with | H y => ?_
    rw [mapH1_mk, Submodule.Quotient.eq] at hy
    obtain ⟨w, hw⟩ := hy
    refine ⟨-α₂.prodMap β₂ w, ?_⟩
    rw [map_neg, ← LinearMap.comp_apply, d_comp α₂ β₂ γ₂ hf₂ hg₂, LinearMap.comp_apply, hw,
      map_sub, hγ.apply_apply_eq_zero, zero_sub, neg_neg]

include hf₂ hg₂ in
/-- `H¹ → H¹''` is surjective: `H²` of a two-set covering vanishes. -/
lemma mapH1_surjective (hγ₂ : Surjective γ₂) : Surjective (mapH1 α₂ β₂ γ₂ hf₂ hg₂) := by
  intro x
  induction x using Submodule.Quotient.induction_on with | H x => ?_
  obtain ⟨y, rfl⟩ := hγ₂ x
  exact ⟨Submodule.Quotient.mk y, rfl⟩

end SES

end TwoCech
