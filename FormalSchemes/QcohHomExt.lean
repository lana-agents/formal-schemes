/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.QcohCover

/-!
# Morphisms of quasi-coherent modules are determined by sections over affine opens

* `Scheme.Modules.hom_ext_of_isIso_fromTildeΓ`: on `Spec R`, two morphisms out of a module `Q`
  with `Q ≅ Γ(Q)^~` agreeing on global sections are equal;
* `Scheme.Modules.hom_ext_pushforward_tilde`: two morphisms `P ⟶ f_* M^~`, for an open immersion
  `f : Spec R → X` along which `P` restricts to the `~` of its sections, agreeing on the sections
  over the image of `f`, are equal.
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}}

/-- On `Spec R`, morphisms out of `Q ≅ Γ(Q)^~` are determined by global sections. -/
lemma hom_ext_of_isIso_fromTildeΓ {Q Q' : (Spec R).Modules}
    [IsIso (Scheme.Modules.fromTildeΓ (R := R) Q)] {a b : Q ⟶ Q'}
    (h : ∀ x : Γ(Q, ⊤), a.app ⊤ x = b.app ⊤ x) : a = b := by
  rw [← cancel_epi (Scheme.Modules.fromTildeΓ (R := R) Q)]
  apply ((tilde.adjunction (R := R)).homEquiv _ _).injective
  have hΓ : (moduleSpecΓFunctor (R := R)).map a = (moduleSpecΓFunctor (R := R)).map b := by
    ext x
    exact h x
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact congrArg (_ ≫ ·) (((moduleSpecΓFunctor (R := R)).map_comp _ _).trans
    ((congrArg (_ ≫ ·) hΓ).trans ((moduleSpecΓFunctor (R := R)).map_comp _ _).symm))

/-- Morphisms `P ⟶ f_* M^~` are determined by the sections over the image of `f`. -/
lemma hom_ext_pushforward_tilde {X : Scheme.{u}} (f : Spec R ⟶ X) [IsOpenImmersion f]
    (P : X.Modules) [IsIso (Scheme.Modules.fromTildeΓ (R := R) (P.restrict f))]
    (M : ModuleCat.{u} R) {α β : P ⟶ (pushforward f).obj ((tilde.functor R).obj M)}
    (h : ∀ x : Γ(P, f ''ᵁ ⊤), α.app (f ''ᵁ ⊤) x = β.app (f ''ᵁ ⊤) x) : α = β := by
  let adj := restrictAdjunction f
  have ea : (adj.homEquiv _ _).symm α = (restrictFunctor f).map α ≫ adj.counit.app _ :=
    Adjunction.homEquiv_counit adj P _ α
  have eb : (adj.homEquiv _ _).symm β = (restrictFunctor f).map β ≫ adj.counit.app _ :=
    Adjunction.homEquiv_counit adj P _ β
  have key : (adj.homEquiv _ _).symm α = (adj.homEquiv _ _).symm β := by
    refine hom_ext_of_isIso_fromTildeΓ (R := R) fun x ↦ ?_
    have hc : ∀ γ : P ⟶ (pushforward f).obj ((tilde.functor R).obj M),
        ((restrictFunctor f).map γ ≫ adj.counit.app _).app ⊤ x =
          (adj.counit.app _).app ⊤ (((restrictFunctor f).map γ).app ⊤ x) := fun _ ↦ rfl
    have hr : ∀ γ : P ⟶ (pushforward f).obj ((tilde.functor R).obj M),
        ((restrictFunctor f).map γ).app ⊤ x = γ.app (f ''ᵁ ⊤) x := fun _ ↦ rfl
    rw [ea, eb]
    exact (hc α).trans ((congrArg (ConcreteCategory.hom ((adj.counit.app _).app ⊤))
      ((hr α).trans ((h x).trans (hr β).symm))).trans (hc β).symm)
  exact (adj.homEquiv _ _).symm.injective key

end AlgebraicGeometry.Scheme.Modules
