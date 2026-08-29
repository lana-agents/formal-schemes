import FormalSchemes.ActionQuotientSeparatingSections

set_option linter.style.header false

/-!
# The stalk maps of an action quotient are isomorphisms over a separating open

This is the missing half of "the projection of a free, properly discontinuous action quotient is a
local isomorphism". `FormalSchemes.ActionDiscontinuous` supplies the topological half — over a
separating open `U`, `π.base` restricts to an open embedding — and
`FormalSchemes.ActionQuotientFormalScheme` shows that the two together make the quotient a formal
scheme. What was open is the statement proved here:

> if the action is properly discontinuous on an open `U` and `x ∈ U`, then `π.stalkMap x` is an
> isomorphism.

The proof is `CategoryTheory.bijective_restrictPullback` — over a separating open the sections of
the quotient are exactly the sections of `X` — taken to the colimit. Both halves need the
neighbourhoods `π '' V` for `V ≤ U`, which are cofinal at `π x` precisely because `π` is an open
map and `V ↦ V ⊓ U` shrinks any neighbourhood into `U`.

## Main results

* `CategoryTheory.bijective_stalkMap_actionQuotientπ`, `isIso_stalkMap_actionQuotientπ`: the stalk
  maps of the coequalizer projection are isomorphisms over a separating open.

The transport to *any* projection exhibiting the quotient, along
`CategoryTheory.IsActionQuotient.isoActionQuotient`, is one module further on:
`AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_of_isProperlyDiscontinuousOn` in
`FormalSchemes.FreeActionQuotientFormalScheme`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace Opposite
open AlgebraicGeometry AlgebraicGeometry.LocallyRingedSpace

universe u

namespace CategoryTheory

variable {G : Type u} [Group G] {X : LocallyRingedSpace.{u}} (a : G →* Aut X)
variable [HasCoproduct fun _ : G => X]
  [HasCoequalizer (actionQuotientLeft a) (actionQuotientRight G X)]

/-- The comparison map of a morphism of locally ringed spaces, in the two spellings the tree uses:
`Hom.c` (Mathlib's stalk API) and `Hom.toShHom.hom.c` (the sections API of
`FormalSchemes.ActionQuotientSections`). They are the same map, but not syntactically, so a rewrite
between the two halves of the argument needs this. -/
theorem c_app_eq_toShHom {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (V : Opens Y.toTopCat) :
    f.c.app (op V) = f.toShHom.hom.c.app (op V) :=
  rfl

/-- **Restricting a section of the quotient before pulling it back.** Every restriction map between
the same pair of opens is the same map, so the inclusion `ι` may be given by the caller. -/
theorem restrictPullback_map (V : Opens X.toTopCat)
    {V' : Opens (actionQuotient a).toTopCat} (hle : quotientImage a V ≤ V')
    (u : ToType ((actionQuotient a).presheaf.obj (op V')))
    (ι : V ⟶ (Opens.map (actionQuotientπ a).toShHom.hom.base).obj V') :
    restrictPullback a V ((actionQuotient a).presheaf.map (homOfLE hle).op u) =
      X.presheaf.map ι.op ((actionQuotientπ a).toShHom.hom.c.app (op V') u) := by
  rw [restrictPullback, c_app_naturality]
  refine (presheaf_map_comp_apply X.presheaf _ _ _).trans ?_
  exact ConcreteCategory.congr_hom (presheaf_map_congr X.presheaf _ _) _

/-- **The stalk maps of the coequalizer projection are bijective over a separating open.**
Surjectivity: a germ at `x` is represented on some `V ≤ U`, and
`bijective_restrictPullback` produces a section of the quotient over `π '' V` restricting to it.
Injectivity: two germs with the same image agree on some `A ∋ x`, hence on `A ⊓ U`, and the same
bijection makes their restrictions to `π '' (A ⊓ U)` equal. -/
theorem bijective_stalkMap_actionQuotientπ {U : Opens X.toTopCat}
    (hU : IsProperlyDiscontinuousOn a (U : Set X)) {x : X} (hx : x ∈ U) :
    Function.Bijective ((actionQuotientπ a).stalkMap x) := by
  constructor
  · intro z₁ z₂ hz
    obtain ⟨V₁, hy₁, u₁, rfl⟩ := (actionQuotient a).presheaf.exists_germ_eq z₁
    obtain ⟨V₂, hy₂, u₂, rfl⟩ := (actionQuotient a).presheaf.exists_germ_eq z₂
    rw [LocallyRingedSpace.stalkMap_germ_apply, LocallyRingedSpace.stalkMap_germ_apply,
      c_app_eq_toShHom, c_app_eq_toShHom] at hz
    obtain ⟨A, hxA, iA₁, iA₂, heq⟩ := X.presheaf.germ_eq x _ _ _ _ hz
    have hxV : x ∈ A ⊓ U := ⟨hxA, hx⟩
    have hle₁ : quotientImage a (A ⊓ U) ≤ V₁ := by
      rintro z ⟨w, hw, rfl⟩
      exact iA₁.le hw.1
    have hle₂ : quotientImage a (A ⊓ U) ≤ V₂ := by
      rintro z ⟨w, hw, rfl⟩
      exact iA₂.le hw.1
    have hmem : (actionQuotientπ a).base x ∈ quotientImage a (A ⊓ U) := ⟨x, hxV, rfl⟩
    have hres : restrictPullback a (A ⊓ U)
          ((actionQuotient a).presheaf.map (homOfLE hle₁).op u₁) =
        restrictPullback a (A ⊓ U)
          ((actionQuotient a).presheaf.map (homOfLE hle₂).op u₂) := by
      rw [restrictPullback_map a _ hle₁ u₁ (homOfLE (le_trans inf_le_left iA₁.le)),
        restrictPullback_map a _ hle₂ u₂ (homOfLE (le_trans inf_le_left iA₂.le))]
      calc X.presheaf.map (homOfLE (le_trans inf_le_left iA₁.le)).op
              ((actionQuotientπ a).toShHom.hom.c.app (op V₁) u₁)
          = X.presheaf.map (homOfLE (inf_le_left : A ⊓ U ≤ A)).op
              (X.presheaf.map iA₁.op
                ((actionQuotientπ a).toShHom.hom.c.app (op V₁) u₁)) := by
            refine Eq.trans ?_ (presheaf_map_comp_apply X.presheaf _ _ _).symm
            exact ConcreteCategory.congr_hom (presheaf_map_congr X.presheaf _ _) _
        _ = X.presheaf.map (homOfLE (inf_le_left : A ⊓ U ≤ A)).op
              (X.presheaf.map iA₂.op
                ((actionQuotientπ a).toShHom.hom.c.app (op V₂) u₂)) := congrArg _ heq
        _ = X.presheaf.map (homOfLE (le_trans inf_le_left iA₂.le)).op
              ((actionQuotientπ a).toShHom.hom.c.app (op V₂) u₂) := by
            refine (presheaf_map_comp_apply X.presheaf _ _ _).trans ?_
            exact ConcreteCategory.congr_hom (presheaf_map_congr X.presheaf _ _) _
    have := (bijective_restrictPullback a hU (V := A ⊓ U) inf_le_right).1 hres
    calc (actionQuotient a).presheaf.germ V₁ ((actionQuotientπ a).base x) hy₁ u₁
        = (actionQuotient a).presheaf.germ (quotientImage a (A ⊓ U))
            ((actionQuotientπ a).base x) hmem
            ((actionQuotient a).presheaf.map (homOfLE hle₁).op u₁) :=
          ((actionQuotient a).presheaf.germ_res_apply (homOfLE hle₁) _ hmem u₁).symm
      _ = (actionQuotient a).presheaf.germ (quotientImage a (A ⊓ U))
            ((actionQuotientπ a).base x) hmem
            ((actionQuotient a).presheaf.map (homOfLE hle₂).op u₂) := by rw [this]
      _ = (actionQuotient a).presheaf.germ V₂ ((actionQuotientπ a).base x) hy₂ u₂ :=
          (actionQuotient a).presheaf.germ_res_apply (homOfLE hle₂) _ hmem u₂
  · intro z
    obtain ⟨V₀, hxV₀, s, rfl⟩ := X.presheaf.exists_germ_eq z
    have hxV : x ∈ V₀ ⊓ U := ⟨hxV₀, hx⟩
    obtain ⟨u, hu⟩ := (bijective_restrictPullback a hU (V := V₀ ⊓ U) inf_le_right).2
      (X.presheaf.map (homOfLE (inf_le_left : V₀ ⊓ U ≤ V₀)).op s)
    have hmem : (actionQuotientπ a).base x ∈ quotientImage a (V₀ ⊓ U) := ⟨x, hxV, rfl⟩
    refine ⟨(actionQuotient a).presheaf.germ (quotientImage a (V₀ ⊓ U))
      ((actionQuotientπ a).base x) hmem u, ?_⟩
    rw [LocallyRingedSpace.stalkMap_germ_apply, c_app_eq_toShHom]
    calc X.presheaf.germ
            ((Opens.map (actionQuotientπ a).toShHom.hom.base).obj (quotientImage a (V₀ ⊓ U)))
            x hmem ((actionQuotientπ a).toShHom.hom.c.app (op (quotientImage a (V₀ ⊓ U))) u)
        = X.presheaf.germ (V₀ ⊓ U) x hxV (restrictPullback a (V₀ ⊓ U) u) :=
          (X.presheaf.germ_res_apply (homOfLE (self_le_preimage_quotientImage a (V₀ ⊓ U)))
            x hxV _).symm
      _ = X.presheaf.germ (V₀ ⊓ U) x hxV
            (X.presheaf.map (homOfLE (inf_le_left : V₀ ⊓ U ≤ V₀)).op s) := by rw [hu]
      _ = X.presheaf.germ V₀ x hxV₀ s :=
          X.presheaf.germ_res_apply (homOfLE inf_le_left) x hxV s

/-- **The stalk maps of the coequalizer projection are isomorphisms over a separating open.** -/
theorem isIso_stalkMap_actionQuotientπ {U : Opens X.toTopCat}
    (hU : IsProperlyDiscontinuousOn a (U : Set X)) {x : X} (hx : x ∈ U) :
    IsIso ((actionQuotientπ a).stalkMap x) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_stalkMap_actionQuotientπ a hU hx)

end CategoryTheory
