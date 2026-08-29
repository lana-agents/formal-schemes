import FormalSchemes.ActionInvariantExtension

set_option linter.style.header false

/-!
# Over a separating open, the quotient has exactly the sections of `X`

`FormalSchemes.ActionQuotientInvariantSections` identifies the sections of `X / G` over an open `V`
of the quotient with the *invariant* sections of `X` over `π⁻¹ V`, for an arbitrary action.
`FormalSchemes.ActionInvariantExtension` says that when the action is properly discontinuous on an
open `U` and `V ≤ U`, the invariant sections of `X` over the saturation of `V` are in bijection with
*all* sections of `X` over `V` — one is the unique extension of the other, translate by translate.

Composing the two gives the statement this file is for:

> for `V ≤ U` with `U` separating, `u ↦ (π^* u)|_V` is a **bijection** from the sections of the
> quotient over `π '' V` to the sections of `X` over `V`.

That is the section-level form of "`π` is a local isomorphism", and taking the colimit over the
`V ∋ x` turns it into the statement that the stalk maps of `π` are isomorphisms.

## Main results

* `CategoryTheory.quotientImage`: the image of `V` in the quotient, as an open.
* `CategoryTheory.isInvariantSection_actionQuotientπ_c_app`: a pullback along `π` is invariant.
* `CategoryTheory.restrictPullback`: the map `u ↦ (π^* u)|_V`.
* `CategoryTheory.bijective_restrictPullback`: it is a bijection.

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

/-- **The image of an open of `X` in the quotient.** It is open because the projection of an action
quotient is an open map, with no hypothesis on the action. -/
def quotientImage (V : Opens X.toTopCat) : Opens (actionQuotient a).toTopCat :=
  imageOpen (isActionQuotient_actionQuotientπ a) V

/-- The saturation of `V` is the supremum of its translates. -/
theorem preimage_quotientImage (V : Opens X.toTopCat) :
    (Opens.map (actionQuotientπ a).toShHom.hom.base).obj (quotientImage a V) =
      ⨆ g : G, translate a V g :=
  preimage_imageOpen (isActionQuotient_actionQuotientπ a) V

/-- `V` sits inside the saturation of `V`. -/
theorem self_le_preimage_quotientImage (V : Opens X.toTopCat) :
    V ≤ (Opens.map (actionQuotientπ a).toShHom.hom.base).obj (quotientImage a V) :=
  fun x hx => ⟨x, hx, rfl⟩

/-- **A pullback along the projection is an invariant section.** This is the forward half of the
descent criterion, read through `IsInvariantSection`. -/
theorem isInvariantSection_actionQuotientπ_c_app (V : Opens (actionQuotient a).toTopCat)
    (u : ToType ((actionQuotient a).presheaf.obj (op V))) :
    IsInvariantSection a ((actionQuotientπ a).toShHom.hom.c.app (op V) u) :=
  fun k _ => (exists_actionQuotientπ_c_app_eq_iff_forall a V _).mp ⟨u, rfl⟩ k

/-- **The restriction of a pullback to `V`.** The map the theorem below is about: pull a section of
the quotient back along `π`, then restrict it from the saturation of `V` to `V`. -/
def restrictPullback (V : Opens X.toTopCat)
    (u : ToType ((actionQuotient a).presheaf.obj (op (quotientImage a V)))) :
    ToType (X.presheaf.obj (op V)) :=
  X.presheaf.map (homOfLE (self_le_preimage_quotientImage a V)).op
    ((actionQuotientπ a).toShHom.hom.c.app (op (quotientImage a V)) u)

/-- **Over a separating open the quotient has exactly the sections of `X`.** Injectivity is the
uniqueness of the invariant extension composed with the injectivity of `π^*`; surjectivity is the
existence of the invariant extension composed with the descent criterion. Proper discontinuity
enters only through `AlgebraicGeometry.LocallyRingedSpace.exists_invariant_extension`. -/
theorem bijective_restrictPullback {U : Set X} (hU : IsProperlyDiscontinuousOn a U)
    {V : Opens X.toTopCat} (hVU : (V : Set X) ⊆ U) :
    Function.Bijective (restrictPullback a V) := by
  constructor
  · intro u₁ u₂ hu
    refine LocallyRingedSpace.injective_coequalizer_π_c_app _ _ _ ?_
    exact eq_of_isInvariantSection_of_restrict_eq hU hVU (preimage_quotientImage a V)
      (self_le_preimage_quotientImage a V) (preimage_actionQuotientπ_eq a (quotientImage a V))
      (isInvariantSection_actionQuotientπ_c_app a _ u₁)
      (isInvariantSection_actionQuotientπ_c_app a _ u₂) hu
  · intro s
    obtain ⟨t, hres, hinv⟩ :=
      exists_invariant_extension hU hVU (preimage_quotientImage a V) s
    obtain ⟨u, hu⟩ := (exists_actionQuotientπ_c_app_eq_iff_forall a (quotientImage a V) t).mpr
      fun g => hinv g (preimage_actionQuotientπ_eq a (quotientImage a V) g)
    refine ⟨u, ?_⟩
    rw [restrictPullback, hu]
    exact hres _

end CategoryTheory
