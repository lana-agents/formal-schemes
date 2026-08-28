import FormalSchemes.ActionQuotientCarrier

set_option linter.style.header false

/-!
# Free, properly discontinuous actions, and the topology of their quotients

`FormalSchemes.ActionQuotientCarrier` computes the underlying space of a quotient of a locally
ringed space by a group action: the points are the orbits and the topology is the quotient
topology, with **no** hypothesis on the action. This file adds the hypothesis under which the
quotient can be expected to be a formal scheme again, and proves everything about it that lives on
the topological side.

## The hypothesis, and why it is this one

Issue 224 asks for the quotient by a *free, properly discontinuous* action. Neither notion had a
general form on this tree — what existed was two theorems about the patches of one specific glue
datum (`tateShift_properlyDiscontinuous`, `tateInvShift_properlyDiscontinuous`). Mathlib's
`ProperlyDiscontinuousSMul` is stated for an `SMul Γ T` on a topological space, so using it would
mean first transporting `a : G →* Aut X` to an `SMul G ↥X`.

The condition below is neither: it is the property the local-isomorphism argument actually consumes,
stated directly.

`IsProperlyDiscontinuousOn a U` says every nontrivial translate of `U` misses `U`; the action is
`IsFreeProperlyDiscontinuous` when every point has such an open neighbourhood. One condition
packages both halves — freeness is `isFreeProperlyDiscontinuous_free` below, and is immediate:
a `g` fixing a point of such a `U` would put `(a g) '' U` and `U` both around that point.

The reason to prefer it to a transported `ProperlyDiscontinuousSMul` is measured, not aesthetic: the
project's only instance is the Tate `q^{2ℤ}`-action, and its patch-wise theorem
`tateInvShift_properlyDiscontinuous` discharges this form **directly**, with the chain's own patches
as the neighbourhoods — see `tateInvPeriodSq_isFreeProperlyDiscontinuous`.

## What is proved here, and what is left

Everything topological about the quotient map near a separating neighbourhood:

* `π.base` is an open map, for *any* action (`isOpenMap_base_of_isActionQuotient`);
* it is injective on a separating open (`injOn_base_of_isProperlyDiscontinuousOn`);
* hence it restricts to an **open embedding** of that open into the quotient
  (`isOpenEmbedding_restrict_of_isProperlyDiscontinuousOn`).

That is the topological half of "the quotient projection is a local isomorphism". What is *not*
here is the other half: that the restriction is an open immersion of **locally ringed spaces**,
i.e. that the stalk maps of `π` are isomorphisms. By
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_stalk_iso` those two together are exactly
what is needed, and the second is a statement about the structure sheaf of a coequalizer, which
nothing on this tree or in Mathlib has for this diagram shape.

## Main definitions

* `AlgebraicGeometry.LocallyRingedSpace.IsProperlyDiscontinuousOn`
* `AlgebraicGeometry.LocallyRingedSpace.IsFreeProperlyDiscontinuous`

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.isOpenMap_base_of_isActionQuotient`
* `AlgebraicGeometry.LocallyRingedSpace.isOpenEmbedding_restrict_of_isProperlyDiscontinuousOn`
* `AlgebraicGeometry.tateInvPeriodSq_isFreeProperlyDiscontinuous`: the `q^{2ℤ}`-action on the
  inversion-glued Tate chain satisfies the hypothesis, so it is not vacuous.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe v u

namespace AlgebraicGeometry

namespace LocallyRingedSpace

variable {G : Type v} [Group G] {X : LocallyRingedSpace.{u}}

/-! ### The hypothesis -/

/-- **`U` separates the translates of the action `a`**: every nontrivial `a g` moves `U` off
itself. -/
def IsProperlyDiscontinuousOn (a : G →* Aut X) (U : Set X) : Prop :=
  ∀ g : G, g ≠ 1 → Disjoint ((a g).hom.base '' U) U

/-- **The action is free and properly discontinuous**: every point has an open neighbourhood
separating the translates. -/
def IsFreeProperlyDiscontinuous (a : G →* Aut X) : Prop :=
  ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsProperlyDiscontinuousOn a U

variable {a : G →* Aut X}

/-- **The condition implies freeness**, which is why one hypothesis suffices for both halves: a `g`
fixing a point of a separating open would put that point in both `(a g) '' U` and `U`. -/
theorem eq_one_of_isProperlyDiscontinuousOn {U : Set X} (hU : IsProperlyDiscontinuousOn a U)
    {x : X} (hx : x ∈ U) {g : G} (hgx : (a g).hom.base x = x) : g = 1 := by
  by_contra hg
  exact Set.disjoint_left.mp (hU g hg) (hgx ▸ Set.mem_image_of_mem _ hx) hx

/-- Each `a g` is a homeomorphism on underlying spaces, being an isomorphism of locally ringed
spaces. -/
def autHomeo (a : G →* Aut X) (g : G) : X.toTopCat ≃ₜ X.toTopCat :=
  TopCat.homeoOfIso (forgetToTop.mapIso (a g))

theorem autHomeo_apply (g : G) (x : X) : autHomeo a g x = (a g).hom.base x :=
  rfl

theorem isOpenMap_action_base (g : G) : IsOpenMap ((a g).hom.base : X → X) :=
  (autHomeo a g).isOpenMap

theorem action_one_base_apply (a : G →* Aut X) (x : X) : (a (1 : G)).hom.base x = x := by
  rw [map_one]; rfl

/-! ### The quotient map is open -/

variable [Small.{u} G] {Q : LocallyRingedSpace.{u}} {π : X ⟶ Q}

/-- **The saturation of an open set is the union of its translates.** -/
theorem preimage_image_base_of_isActionQuotient (h : IsActionQuotient a π) (W : Set X) :
    π.base ⁻¹' (π.base '' W) = ⋃ g : G, (a g).hom.base '' W := by
  ext y
  constructor
  · rintro ⟨w, hw, hyw⟩
    obtain ⟨g, hg⟩ := (base_eq_iff_of_isActionQuotient h w y).mp hyw
    exact Set.mem_iUnion.mpr ⟨g, ⟨w, hw, hg⟩⟩
  · rintro hy
    obtain ⟨g, w, hw, rfl⟩ := Set.mem_iUnion.mp hy
    exact ⟨w, hw, (base_eq_iff_of_isActionQuotient h w _).mpr ⟨g, rfl⟩⟩

/-- **The projection of an action quotient is an open map.** No hypothesis on the action: the
saturation of an open set is a union of translates, each open because every `a g` is an
isomorphism, and the quotient topology then makes the image open. -/
theorem isOpenMap_base_of_isActionQuotient (h : IsActionQuotient a π) :
    IsOpenMap (π.base : X → Q) := fun W hW => by
  refine (base_isQuotientMap_of_isActionQuotient h).isOpen_preimage.mp ?_
  rw [preimage_image_base_of_isActionQuotient h W]
  exact isOpen_iUnion fun g => isOpenMap_action_base g W hW

/-! ### The projection is injective on a separating open -/

/-- **The projection is injective on a separating open.** Two of its points with the same image
differ by some `a g`, and only `g = 1` can carry a point of `U` back into `U`. -/
theorem injOn_base_of_isProperlyDiscontinuousOn (h : IsActionQuotient a π) {U : Set X}
    (hU : IsProperlyDiscontinuousOn a U) : Set.InjOn (π.base : X → Q) U := by
  intro x hx y hy hxy
  obtain ⟨g, hg⟩ := (base_eq_iff_of_isActionQuotient h x y).mp hxy
  by_cases hg1 : g = 1
  · rw [hg1] at hg
    exact (action_one_base_apply a x).symm.trans hg
  · exact ((Set.disjoint_left.mp (hU g hg1) (hg ▸ Set.mem_image_of_mem _ hx)) hy).elim

/-- **The projection restricts to an open embedding of a separating open.** This is the topological
half of "`π` is a local isomorphism"; the other half is that the restriction is an open immersion
of locally ringed spaces, which is a statement about the structure sheaf. -/
theorem isOpenEmbedding_restrict_of_isProperlyDiscontinuousOn (h : IsActionQuotient a π)
    {U : Set X} (hUopen : IsOpen U) (hU : IsProperlyDiscontinuousOn a U) :
    IsOpenEmbedding (U.restrict (π.base : X → Q)) := by
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap
    (π.base.hom.continuous.comp continuous_subtype_val)
    ((Set.injOn_iff_injective).mp (injOn_base_of_isProperlyDiscontinuousOn h hU))
    fun W hW => ?_
  obtain ⟨W', hW', rfl⟩ := isOpen_induced_iff.mp hW
  have : U.restrict (π.base : X → Q) '' (Subtype.val ⁻¹' W') = π.base '' (W' ∩ U) := by
    ext z
    constructor
    · rintro ⟨⟨x, hx⟩, hxW, rfl⟩
      exact ⟨x, ⟨hxW, hx⟩, rfl⟩
    · rintro ⟨x, ⟨hxW, hx⟩, rfl⟩
      exact ⟨⟨x, hx⟩, hxW, rfl⟩
  rw [this]
  exact isOpenMap_base_of_isActionQuotient h _ (hW'.inter hUopen)

end LocallyRingedSpace

/-! ### The hypothesis is satisfiable: the Tate `q^{2ℤ}`-action -/

section Tate

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)

/-- **The `q^{2ℤ}`-action on the inversion-glued Tate chain is free and properly discontinuous.**
The separating neighbourhood of a point is the patch `U_n` containing it: the chain's patches are
jointly surjective and open, and `tateInvShift_properlyDiscontinuous` says `U_n` is disjoint from
`σᵏ(U_n)` for every `k ∉ {−1, 0, 1}` — which covers every nontrivial element of the *square* action,
whose exponents are the even integers.

This is why `LocallyRingedSpace.IsFreeProperlyDiscontinuous` is stated in the neighbourhood form
rather than as a transported `ProperlyDiscontinuousSMul`: the project's only instance discharges the
neighbourhood form with the patches it already has, and nothing has to be rebuilt. -/
theorem tateInvPeriodSq_isFreeProperlyDiscontinuous :
    LocallyRingedSpace.IsFreeProperlyDiscontinuous (tateInvPeriodSqAction R I q hq hI) := by
  intro x
  obtain ⟨n, y, rfl⟩ := (tateChainInvFormalGlueData R I q hq hI).ι_jointly_surjective x
  refine ⟨Set.range ((tateChainInvFormalGlueData R I q hq hI).ι n).base,
    ((tateChainInvFormalGlueData R I q hq hI).ι_isOpenImmersion n).base_open.isOpen_range,
    ⟨y, rfl⟩, fun g hg => ?_⟩
  have hk0 : 2 * g.toAdd ≠ 0 := by
    simpa using fun h => hg (by simpa using h)
  rw [tateInvPeriodSqAction_apply, Set.disjoint_left]
  have key := tateInvShift_properlyDiscontinuous R I q hq hI n (2 * g.toAdd) hk0
    (by omega) (by omega)
  rintro z ⟨w, ⟨y', rfl⟩, rfl⟩
  exact Set.disjoint_right.mp key ⟨y', rfl⟩

end Tate

end AlgebraicGeometry
