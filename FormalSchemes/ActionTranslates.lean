import FormalSchemes.ActionDiscontinuous

set_option linter.style.header false

/-!
# The translates of a small open inside a separating open

`FormalSchemes.ActionDiscontinuous` shows that the projection `π` of an action quotient is an open
map and that it is injective on a separating open `U`. This file records the shape of the
*saturation* of an open `V ≤ U`, which is the piece of geometry the stalk lemma runs on:

> `π⁻¹(π '' V)` is the supremum of the translates `(a g)⁻¹ V`, and those translates are **pairwise
> disjoint**.

Both halves are stated for `Opens X` rather than for sets, because that is what the structure sheaf
is indexed by. The translate is written as the *preimage* `(Opens.map (a g).base).obj V` rather than
as the image `(a g) '' V`: the two agree (`preimage_action_base_eq_image`, `(a g)` being an
isomorphism), but only the preimage form is what `Opens.map` and the comparison maps `c.app` of a
morphism of presheafed spaces consume, so writing it that way removes a transport from every
downstream statement.

## Main definitions

* `AlgebraicGeometry.LocallyRingedSpace.imageOpen`: the image of an open under the projection of an
  action quotient, as an open of the quotient. It is open by
  `isOpenMap_base_of_isActionQuotient`, with no hypothesis on the action.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.translate`: the `g`-th translate `(a g)⁻¹ V` of an open.
* `AlgebraicGeometry.LocallyRingedSpace.preimage_imageOpen`: `π⁻¹(π '' V) = ⨆ g, (a g)⁻¹ V`, for
  an arbitrary action.
* `AlgebraicGeometry.LocallyRingedSpace.translate_translate`: translating twice multiplies the
  group elements.
* `AlgebraicGeometry.LocallyRingedSpace.disjoint_translate`: for `V ≤ U` with `U` separating, the
  translates `(a g)⁻¹ V` are pairwise disjoint.
* `AlgebraicGeometry.LocallyRingedSpace.bijOn_base_imageOpen`: `π.base` is a bijection from `V`
  onto `π '' V`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory Topology TopologicalSpace

universe v u

namespace AlgebraicGeometry

namespace LocallyRingedSpace

variable {G : Type v} [Group G] {X : LocallyRingedSpace.{u}} {a : G →* Aut X}

/-! ### The action on points -/

/-- The action is a left action on points: `a (g * h)` moves a point the way `a h` does, then
`a g`. This is `Aut`'s multiplication (`f * g = g ≫ f` on the underlying morphisms) read on
bases. -/
theorem action_mul_base_apply (g h : G) (x : X) :
    (a (g * h)).hom.base x = (a g).hom.base ((a h).hom.base x) := by
  rw [map_mul]
  rfl

/-- `a g⁻¹` undoes `a g` on points. -/
@[simp]
theorem action_inv_base_apply (g : G) (x : X) :
    (a g⁻¹).hom.base ((a g).hom.base x) = x := by
  rw [← action_mul_base_apply, inv_mul_cancel, action_one_base_apply]

/-- `a g` undoes `a g⁻¹` on points. -/
@[simp]
theorem action_base_inv_apply (g : G) (x : X) :
    (a g).hom.base ((a g⁻¹).hom.base x) = x := by
  rw [← action_mul_base_apply, mul_inv_cancel, action_one_base_apply]

/-- **The image of a set under `a g` is its preimage under `a g⁻¹`.** The two descriptions of a
translate agree because `a g` is an isomorphism; the preimage form is the one `Opens.map` uses. -/
theorem preimage_action_base_eq_image (g : G) (W : Set X) :
    (a g⁻¹).hom.base ⁻¹' W = (a g).hom.base '' W := by
  ext x
  refine ⟨fun hx => ⟨_, hx, action_base_inv_apply g x⟩, ?_⟩
  rintro ⟨y, hy, rfl⟩
  change (a g⁻¹).hom.base ((a g).hom.base y) ∈ W
  rw [action_inv_base_apply]
  exact hy

/-- Membership in a translate, read off `a g⁻¹`. -/
theorem mem_image_action_base_iff (g : G) (W : Set X) (x : X) :
    x ∈ (a g).hom.base '' W ↔ (a g⁻¹).hom.base x ∈ W := by
  rw [← preimage_action_base_eq_image]
  exact Iff.rfl

/-! ### The translates of an open -/

/-- **The `g`-th translate of an open**, written as the preimage under `a g`. It is the image under
`a g⁻¹` (`preimage_action_base_eq_image`), but the preimage form is what `Opens.map` and the
comparison maps `c.app` consume. The spelling `(a g).hom.toShHom.hom.base` is the one the sections
API of `FormalSchemes.ActionQuotientInvariantSections` uses, so the two match syntactically. -/
def translate (a : G →* Aut X) (V : Opens X.toTopCat) (g : G) : Opens X.toTopCat :=
  (Opens.map (a g).hom.toShHom.hom.base).obj V

/-- Membership in a translate is membership of the moved point, by definition. -/
theorem mem_translate {V : Opens X.toTopCat} {g : G} {x : X} :
    x ∈ translate a V g ↔ (a g).hom.base x ∈ V :=
  Iff.rfl

/-- The underlying set of a translate. -/
theorem coe_translate (V : Opens X.toTopCat) (g : G) :
    (translate a V g : Set X) = (a g).hom.base ⁻¹' (V : Set X) :=
  rfl

/-- The translate of an open by the identity is the open itself. -/
@[simp]
theorem translate_one (V : Opens X.toTopCat) : translate a V (1 : G) = V := by
  refine SetLike.ext fun x => ?_
  rw [mem_translate, action_one_base_apply]
  exact Iff.rfl

/-- **Translating twice multiplies the group elements.** Translating `translate a V g` by `a k`
gives `translate a V (g * k)`: the two `Opens.map`s compose into the map of `a (g * k)`, `Aut`'s
multiplication being `f * g = g ≫ f` on underlying morphisms. -/
theorem translate_translate (V : Opens X.toTopCat) (g k : G) :
    (Opens.map (a k).hom.toShHom.hom.base).obj (translate a V g) = translate a V (g * k) := by
  have hcomp : ((a (g * k)).hom).toShHom.hom.base
      = (a k).hom.toShHom.hom.base ≫ (a g).hom.toShHom.hom.base := by
    rw [map_mul]
    rfl
  change (Opens.map (a k).hom.toShHom.hom.base).obj ((Opens.map (a g).hom.toShHom.hom.base).obj V)
    = (Opens.map ((a (g * k)).hom).toShHom.hom.base).obj V
  rw [hcomp, Opens.map_comp_obj]

/-! ### Disjointness of the translates -/

/-- **The translates of an open contained in a separating open are pairwise disjoint.** A point in
`translate a V g ⊓ translate a V k` produces a point `y = (a k) x` of `U` whose image under
`a (g * k⁻¹)` is again in `U`, which `IsProperlyDiscontinuousOn` forbids unless `g = k`. -/
theorem disjoint_translate {U : Set X} (hU : IsProperlyDiscontinuousOn a U)
    {V : Opens X.toTopCat} (hVU : (V : Set X) ⊆ U) {g k : G} (hgk : g ≠ k) :
    Disjoint (translate a V g) (translate a V k) := by
  refine disjoint_iff_inf_le.mpr fun x hx => ?_
  obtain ⟨hxg, hxk⟩ := hx
  have hy : (a k).hom.base x ∈ U := hVU hxk
  have hgy : (a (g * k⁻¹)).hom.base ((a k).hom.base x) ∈ U := by
    rw [action_mul_base_apply, action_inv_base_apply]
    exact hVU hxg
  have hne : g * k⁻¹ ≠ 1 := fun hc => hgk (by rwa [mul_inv_eq_one] at hc)
  exact (Set.disjoint_left.mp (hU _ hne) (Set.mem_image_of_mem _ hy) hgy).elim

/-! ### The saturation of an open -/

variable [Small.{u} G] {Q : LocallyRingedSpace.{u}} {π : X ⟶ Q}

/-- **The image of an open under the projection of an action quotient, as an open.** The projection
is an open map for *any* action (`isOpenMap_base_of_isActionQuotient`), so no hypothesis beyond
`IsActionQuotient` is needed. -/
def imageOpen (h : IsActionQuotient a π) (V : Opens X.toTopCat) : Opens Q.toTopCat where
  carrier := (π.base : X → Q) '' (V : Set X)
  is_open' := isOpenMap_base_of_isActionQuotient h _ V.isOpen

/-- The underlying set of the image of an open. -/
@[simp]
theorem coe_imageOpen (h : IsActionQuotient a π) (V : Opens X.toTopCat) :
    (imageOpen h V : Set Q) = (π.base : X → Q) '' (V : Set X) :=
  rfl

/-- A point of `V` projects into the image of `V`. -/
theorem mem_imageOpen_self (h : IsActionQuotient a π) {V : Opens X.toTopCat} {x : X}
    (hx : x ∈ V) : π.base x ∈ imageOpen h V :=
  ⟨x, hx, rfl⟩

/-- **The saturation of an open is the supremum of its translates.** This is
`preimage_image_base_of_isActionQuotient` re-indexed by `g ↦ g⁻¹`, so that the pieces are written
as preimages. No hypothesis on the action. -/
theorem preimage_imageOpen (h : IsActionQuotient a π) (V : Opens X.toTopCat) :
    (Opens.map π.toShHom.hom.base).obj (imageOpen h V) = ⨆ g : G, translate a V g := by
  have hset : (π.base : X → Q) ⁻¹' ((π.base : X → Q) '' (V : Set X))
      = ⋃ g : G, (a g).hom.base '' (V : Set X) :=
    preimage_image_base_of_isActionQuotient h _
  refine SetLike.ext fun x => ?_
  have hx : x ∈ (Opens.map π.toShHom.hom.base).obj (imageOpen h V) ↔
      x ∈ ⋃ g : G, (a g).hom.base '' (V : Set X) := by
    rw [← hset]
    exact Iff.rfl
  rw [hx, Set.mem_iUnion]
  constructor
  · rintro ⟨g, hg⟩
    exact Opens.mem_iSup.mpr ⟨g⁻¹, (mem_image_action_base_iff g _ x).mp hg⟩
  · intro hxs
    obtain ⟨g, hg⟩ := Opens.mem_iSup.mp hxs
    refine ⟨g⁻¹, (mem_image_action_base_iff g⁻¹ _ x).mpr ?_⟩
    rw [inv_inv]
    exact mem_translate.mp hg

/-! ### The projection is a bijection from a separating open onto its image -/

/-- `π.base` is injective on a separating open, hence a bijection from an open `V ≤ U` onto its
image. -/
theorem bijOn_base_imageOpen (h : IsActionQuotient a π) {U : Set X}
    (hU : IsProperlyDiscontinuousOn a U) {V : Opens X.toTopCat} (hVU : (V : Set X) ⊆ U) :
    Set.BijOn (π.base : X → Q) (V : Set X) (imageOpen h V : Set Q) :=
  ⟨fun x hx => ⟨x, hx, rfl⟩,
    (injOn_base_of_isProperlyDiscontinuousOn h hU).mono hVU,
    fun _ hz => hz⟩

end LocallyRingedSpace

end AlgebraicGeometry
