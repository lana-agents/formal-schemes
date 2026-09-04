import FormalSchemes.ActionQuotientCarrier
import FormalSchemes.OpenImmersionIsoOfRangeEq

set_option linter.style.header false

/-!
# Restricting an action quotient to an open of the quotient

Let `a : G →* Aut X` act on a locally ringed space, let `π : X ⟶ Q` exhibit `Q` as the quotient
(`CategoryTheory.IsActionQuotient`), and let `V` be an open of `Q`. The open `π ⁻¹ V` is invariant,
so `a` restricts to it, and the question is whether `X|_{π ⁻¹ V} ⟶ Q|_V` is again an action
quotient. Three deliveries on the node-chart row named that statement as the one thing missing from
the invariant-sections route to a chart on `T_inv/⟨σ⟩`, and nothing on this tree produces an
`CategoryTheory.IsActionQuotient` by restriction.

This file supplies the restricted action, the restricted projection, and the answer **on underlying
topological spaces**. The answer in `AlgebraicGeometry.LocallyRingedSpace` itself is *not* proved
here; the gap is stated precisely below rather than left for a reader to discover.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.restrictOpensHom`: a morphism `f : X ⟶ Y` restricted to
  opens `U ⊆ X` and `V ⊆ Y` with `f U ⊆ V`, together with its factorisation, functoriality and
  identity laws. Everything else in the file is built from it.
* `AlgebraicGeometry.LocallyRingedSpace.IsInvariantOpen` and
  `AlgebraicGeometry.LocallyRingedSpace.restrictAction`: **the restricted action**, as a
  `G →* Aut (X.restrict U.isOpenEmbedding)` for an invariant open `U`. `G` is only a monoid.
* `AlgebraicGeometry.LocallyRingedSpace.isInvariantOpen_preimage`: `π ⁻¹ V` is invariant, from
  invariance of `π` alone.
* `AlgebraicGeometry.LocallyRingedSpace.restrictπ` and
  `AlgebraicGeometry.LocallyRingedSpace.isActionInvariant_restrictπ`: **the restricted projection**
  and its invariance — the first of the four obligations of the target statement.
* `AlgebraicGeometry.LocallyRingedSpace.base_isQuotientMap_restrictπ`,
  `AlgebraicGeometry.LocallyRingedSpace.base_surjective_restrictπ` and
  `AlgebraicGeometry.LocallyRingedSpace.base_eq_iff_restrictπ`: the underlying space of `Q|_V` is
  the orbit space of `π ⁻¹ V` — quotient topology, and points are orbits.
* `AlgebraicGeometry.LocallyRingedSpace.isActionQuotient_forgetToTop_restrictπ`: **the target
  statement after `AlgebraicGeometry.LocallyRingedSpace.forgetToTop`.** The restricted projection
  is an action quotient in `TopCat`.

## What is *not* proved here

**The statement in `AlgebraicGeometry.LocallyRingedSpace`**, which is what the row asks for. Of its
four obligations, `CategoryTheory.IsActionQuotient.isInvariant` is proved
(`AlgebraicGeometry.LocallyRingedSpace.isActionInvariant_restrictπ`) and the other three are not.
What separates them is the structure sheaf and nothing else, and the split is sharp:

* the *base map* of the descent of an invariant `f : X|_{π ⁻¹ V} ⟶ Z` exists and is
  `AlgebraicGeometry.LocallyRingedSpace.descRestrictπ`;
* what is missing is the map of sheaves `Z.presheaf ⟶ _ * (Q|_V).presheaf` and its naturality,
  plus `IsLocalHom` on stalks. The last of these is not extra work once the first two are done: if
  a composite of stalk maps is local and the second factor is local, so is the first, and the
  composite here is `f`'s stalk map, which is local because `f` is a morphism of *locally* ringed
  spaces.

The sheaf half is where the tree's existing invariant-sections description of a quotient's
structure sheaf has to be brought in — `CategoryTheory.exists_actionQuotientπ_c_app_eq_iff_forall`
(`FormalSchemes.ActionQuotientInvariantSections`) and
`AlgebraicGeometry.LocallyRingedSpace.injective_coequalizer_π_c_app`
(`FormalSchemes.ActionQuotientSections`), reached from a general
`CategoryTheory.IsActionQuotient` through
`CategoryTheory.IsActionQuotient.isoActionQuotient`. Restricting to `V` does not change sections
over sub-opens of `V`, which is why those two are expected to transfer; **that expectation is not
discharged anywhere here.**

**Anything about the node chart, its outstanding hypothesis, or the Tate curve.** This file is at
`AlgebraicGeometry.LocallyRingedSpace` level and mentions no ring, ideal or spectrum. What lands
does not produce a chart at the node locus and settles nothing on the node-chart row; it is
infrastructure for the invariant-sections route, and that route still needs the sheaf half above.

**Any weakening of `AlgebraicGeometry.FormalScheme.LocallyFG` anywhere.** See the implementation
notes for the measurement.

## Implementation notes

**`AlgebraicGeometry.FormalScheme.LocallyFG` has no bearing on any statement in this file, and the
proofs measure that rather than assert it**: no declaration here mentions
`AlgebraicGeometry.FormalScheme` at all, and neither of the file's two imports,
`FormalSchemes.ActionQuotientCarrier` and `FormalSchemes.OpenImmersionIsoOfRangeEq`, reaches
`FormalSchemes.OpenFormalSubscheme` — transitively, not only directly: the file's own import
closure is 72 project modules and `FormalSchemes.OpenFormalSubscheme` is not one of them. This
does **not** contradict `FormalSchemes.ActionQuotientFormalScheme`'s "not removable" paragraph,
which is about a different problem: producing an *affine chart* inside a separating open, through
`AlgebraicGeometry.FormalScheme.restrictOpen` and the local criterion for being a formal scheme.
Restricting a quotient is not that problem, and the hypothesis does not follow the construction
into it. Whether the missing sheaf half also avoids it is untested, because that half is unwritten.

`G` is a monoid throughout the restriction constructions, matching
`CategoryTheory.IsActionQuotient`; the group and smallness hypotheses appear only from
`AlgebraicGeometry.LocallyRingedSpace.base_isQuotientMap_of_isActionQuotient` onwards, where they
are `FormalSchemes.ActionQuotientCarrier`'s.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory Topology TopologicalSpace

universe v u

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X Y Z : LocallyRingedSpace.{u}}

/-- **A morphism restricted to a pair of opens.** For `f : X ⟶ Y`, an open `U` of `X` and an open
`V` of `Y` with `f U ⊆ V`, the morphism `X|_U ⟶ Y|_V` over `f`, built by the universal property of
the open immersion `Y|_V ⟶ Y` (`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift`).

The range side-condition that `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift` wants is
exactly `f U ⊆ V` once both ranges are read off with
`AlgebraicGeometry.LocallyRingedSpace.range_ofRestrict`.

`AlgebraicGeometry.LocallyRingedSpace.restrictLE` (`FormalSchemes.ThickeningChartSpfHom`) is the
case `f = 𝟙 Y`, `X = Y`. It is **not** rerouted through this construction: the two modules are
incomparable in the import order — neither is in the other's import closure — so removing the
overlap means rehoming one of them, which is a dedup question and not this file's. -/
def restrictOpensHom (f : X ⟶ Y) (U : Opens X.toTopCat) (V : Opens Y.toTopCat)
    (h : f.base '' (U : Set X.toTopCat) ⊆ (V : Set Y.toTopCat)) :
    X.restrict U.isOpenEmbedding ⟶ Y.restrict V.isOpenEmbedding :=
  IsOpenImmersion.lift (Y.ofRestrict V.isOpenEmbedding)
    (X.ofRestrict U.isOpenEmbedding ≫ f) (by
      rw [comp_base, TopCat.coe_comp, Set.range_comp, range_ofRestrict, range_ofRestrict]
      exact h)

/-- **The restricted morphism lies over `f`**, which is the only property of it that anything here
uses; every other statement in this file is proved by composing with `ofRestrict` and cancelling
the monomorphism. -/
@[reassoc (attr := simp)]
theorem restrictOpensHom_comp_ofRestrict (f : X ⟶ Y) (U : Opens X.toTopCat)
    (V : Opens Y.toTopCat) (h : f.base '' (U : Set X.toTopCat) ⊆ (V : Set Y.toTopCat)) :
    restrictOpensHom f U V h ≫ Y.ofRestrict V.isOpenEmbedding
      = X.ofRestrict U.isOpenEmbedding ≫ f :=
  IsOpenImmersion.lift_fac _ _ _

/-- The same, read on a point: the restricted morphism moves a point of `U` the way `f` does. -/
theorem restrictOpensHom_base_apply (f : X ⟶ Y) (U : Opens X.toTopCat) (V : Opens Y.toTopCat)
    (h : f.base '' (U : Set X.toTopCat) ⊆ (V : Set Y.toTopCat))
    (x : (X.restrict U.isOpenEmbedding).toTopCat) :
    (Y.ofRestrict V.isOpenEmbedding).base ((restrictOpensHom f U V h).base x)
      = f.base ((X.ofRestrict U.isOpenEmbedding).base x) :=
  congrArg (fun t : X.restrict U.isOpenEmbedding ⟶ Y => (ConcreteCategory.hom t.base) x)
    (restrictOpensHom_comp_ofRestrict f U V h)

/-- **Two morphisms into a restriction agreeing over the ambient space are equal**, because an open
immersion of locally ringed spaces is a monomorphism. -/
theorem hom_ext_of_comp_ofRestrict {W : LocallyRingedSpace.{u}} (V : Opens Y.toTopCat)
    {m₁ m₂ : W ⟶ Y.restrict V.isOpenEmbedding}
    (h : m₁ ≫ Y.ofRestrict V.isOpenEmbedding = m₂ ≫ Y.ofRestrict V.isOpenEmbedding) :
    m₁ = m₂ :=
  (cancel_mono _).mp h

/-- Restricting the identity gives the identity. -/
theorem restrictOpensHom_id (U : Opens X.toTopCat) :
    restrictOpensHom (𝟙 X) U U (by simp) = 𝟙 (X.restrict U.isOpenEmbedding) := by
  refine hom_ext_of_comp_ofRestrict U ?_
  simp

/-- **Restriction is functorial in the morphism.** With
`AlgebraicGeometry.LocallyRingedSpace.restrictOpensHom_id` this is what makes
`AlgebraicGeometry.LocallyRingedSpace.restrictAction` a monoid homomorphism. -/
theorem restrictOpensHom_comp (f : X ⟶ Y) (g : Y ⟶ Z) (U : Opens X.toTopCat)
    (V : Opens Y.toTopCat) (W : Opens Z.toTopCat)
    (hf : f.base '' (U : Set X.toTopCat) ⊆ (V : Set Y.toTopCat))
    (hg : g.base '' (V : Set Y.toTopCat) ⊆ (W : Set Z.toTopCat)) :
    restrictOpensHom (f ≫ g) U W (by
      rw [comp_base, TopCat.coe_comp, Set.image_comp]
      exact (Set.image_mono hf).trans hg)
      = restrictOpensHom f U V hf ≫ restrictOpensHom g V W hg := by
  refine hom_ext_of_comp_ofRestrict W ?_
  rw [restrictOpensHom_comp_ofRestrict, Category.assoc, restrictOpensHom_comp_ofRestrict,
    restrictOpensHom_comp_ofRestrict_assoc]

section Action

variable {G : Type v} [Monoid G]

/-- **An open is invariant under an action** when each `a g` pulls it back to itself. The preimage
form is the one `TopologicalSpace.Opens.map` uses, and it is the same condition as
`AlgebraicGeometry.LocallyRingedSpace.translate a U g = U` for every `g`
(`FormalSchemes.ActionTranslates`), which is stated only for a group.

Stating it once, rather than carrying a range hypothesis on each `a g` separately, is what keeps
`AlgebraicGeometry.LocallyRingedSpace.restrictAction`'s two monoid laws readable. -/
def IsInvariantOpen (a : G →* Aut X) (U : Opens X.toTopCat) : Prop :=
  ∀ g : G, (Opens.map (a g).hom.base).obj U = U

/-- An invariant open is carried into itself by `a g`. -/
theorem IsInvariantOpen.image_hom_subset {a : G →* Aut X} {U : Opens X.toTopCat}
    (hU : IsInvariantOpen a U) (g : G) :
    (a g).hom.base '' (U : Set X.toTopCat) ⊆ (U : Set X.toTopCat) := by
  rintro _ ⟨x, hx, rfl⟩
  have h : x ∈ (Opens.map (a g).hom.base).obj U := by rw [hU g]; exact hx
  exact h

/-- An invariant open is carried into itself by the *inverse* of `a g` as well, which is what makes
the restriction of `a g` an automorphism rather than merely an endomorphism. Only the pointwise
inverse law `AlgebraicGeometry.LocallyRingedSpace.iso_inv_base_hom_base_apply` is needed, so no
group hypothesis on `G` appears. -/
theorem IsInvariantOpen.image_inv_subset {a : G →* Aut X} {U : Opens X.toTopCat}
    (hU : IsInvariantOpen a U) (g : G) :
    (a g).inv.base '' (U : Set X.toTopCat) ⊆ (U : Set X.toTopCat) := by
  rintro _ ⟨x, hx, rfl⟩
  have h : (a g).inv.base x ∈ (Opens.map (a g).hom.base).obj U := by
    change (a g).hom.base ((a g).inv.base x) ∈ U
    rw [iso_inv_base_hom_base_apply (a g : X ≅ X)]
    exact hx
  rw [hU g] at h
  exact h

/-- **`a g` restricted to an invariant open.** Both directions restrict, by
`AlgebraicGeometry.LocallyRingedSpace.IsInvariantOpen.image_hom_subset` and
`AlgebraicGeometry.LocallyRingedSpace.IsInvariantOpen.image_inv_subset`, and the two round trips
are the functoriality of `AlgebraicGeometry.LocallyRingedSpace.restrictOpensHom`. -/
def restrictAut (a : G →* Aut X) (U : Opens X.toTopCat)
    (hU : IsInvariantOpen a U) (g : G) : Aut (X.restrict U.isOpenEmbedding) where
  hom := restrictOpensHom (a g).hom U U (hU.image_hom_subset g)
  inv := restrictOpensHom (a g).inv U U (hU.image_inv_subset g)
  hom_inv_id := by
    rw [← restrictOpensHom_comp]
    simp [restrictOpensHom_id]
  inv_hom_id := by
    rw [← restrictOpensHom_comp]
    simp [restrictOpensHom_id]

/-- The underlying morphism of the restricted automorphism. -/
@[simp]
theorem restrictAut_hom (a : G →* Aut X) (U : Opens X.toTopCat) (hU : IsInvariantOpen a U)
    (g : G) : (restrictAut a U hU g).hom
      = restrictOpensHom (a g).hom U U (hU.image_hom_subset g) := rfl

/-- **The restricted action.** For an open invariant under `a`, the action of the same `G` on the
open subspace. This is the first of the two pieces the restriction question needs; the second is
the universal property, on which see this file's module docstring.

`G` is only a monoid: the inverse of `a g` is supplied by `Aut`, not by `G`. -/
def restrictAction (a : G →* Aut X) (U : Opens X.toTopCat)
    (hU : IsInvariantOpen a U) : G →* Aut (X.restrict U.isOpenEmbedding) where
  toFun g := restrictAut a U hU g
  map_one' := by
    refine Iso.ext (hom_ext_of_comp_ofRestrict U ?_)
    have h1 : (1 : Aut X).hom = 𝟙 X := rfl
    have h1' : (1 : Aut (X.restrict U.isOpenEmbedding)).hom = 𝟙 _ := rfl
    rw [restrictAut_hom, restrictOpensHom_comp_ofRestrict, map_one, h1, h1',
      Category.comp_id, Category.id_comp]
  map_mul' g k := by
    refine Iso.ext (hom_ext_of_comp_ofRestrict U ?_)
    have hmul : (restrictAut a U hU g * restrictAut a U hU k).hom
        = (restrictAut a U hU k).hom ≫ (restrictAut a U hU g).hom := rfl
    have hmul' : (a g * a k).hom = (a k).hom ≫ (a g).hom := rfl
    rw [restrictAut_hom, restrictOpensHom_comp_ofRestrict, map_mul, hmul, hmul',
      restrictAut_hom, restrictAut_hom, Category.assoc, restrictOpensHom_comp_ofRestrict,
      restrictOpensHom_comp_ofRestrict_assoc]

/-- The underlying morphism of the restricted action at `g`. -/
@[simp]
theorem restrictAction_hom (a : G →* Aut X) (U : Opens X.toTopCat) (hU : IsInvariantOpen a U)
    (g : G) : ((restrictAction a U hU) g).hom
      = restrictOpensHom (a g).hom U U (hU.image_hom_subset g) := rfl

end Action

section Quotient

variable {G : Type v} [Monoid G] {Q : LocallyRingedSpace.{u}} {a : G →* Aut X} {π : X ⟶ Q}

/-- **The preimage of an open of the quotient is invariant.** This needs nothing but invariance of
`π` itself: `(a g).hom ≫ π = π` says the two preimages agree, on the nose. In particular it holds
for any invariant morphism, not only for a quotient projection. -/
theorem isInvariantOpen_preimage (hπ : IsActionInvariant a π) (V : Opens Q.toTopCat) :
    IsInvariantOpen a ((Opens.map π.base).obj V) := by
  intro g
  rw [← Opens.map_comp_obj, ← comp_base, hπ g]

/-- **The projection restricted over an open of the quotient**, `X|_{π ⁻¹ V} ⟶ Q|_V`. The
side-condition is that `π` carries `π ⁻¹ V` into `V`, which is `Set.image_preimage_subset`. -/
def restrictπ (π : X ⟶ Q) (V : Opens Q.toTopCat) :
    X.restrict ((Opens.map π.base).obj V).isOpenEmbedding ⟶ Q.restrict V.isOpenEmbedding :=
  restrictOpensHom π ((Opens.map π.base).obj V) V (by rintro _ ⟨x, hx, rfl⟩; exact hx)

/-- **The restricted projection is invariant under the restricted action.** This is the first field
of the `CategoryTheory.IsActionQuotient` the row asks for, and the only one of the four that is
formal: compose with the monomorphism `Q|_V ⟶ Q` and it becomes invariance of `π`. -/
theorem isActionInvariant_restrictπ (hπ : IsActionInvariant a π) (V : Opens Q.toTopCat) :
    IsActionInvariant (restrictAction a _ (isInvariantOpen_preimage hπ V)) (restrictπ π V) := by
  intro g
  refine hom_ext_of_comp_ofRestrict V ?_
  rw [Category.assoc, restrictπ, restrictOpensHom_comp_ofRestrict, restrictAction_hom,
    restrictOpensHom_comp_ofRestrict_assoc, hπ g]

/-- The restricted projection moves a point of `π ⁻¹ V` the way `π` does. -/
theorem restrictπ_base_apply (π : X ⟶ Q) (V : Opens Q.toTopCat)
    (x : (X.restrict ((Opens.map π.base).obj V).isOpenEmbedding).toTopCat) :
    (Q.ofRestrict V.isOpenEmbedding).base ((restrictπ π V).base x)
      = π.base ((X.ofRestrict ((Opens.map π.base).obj V).isOpenEmbedding).base x) :=
  restrictOpensHom_base_apply π _ V _ x

end Quotient

section Topology

variable {G : Type v} [Group G] [Small.{u} G] {Q : LocallyRingedSpace.{u}}
  {a : G →* Aut X} {π : X ⟶ Q}

/-- **The restricted projection is a topological quotient map.** Its base map is
`Set.restrictPreimage` of `π`'s, and a quotient map restricted to the preimage of an *open* set is
again one (`Topology.IsQuotientMap.restrictPreimage_isOpen`), applied to
`AlgebraicGeometry.LocallyRingedSpace.base_isQuotientMap_of_isActionQuotient`.

Openness of `V` is doing real work here: the same statement for an arbitrary subset of `Q` is
false, and this is the only place in the file where `V` being an open rather than a subset is
used for anything but typing. -/
theorem base_isQuotientMap_restrictπ (h : IsActionQuotient a π) (V : Opens Q.toTopCat) :
    Topology.IsQuotientMap ⇑(ConcreteCategory.hom (restrictπ π V).base) := by
  have hq := (base_isQuotientMap_of_isActionQuotient h).restrictPreimage_isOpen V.isOpen
  have heq : ⇑(ConcreteCategory.hom (restrictπ π V).base)
      = Set.restrictPreimage (V : Set Q.toTopCat) ⇑(ConcreteCategory.hom π.base) := by
    funext x
    exact Subtype.ext (restrictπ_base_apply π V x)
  rw [heq]
  exact hq

/-- The restricted projection is surjective on points. -/
theorem base_surjective_restrictπ (h : IsActionQuotient a π) (V : Opens Q.toTopCat) :
    Function.Surjective ⇑(ConcreteCategory.hom (restrictπ π V).base) :=
  (base_isQuotientMap_restrictπ h V).surjective

/-- **The points of `Q|_V` are the orbits of the restricted action.** Two points of `π ⁻¹ V` have
the same image exactly when some `a g` carries one to the other — and the `a g` that does so
already preserves `π ⁻¹ V`, so no point leaves the open. This is
`AlgebraicGeometry.LocallyRingedSpace.base_eq_iff_of_isActionQuotient` transported across the two
inclusions. -/
theorem base_eq_iff_restrictπ (h : IsActionQuotient a π) (V : Opens Q.toTopCat)
    (x y : (X.restrict ((Opens.map π.base).obj V).isOpenEmbedding).toTopCat) :
    (restrictπ π V).base x = (restrictπ π V).base y ↔
      ∃ g : G, ((restrictAction a _ (isInvariantOpen_preimage h.isInvariant V)) g).hom.base x
        = y := by
  constructor
  · intro hxy
    have hbase : π.base ((X.ofRestrict _).base x) = π.base ((X.ofRestrict _).base y) := by
      rw [← restrictπ_base_apply π V x, ← restrictπ_base_apply π V y, hxy]
    obtain ⟨g, hg⟩ := (base_eq_iff_of_isActionQuotient h _ _).mp hbase
    have hb := restrictOpensHom_base_apply (a g).hom ((Opens.map π.base).obj V)
      ((Opens.map π.base).obj V)
      ((isInvariantOpen_preimage h.isInvariant V).image_hom_subset g) x
    exact ⟨g, ((Opens.map π.base).obj V).isOpenEmbedding.injective (hb.trans hg)⟩
  · rintro ⟨g, rfl⟩
    exact (congrArg (fun t : _ ⟶ Q.restrict V.isOpenEmbedding =>
      (ConcreteCategory.hom t.base) x) (isActionInvariant_restrictπ h.isInvariant V g)).symm

/-- **An invariant continuous map out of `π ⁻¹ V` is constant on the fibres of the restricted
projection.** By `AlgebraicGeometry.LocallyRingedSpace.base_eq_iff_restrictπ` those fibres are the
orbits, and invariance is exactly constancy on orbits. -/
theorem factorsThrough_of_isActionInvariant (h : IsActionQuotient a π) (V : Opens Q.toTopCat)
    {W : TopCat.{u}} (f : forgetToTop.obj (X.restrict ((Opens.map π.base).obj V).isOpenEmbedding)
      ⟶ W)
    (hf : IsActionInvariant (forgetToTop.mapAction
      (restrictAction a _ (isInvariantOpen_preimage h.isInvariant V))) f) :
    Function.FactorsThrough ⇑(TopCat.Hom.hom f)
      ⇑(ConcreteCategory.hom (restrictπ π V).base) := by
  intro x y hxy
  obtain ⟨g, rfl⟩ := (base_eq_iff_restrictπ h V x y).mp hxy
  exact (congrArg (fun t : _ ⟶ W => (ConcreteCategory.hom t) x) (hf g)).symm

/-- **The descent of an invariant continuous map along the restricted projection**,
`Topology.IsQuotientMap.lift` applied to
`AlgebraicGeometry.LocallyRingedSpace.base_isQuotientMap_restrictπ`. -/
def descRestrictπ (h : IsActionQuotient a π) (V : Opens Q.toTopCat)
    {W : TopCat.{u}} (f : forgetToTop.obj (X.restrict ((Opens.map π.base).obj V).isOpenEmbedding)
      ⟶ W)
    (hf : IsActionInvariant (forgetToTop.mapAction
      (restrictAction a _ (isInvariantOpen_preimage h.isInvariant V))) f) :
    forgetToTop.obj (Q.restrict V.isOpenEmbedding) ⟶ W :=
  TopCat.ofHom ((base_isQuotientMap_restrictπ h V).lift (TopCat.Hom.hom f)
    (factorsThrough_of_isActionInvariant h V f hf))

/-- The descent factors the map it descends. -/
@[simp]
theorem descRestrictπ_apply (h : IsActionQuotient a π) (V : Opens Q.toTopCat)
    {W : TopCat.{u}} (f : forgetToTop.obj (X.restrict ((Opens.map π.base).obj V).isOpenEmbedding)
      ⟶ W)
    (hf : IsActionInvariant (forgetToTop.mapAction
      (restrictAction a _ (isInvariantOpen_preimage h.isInvariant V))) f)
    (x : (X.restrict ((Opens.map π.base).obj V).isOpenEmbedding).toTopCat) :
    (ConcreteCategory.hom (descRestrictπ h V f hf))
        ((ConcreteCategory.hom (restrictπ π V).base) x)
      = (ConcreteCategory.hom f) x := by
  have hlift := (base_isQuotientMap_restrictπ h V).lift_comp (TopCat.Hom.hom f)
    (factorsThrough_of_isActionInvariant h V f hf)
  exact DFunLike.congr_fun hlift x

/-- **The restricted projection is an action quotient of topological spaces.** This is the row's
statement after `AlgebraicGeometry.LocallyRingedSpace.forgetToTop`: `Q|_V` carries the quotient
topology of `π ⁻¹ V` by the restricted action, and continuous invariant maps out of `π ⁻¹ V`
descend uniquely.

Existence is `AlgebraicGeometry.LocallyRingedSpace.descRestrictπ`, factorisation is
`AlgebraicGeometry.LocallyRingedSpace.descRestrictπ_apply`, and uniqueness is surjectivity of the
base map. **The corresponding statement in `AlgebraicGeometry.LocallyRingedSpace` itself is not
proved here** — see this file's module docstring for what separates the two. -/
def isActionQuotient_forgetToTop_restrictπ (h : IsActionQuotient a π)
    (V : Opens Q.toTopCat) :
    IsActionQuotient (forgetToTop.mapAction
        (restrictAction a _ (isInvariantOpen_preimage h.isInvariant V)))
      (forgetToTop.map (restrictπ π V)) where
  isInvariant := (isActionInvariant_restrictπ h.isInvariant V).map forgetToTop
  desc f hf := descRestrictπ h V f hf
  fac f hf := by
    ext x
    exact descRestrictπ_apply h V f hf x
  uniq f hf m hm := by
    ext v
    obtain ⟨x, rfl⟩ := base_surjective_restrictπ h V v
    rw [descRestrictπ_apply h V f hf x]
    exact congrArg (fun t : _ ⟶ _ => (ConcreteCategory.hom t) x) hm

end Topology

end AlgebraicGeometry.LocallyRingedSpace
