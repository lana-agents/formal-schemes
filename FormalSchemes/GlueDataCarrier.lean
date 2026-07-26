import Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing
import FormalSchemes.EmptyLocallyRingedSpace

set_option linter.style.header false

/-!
# The underlying space of a glued locally ringed space, and disjointness of the pieces

For a `LocallyRingedSpace.GlueData` `D`, the underlying topological space of the glued locally
ringed space `D.glued` is the topological gluing of the underlying spaces of the pieces
(`AlgebraicGeometry.LocallyRingedSpace.GlueData.isoCarrier`). This is the locally-ringed-space
analogue of `AlgebraicGeometry.Scheme.GlueData.isoCarrier`, obtained by the same chain of forgetful
comparison isomorphisms but stopping one layer earlier (there is no `Scheme`/`LocallyRingedSpace`
layer to traverse).

The payoff recorded here is the **disjointness of the pieces**: if the overlap object `V(i, j)` has
empty carrier (the two pieces do not meet), then the ranges of the open immersions `ι i`, `ι j` into
the glued space are disjoint. This is the tool that, for a glue datum indexed by a poset in which
non-adjacent pieces do not overlap, shows the images of far-apart pieces are disjoint — the
input a properly-discontinuous group action / quotient construction consumes.

## Main results

* `LocallyRingedSpace.GlueData.isoCarrier`: `D.glued.carrier ≅` the topological gluing of the
  carriers of the pieces.
* `LocallyRingedSpace.GlueData.ι_isoCarrier_inv`: compatibility of `isoCarrier` with the inclusions.
* `LocallyRingedSpace.GlueData.range_ι_disjoint_of_isEmpty_V`: disjointness of the ranges of `ι i`,
  `ι j` when the overlap `V(i, j)` is empty.

## References

* `AlgebraicGeometry.Scheme.GlueData.isoCarrier` (Mathlib), the scheme analogue.
* `TopCat.GlueData.image_inter` (Mathlib), the topological input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.GlueData

variable (D : LocallyRingedSpace.GlueData.{u})

local notation "𝖣" => D.toGlueData

/-- The topological glue data underlying `D`, obtained by forgetting the ring structure. -/
abbrev topGlueData : TopCat.GlueData.{u} :=
  D.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toTopGlueData

-- Bridge the open-immersion `f_open` fields of the intermediate glue data down to instances (the
-- `abbrev` projections otherwise do not fire during instance search), mirroring the analogous
-- helper instances in `AlgebraicGeometry.Scheme.GlueData`.
instance sheafedSpace_f_open (i j : D.J) :
    SheafedSpace.IsOpenImmersion (D.toSheafedSpaceGlueData.toGlueData.f i j) :=
  D.toSheafedSpaceGlueData.f_open i j

instance presheafedSpace_f_open (i j : D.J) :
    PresheafedSpace.IsOpenImmersion
      (D.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toGlueData.f i j) :=
  D.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.f_open i j

/-- **The underlying topological space of the glued locally ringed space is the topological gluing
of the underlying spaces of the pieces.** The locally-ringed-space analogue of
`AlgebraicGeometry.Scheme.GlueData.isoCarrier`, one comparison layer shorter. -/
def isoCarrier : 𝖣.glued.carrier ≅ D.topGlueData.toGlueData.glued := by
  refine (PresheafedSpace.forget _).mapIso ?_ ≪≫
    CategoryTheory.GlueData.gluedIso _ (PresheafedSpace.forget.{_, _, u} _)
  refine SheafedSpace.forgetToPresheafedSpace.mapIso ?_ ≪≫
    SheafedSpace.GlueData.isoPresheafedSpace _
  exact D.isoSheafedSpace

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem ι_isoCarrier_inv (i : D.J) :
    D.topGlueData.toGlueData.ι i ≫ (D.isoCarrier).inv = (𝖣.ι i).base := by
  delta isoCarrier
  rw [Iso.trans_inv, GlueData.ι_gluedIso_inv_assoc, Functor.mapIso_inv, Iso.trans_inv,
    Functor.mapIso_inv, SheafedSpace.forgetToPresheafedSpace_map, PresheafedSpace.forget_map,
    PresheafedSpace.forget_map, ← PresheafedSpace.comp_base, ← Category.assoc,
    D.toSheafedSpaceGlueData.ι_isoPresheafedSpace_inv i]
  dsimp
  rw [← PresheafedSpace.comp_base, ← InducedCategory.comp_hom, D.ι_isoSheafedSpace_inv i]
  rfl

/-- **Pieces whose overlap object is empty have disjoint ranges in the glued space.** If the overlap
`V(i, j)` of a `LocallyRingedSpace.GlueData` has empty carrier, then the ranges of the inclusions
`ι i`, `ι j` into the glued space are disjoint. Combined with a glue datum in which non-adjacent
pieces have empty overlap, this shows the images of far-apart pieces are disjoint — the geometric
input a properly-discontinuous group action / quotient construction consumes. -/
theorem range_ι_disjoint_of_isEmpty_V {i j : D.J} (h : IsEmpty (𝖣.V (i, j))) :
    Disjoint (Set.range (𝖣.ι i).base) (Set.range (𝖣.ι j).base) := by
  haveI : IsEmpty (D.topGlueData.V (i, j)) := h
  -- Disjointness at the topological level, from `image_inter` and the empty overlap.
  have key : Disjoint (Set.range (D.topGlueData.ι i)) (Set.range (D.topGlueData.ι j)) := by
    rw [Set.disjoint_iff_inter_eq_empty, D.topGlueData.image_inter i j]
    exact Set.range_eq_empty _
  -- Transport a hypothetical common point through the homeomorphism `isoCarrier.hom`.
  rw [Set.disjoint_left]
  rintro x ⟨a, ha⟩ ⟨b, hb⟩
  -- `e.hom x` lies in both topological ranges, contradicting `key`.
  have hi : D.isoCarrier.hom x ∈ Set.range ⇑(D.topGlueData.ι i) := by
    refine ⟨a, ?_⟩
    have h1 := ConcreteCategory.congr_hom (D.ι_isoCarrier_inv i) a
    rw [ConcreteCategory.comp_apply] at h1
    calc D.topGlueData.ι i a
        = D.isoCarrier.hom (D.isoCarrier.inv (D.topGlueData.ι i a)) :=
          (Iso.inv_hom_id_apply _ _).symm
      _ = D.isoCarrier.hom ((D.ι i).base a) := congrArg _ h1
      _ = D.isoCarrier.hom x := congrArg _ ha
  have hj : D.isoCarrier.hom x ∈ Set.range ⇑(D.topGlueData.ι j) := by
    refine ⟨b, ?_⟩
    have h2 := ConcreteCategory.congr_hom (D.ι_isoCarrier_inv j) b
    rw [ConcreteCategory.comp_apply] at h2
    calc D.topGlueData.ι j b
        = D.isoCarrier.hom (D.isoCarrier.inv (D.topGlueData.ι j b)) :=
          (Iso.inv_hom_id_apply _ _).symm
      _ = D.isoCarrier.hom ((D.ι j).base b) := congrArg _ h2
      _ = D.isoCarrier.hom x := congrArg _ hb
  exact Set.disjoint_left.mp key hi hj

end AlgebraicGeometry.LocallyRingedSpace.GlueData
