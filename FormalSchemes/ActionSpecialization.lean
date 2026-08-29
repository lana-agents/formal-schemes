import FormalSchemes.ActionDiscontinuous

set_option linter.style.header false

/-!
# A specialization obstruction to proper discontinuity

`FormalSchemes.ActionDiscontinuous` defines
`AlgebraicGeometry.LocallyRingedSpace.IsFreeProperlyDiscontinuous a`: every point of `X` has an
open neighbourhood `U` with `(a g) '' U` disjoint from `U` for every `g ≠ 1`. That file proves the
hypothesis *holds* for one action (the Tate `q^{2ℤ}`-shift). This file provides the tool for the
opposite verdict, and it is a purely topological one.

## The criterion

On a space that is not locally Hausdorff — a Zariski space, say — an open neighbourhood of a point
`x` is forced to contain every point that `x` is a specialization of. So if a single point `w`
has **both** `w ⤳ x` and `(a g) w ⤳ x` for one `g ≠ 1`, then every open neighbourhood of `x`
contains `w` and `(a g) w`, hence meets its own `g`-translate in `(a g) w`, and no neighbourhood of
`x` can separate the translates. That is `not_isFreeProperlyDiscontinuous_of_specializes`.

The geometry it is meant for: `x` a node of a chain of rational curves, `w` the generic point of
the component through `x` on one side, `a g` the shift by one component, so that `(a g) w` is the
generic point of the component through `x` on the other side. Both generic points specialize to the
node, so the node has no separating neighbourhood. See
`FormalSchemes.TateInvPeriodNotDiscontinuous`.

Nothing here weakens `IsProperlyDiscontinuousOn` or `IsFreeProperlyDiscontinuous`; both are used
exactly as stated in `FormalSchemes.ActionDiscontinuous`.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.not_isProperlyDiscontinuousOn_of_specializes`
* `AlgebraicGeometry.LocallyRingedSpace.not_isFreeProperlyDiscontinuous_of_specializes`
-/

noncomputable section

open CategoryTheory Topology

universe v u

namespace AlgebraicGeometry

namespace LocallyRingedSpace

variable {G : Type v} [Group G] {X : LocallyRingedSpace.{u}} {a : G →* Aut X}

/-- **A point that two `g`-related points both specialize to has no separating neighbourhood.** If
`w ⤳ x` and `(a g) w ⤳ x` with `g ≠ 1`, then any open `U ∋ x` contains both `w` and `(a g) w`, so
`(a g) w` lies in `(a g) '' U` and in `U`: the two are not disjoint. -/
theorem not_isProperlyDiscontinuousOn_of_specializes {U : Set X} (hUopen : IsOpen U) {x w : X}
    (hxU : x ∈ U) {g : G} (hg : g ≠ 1) (hw : w ⤳ x) (hgw : (a g).hom.base w ⤳ x) :
    ¬ IsProperlyDiscontinuousOn a U := fun hU =>
  Set.disjoint_left.mp (hU g hg)
    (Set.mem_image_of_mem _ (hw.mem_open hUopen hxU)) (hgw.mem_open hUopen hxU)

/-- **The specialization obstruction.** A single pair `w`, `g ≠ 1` with `w ⤳ x` and `(a g) w ⤳ x`
refutes `IsFreeProperlyDiscontinuous a`: the point `x` has no separating neighbourhood at all, since
every open neighbourhood of `x` contains `w` and its `g`-translate. -/
theorem not_isFreeProperlyDiscontinuous_of_specializes {x w : X} {g : G} (hg : g ≠ 1)
    (hw : w ⤳ x) (hgw : (a g).hom.base w ⤳ x) : ¬ IsFreeProperlyDiscontinuous a := by
  intro h
  obtain ⟨U, hUopen, hxU, hU⟩ := h x
  exact not_isProperlyDiscontinuousOn_of_specializes hUopen hxU hg hw hgw hU

end LocallyRingedSpace

end AlgebraicGeometry
