import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.Topology.Sheaves.SheafCondition.Sites

set_option linter.style.header false

/-!
# The comparison maps of a morphism of locally ringed spaces are detected on a basis

For a morphism `f : X ⟶ Y` of locally ringed spaces, the comparison
`f.c : 𝒪_Y ⟶ f_* 𝒪_X` is a morphism of **sheaves** on `Y`, because the pushforward of a sheaf
along a continuous map is a sheaf (`TopCat.Sheaf.pushforward_sheaf_of_sheaf`). A morphism of
sheaves is an isomorphism as soon as its components on a basis of the topology are
(`TopCat.Sheaf.isIso_iff_isIso_basis`), so the same is true of `f.c`:

> if `IsIso (f.c.app (op (B i)))` for every member of a basis `B` of `Opens Y`, then
> `IsIso (f.c.app O)` for **every** open `O`.

The converse is trivial, so this is stated as an `Iff`
(`AlgebraicGeometry.LocallyRingedSpace.isIso_c_app_iff_isBasis`): a `∀ O` obligation on the sheaf
half of an isomorphism criterion is exactly a `∀ i` obligation over any basis.

## Why this file exists, and why it is this low

Nothing below mentions a ring, an ideal, a spectrum or a formal scheme, so — following
`FormalSchemes/LocallyRingedSpaceHomExt.lean`, which makes the same argument for joint epimorphy
— the module sits directly on Mathlib and is in the import closure of everything that could want
it. Its intended consumer is `FormalSchemes/BasicOpenSectionsHom.lean`, which instantiates it at
the basic opens of a formal spectrum, but there is nothing formal-scheme-shaped in the statements
and a leaf placement would strand them (issue 1752).

`AlgebraicGeometry.LocallyRingedSpace.isIso_of_isIso_base_of_isIso_c_app` and
`AlgebraicGeometry.LocallyRingedSpace.isIso_iff_isIso_base_and_isIso_c_app`
(`FormalSchemes.ActionQuotientRestrictQuotient`) are the companion facts — that the base map and
the comparison maps together decide invertibility. They are **not** moved here: they are landed,
they have consumers, and relocating them is a separate row.

## Route

`f.c` is repackaged as a morphism of `TopCat.Sheaf` by `CategoryTheory.ObjectProperty.homMk`, since
`TopCat.Sheaf` is the full subcategory of presheaves cut out by the sheaf condition and its
morphisms *are* the presheaf morphisms. `TopCat.Sheaf.isIso_iff_isIso_basis` then applies verbatim
— its hypothesis is stated at `φ.hom.app`, which is `f.c.app` definitionally — and the instance
`CategoryTheory.ObjectProperty.instIsIsoHom` carries the resulting `IsIso` back to `f.c`.
`CategoryTheory.NatTrans.isIso_iff_isIso_app` then reads off the components.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.isIso_c_of_isBasis`: `f.c` is an isomorphism of presheaves
  as soon as its components on a basis are.
* `AlgebraicGeometry.LocallyRingedSpace.isIso_c_app_iff_isBasis`: the `∀ i` and the `∀ O` forms of
  the sheaf half are equivalent.
* `AlgebraicGeometry.LocallyRingedSpace.isIso_c_app_of_isBasis`: the direction a criterion
  consumes.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe v u

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X Y : LocallyRingedSpace.{u}}

/-- **The comparison of a morphism of locally ringed spaces is an isomorphism as soon as it is one
on a basis.** `f.c` is a morphism of sheaves — the pushforward of `𝒪_X` along `f.base` is a sheaf —
so `TopCat.Sheaf.isIso_iff_isIso_basis` applies to it once it is repackaged as a morphism of the
full subcategory `TopCat.Sheaf`, which changes nothing definitionally. -/
theorem isIso_c_of_isBasis {ι : Type v} (f : X ⟶ Y) {B : ι → Opens Y.toTopCat}
    (hB : Opens.IsBasis (Set.range B)) (hi : ∀ i, IsIso (f.c.app (op (B i)))) :
    IsIso f.c :=
  haveI : IsIso (ObjectProperty.homMk (X := Y.toSheafedSpace.sheaf)
      (Y := (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.toSheafedSpace.sheaf) f.c) :=
    TopCat.Sheaf.isIso_iff_isIso_basis hB hi
  inferInstanceAs (IsIso (ObjectProperty.homMk (X := Y.toSheafedSpace.sheaf)
    (Y := (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.toSheafedSpace.sheaf) f.c).hom)

/-- **The sheaf half of an isomorphism criterion is a statement about a basis.** The `∀ O` form and
the `∀ i` form of "every comparison map of `f` is invertible" are equivalent, for any basis `B` of
the opens of the target.

The reverse implication is the specialisation at a basis member and carries no content; the point
is the forward one, which is `AlgebraicGeometry.LocallyRingedSpace.isIso_c_of_isBasis` followed by
`CategoryTheory.NatTrans.isIso_iff_isIso_app`. -/
theorem isIso_c_app_iff_isBasis {ι : Type v} (f : X ⟶ Y) {B : ι → Opens Y.toTopCat}
    (hB : Opens.IsBasis (Set.range B)) :
    (∀ i, IsIso (f.c.app (op (B i)))) ↔ ∀ O : (Opens Y.toTopCat)ᵒᵖ, IsIso (f.c.app O) :=
  ⟨fun hi => (NatTrans.isIso_iff_isIso_app f.c).mp (isIso_c_of_isBasis f hB hi), fun h _ => h _⟩

/-- The forward direction of `AlgebraicGeometry.LocallyRingedSpace.isIso_c_app_iff_isBasis`, in the
shape an isomorphism criterion consumes. -/
theorem isIso_c_app_of_isBasis {ι : Type v} (f : X ⟶ Y) {B : ι → Opens Y.toTopCat}
    (hB : Opens.IsBasis (Set.range B)) (hi : ∀ i, IsIso (f.c.app (op (B i))))
    (O : (Opens Y.toTopCat)ᵒᵖ) : IsIso (f.c.app O) :=
  (isIso_c_app_iff_isBasis f hB).mp hi O

end AlgebraicGeometry.LocallyRingedSpace

end
