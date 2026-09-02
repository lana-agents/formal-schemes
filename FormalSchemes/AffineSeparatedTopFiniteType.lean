import FormalSchemes.AffineSeparatedScheme
import FormalSchemes.RelativeTopFiniteType

set_option linter.style.header false

/-!
# An affine formal scheme of finite type over `Spf R` is separated (EGA I §10.13, §10.15)

Two properties of a formal scheme over an affine base have been developed independently in this
tree: being **topologically of finite type** (§10.13,
`FormalSchemes.RelativeTopFiniteType`) and being **separated** (§10.15,
`FormalSchemes.GeneralSeparatedScheme`). For an affine formal scheme they hold together, and this
file says so in one statement:

> If `A` is an `R`-algebra topologically of finite type with ideal of definition `L`, then
> `Spf L` is **separated over `Spf R`**, and its structural morphism is **topologically of finite
> type**.

This is the affine case of Raynaud's admissible formal `R`-schemes (Bosch, LNM 2105, §7): the
local model every chart of every glued formal scheme in this development is an instance of.

## Why this is a single statement and not two facts side by side

Both halves are about the *same* morphism, `IsTopologicallyFiniteType.structHom h : Spf L ⟶ Spf R`.
The separatedness half sees it through `.toLRSHom` only because
`FormalScheme.IsSeparatedOverSpf` is stated at the level of `LocallyRingedSpace`, matching
`fibreLiftAdic` and the rest of the general fibre-product API, while
`FormalScheme.IsRelativelyTopFiniteType` is stated at `FormalScheme.Hom`. The asymmetry is in the
two predicates, not in the object: `FormalScheme.Hom.mk` and `.toLRSHom` are inverse on the nose.

## The ideal of definition is not specialised

`spf_isSeparatedOverSpf` is stated at the canonical ideal `I·A = I.map (algebraMap R A)`, whereas a
tf-type presentation carries its own `L`. These agree — that is `IsTopologicallyFiniteType.map_eq`
— so the theorem below is stated at a general `L` and substitutes, rather than restricting the
hypothesis to the canonical spelling. The general form is the one a consumer holds.

## Main results

* `AlgebraicGeometry.spf_isSeparatedOverSpf_and_isRelativelyTopFiniteType`: an affine formal scheme
  topologically of finite type over `Spf R` is separated over `Spf R`, and of finite type.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13, §10.15.
-/

noncomputable section

open CategoryTheory FormalSpectrum

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {I : Ideal R} (hI : I.FG)
variable [TopologicalSpace R] [IsAdicRing I]
variable {A : Type u} [CommRing A] [Algebra R A] [TopologicalSpace A]
variable {L : Ideal A} [IsAdicRing L]

/-- **An affine formal scheme topologically of finite type over `Spf R` is separated over `Spf R`**
(EGA I §10.13, §10.15), and its structural morphism is of finite type: both EGA properties of the
single morphism `IsTopologicallyFiniteType.structHom h : Spf L ⟶ Spf R`.

The separatedness half is `spf_isSeparatedOverSpf` (issue 844) and needs no finite-type input at
all — every affine formal scheme is separated. What the finite-type hypothesis buys is the second
half, `IsTopologicallyFiniteType.isRelativelyTopFiniteType`, and the right to state them together.

`IsTopologicallyFiniteType.map_eq` identifies `L` with `I·A`, after which the two structural
morphisms are the same term: `IsTopologicallyFiniteType.structHom` is `FormalScheme.Hom.mk` of
`locallyRingedSpaceMap I L (algebraMap R A) _`, and its proof argument is a proof of the same
`Prop` as the `Ideal.le_comap_map` that `spf_isSeparatedOverSpf` uses. -/
theorem spf_isSeparatedOverSpf_and_isRelativelyTopFiniteType
    (h : IsTopologicallyFiniteType R I A L) :
    FormalScheme.IsSeparatedOverSpf hI (FormalScheme.Spf L)
        (IsTopologicallyFiniteType.structHom h).toLRSHom ∧
      FormalScheme.IsRelativelyTopFiniteType R I (IsTopologicallyFiniteType.structHom h) := by
  obtain rfl := IsTopologicallyFiniteType.map_eq h
  exact ⟨spf_isSeparatedOverSpf hI, IsTopologicallyFiniteType.isRelativelyTopFiniteType h⟩

end AlgebraicGeometry

end
