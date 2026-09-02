import FormalSchemes.Gluing
import FormalSchemes.LocallyRingedSpaceGlueDesc

set_option linter.style.header false

/-!
# Gluing morphisms out of a glued formal scheme

Given a `FormalScheme.GlueData` `D` with glued formal scheme `T := D.gluedFormalScheme`, a family
of morphisms `k i : U i ⟶ Y` from the pieces to a common target `Y` that **agree on the overlaps**
glues to a single morphism `T ⟶ Y`. This is the morphism-level companion of the object-level
`gluedFormalScheme`: the glued space is the multicoequalizer of the gluing diagram
(`CategoryTheory.GlueData.glued = multicoequalizer D.diagram`), so a morphism out of it is exactly a
compatible cocone.

**Everything here is a wrapper over `FormalSchemes.LocallyRingedSpaceGlueDesc`**, which states the
same three results for a bare `AlgebraicGeometry.LocallyRingedSpace.GlueData`. Nothing in the
construction uses the formal-scheme condition on the pieces, so there is no second proof: `ι` of a
`FormalScheme.GlueData` is by definition `ι` of its underlying locally ringed space glue datum, and
`(D.gluedFormalScheme).toLocallyRingedSpace` is that datum's `glued`. The wrappers exist because the
Tate cluster spells its glued objects formally, and their statements are unchanged.

The compatibility condition is the one imposed by the gluing diagram
(`CategoryTheory.GlueData.diagram`, whose two legs on the overlap `V(i, j)` are `f i j` and
`t i j ≫ f j i`):
```
f i j ≫ k i = t i j ≫ f j i ≫ k j    for all i, j.
```

## Main definitions

* `FormalScheme.GlueData.glueMorphisms`: the glued morphism `T ⟶ Y`.
* `FormalScheme.GlueData.ι_glueMorphisms`: it restricts to `k i` along each `ι i`.
* `FormalScheme.GlueData.hom_ext`: two morphisms out of `T` agreeing on every piece are equal.

This is the combinator required to assemble the structural morphism `T ⟶ Spf R` of the Tate chain
(issue 208) out of the per-patch structural morphisms, and more generally any morphism out of a
non-affine formal scheme built by gluing.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4.
* Mathlib `CategoryTheory.GlueData`, `CategoryTheory.Limits.multicoequalizer`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace FormalScheme.GlueData

variable (D : FormalScheme.GlueData.{u}) {Y : LocallyRingedSpace.{u}}

/-- Abbreviation for the underlying `CategoryTheory.GlueData` of locally ringed spaces. -/
private abbrev cgd : CategoryTheory.GlueData LocallyRingedSpace.{u} :=
  D.toLocallyRingedSpaceGlueData.toGlueData

/-- **Gluing a family of morphisms out of the glued formal scheme.** Given morphisms
`k i : U i ⟶ Y` from the pieces to a common target that agree on the overlaps
(`f i j ≫ k i = t i j ≫ f j i ≫ k j`), the induced morphism `T ⟶ Y` out of the glued formal
scheme.

This is `AlgebraicGeometry.LocallyRingedSpace.GlueData.desc` at the underlying glue datum: the
formal-scheme condition on the pieces plays no part in the construction. Definitionally it is
still `Multicoequalizer.desc D.cgd.diagram Y k _`, which is what the `simp` lemmas of consumers
that unfold it rely on. -/
def glueMorphisms
    (k : ∀ i, D.cgd.U i ⟶ Y)
    (h : ∀ i j, D.cgd.f i j ≫ k i = D.cgd.t i j ≫ D.cgd.f j i ≫ k j) :
    (D.gluedFormalScheme).toLocallyRingedSpace ⟶ Y :=
  D.toLocallyRingedSpaceGlueData.desc k h

@[reassoc (attr := simp)]
theorem ι_glueMorphisms
    (k : ∀ i, D.cgd.U i ⟶ Y)
    (h : ∀ i j, D.cgd.f i j ≫ k i = D.cgd.t i j ≫ D.cgd.f j i ≫ k j)
    (i : D.toLocallyRingedSpaceGlueData.J) :
    D.ι i ≫ D.glueMorphisms k h = k i :=
  D.toLocallyRingedSpaceGlueData.ι_desc k h i

/-- **Uniqueness of the glued morphism**: two morphisms out of the glued formal scheme that agree
after restriction along every `ι i` are equal (the `ι i` are jointly epimorphic). -/
theorem hom_ext {f g : (D.gluedFormalScheme).toLocallyRingedSpace ⟶ Y}
    (h : ∀ i, D.ι i ≫ f = D.ι i ≫ g) : f = g :=
  D.toLocallyRingedSpaceGlueData.hom_ext h

end FormalScheme.GlueData

end AlgebraicGeometry
