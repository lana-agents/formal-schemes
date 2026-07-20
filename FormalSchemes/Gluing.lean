import FormalSchemes.SpfMap
import Mathlib.AlgebraicGeometry.Gluing

set_option linter.style.header false

/-!
# Locality of the formal-scheme condition, and gluing

Being a formal scheme is a *local* condition on a locally ringed space: a locally ringed space
admitting a jointly surjective family of open immersions from affine formal schemes is a formal
scheme (`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.formalScheme`), exactly as for
schemes (`LocallyRingedSpace.IsOpenImmersion.scheme`). Conversely, every formal scheme admits
such a family (`FormalScheme.exists_openImmersion`).

Together these give the gluing theorem: a family of formal schemes glued along open immersions
(a `LocallyRingedSpace.GlueData` whose pieces are formal schemes) is again a formal scheme
(`FormalScheme.GlueData.gluedFormalScheme`), since the glued space is covered by the images of
the pieces. This is the construction that produces non-affine formal schemes — in particular
the Tate chain, obtained by gluing formal annuli.

## Main definitions and results

* `FormalScheme.exists_openImmersion`: every point of a formal scheme is in the range of an
  open immersion from an affine formal scheme.
* `LocallyRingedSpace.IsOpenImmersion.formalScheme`: the converse; the local criterion.
* `FormalScheme.GlueData`: glue data of formal schemes (a `LocallyRingedSpace.GlueData` whose
  pieces are formal schemes), and `FormalScheme.GlueData.gluedFormalScheme`, the glued formal
  scheme, with `ι` the open immersions of the pieces into it.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4.
* [The Stacks Project, Tag 0AIL](https://stacks.math.columbia.edu/tag/0AIL)
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

namespace LocallyRingedSpace.IsOpenImmersion

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
-- As for `LocallyRingedSpace.IsOpenImmersion.scheme` in Mathlib, comparing the restriction of
-- the ambient space with the affine model needs reducible-transparency defeq checks.
/-- **The formal-scheme condition is local**: a locally ringed space admitting, around every
point, an open immersion from the formal spectrum of an adic ring is a formal scheme. This
mirrors `LocallyRingedSpace.IsOpenImmersion.scheme` for schemes. -/
protected def formalScheme (X : LocallyRingedSpace.{u})
    (h : ∀ x : X, ∃ (R : Type u) (_ : CommRing R) (_ : TopologicalSpace R) (I : Ideal R)
      (_ : IsAdicRing I) (f : FormalSpectrum.locallyRingedSpaceObj I ⟶ X),
        (x ∈ Set.range f.base :) ∧ LocallyRingedSpace.IsOpenImmersion f) :
    FormalScheme where
  toLocallyRingedSpace := X
  local_affine := by
    intro x
    obtain ⟨R, _, _, I, _, f, h₁, h₂⟩ := h x
    refine ⟨⟨⟨_, h₂.base_open.isOpen_range⟩, h₁⟩, R, ‹_›, ‹_›, I, ‹_›, ⟨?_⟩⟩
    apply LocallyRingedSpace.isoOfSheafedSpaceIso
    refine SheafedSpace.forgetToPresheafedSpace.preimageIso ?_
    apply PresheafedSpace.IsOpenImmersion.isoOfRangeEq (PresheafedSpace.ofRestrict _ _) f.1
    exact Subtype.range_coe_subtype

end LocallyRingedSpace.IsOpenImmersion

namespace FormalScheme

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
-- Composing the local isomorphism with the inclusion of the open needs reducible-transparency
-- defeq checks, as in the criterion above.
/-- Every point of a formal scheme lies in the range of an open immersion from an affine formal
scheme: the inverse of the local isomorphism, composed with the inclusion of the open. -/
theorem exists_openImmersion (X : FormalScheme.{u}) (x : X) :
    ∃ (R : Type u) (_ : CommRing R) (_ : TopologicalSpace R) (I : Ideal R) (_ : IsAdicRing I)
      (f : FormalSpectrum.locallyRingedSpaceObj I ⟶ X.toLocallyRingedSpace),
      (x ∈ Set.range f.base :) ∧ LocallyRingedSpace.IsOpenImmersion f := by
  obtain ⟨U, R, hR, hTR, I, hI, ⟨e⟩⟩ := X.local_affine x
  refine ⟨R, hR, hTR, I, hI,
    e.inv ≫ X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding,
    ⟨e.hom.base ⟨x, U.2⟩, ?_⟩, inferInstance⟩
  simp only [LocallyRingedSpace.comp_toHom, PresheafedSpace.comp_base, TopCat.hom_comp,
    ContinuousMap.coe_comp, Function.comp_apply]
  have hinv : e.inv.base (e.hom.base ⟨x, U.2⟩) = ⟨x, U.2⟩ := by simp
  rw [hinv]
  rfl

/-- Glue data of formal schemes: a family of formal schemes together with gluing data of the
underlying locally ringed spaces along open immersions. -/
structure GlueData where
  /-- The underlying glue data of locally ringed spaces. -/
  toLocallyRingedSpaceGlueData : LocallyRingedSpace.GlueData.{u}
  /-- Each piece is a formal scheme. -/
  isFormalScheme : ∀ i : toLocallyRingedSpaceGlueData.J,
    ∃ Y : FormalScheme.{u},
      Nonempty (Y.toLocallyRingedSpace ≅ toLocallyRingedSpaceGlueData.U i)

namespace GlueData

variable (D : GlueData.{u})

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
-- Same transparency requirement as in the local criterion above.
/-- **Gluing formal schemes**: the locally ringed space glued from a family of formal schemes
along open immersions is a formal scheme. Every point lies in the image of some piece, and the
piece is locally an affine formal scheme, so the criterion
`LocallyRingedSpace.IsOpenImmersion.formalScheme` applies. -/
def gluedFormalScheme : FormalScheme.{u} := by
  refine LocallyRingedSpace.IsOpenImmersion.formalScheme
    D.toLocallyRingedSpaceGlueData.toGlueData.glued fun x => ?_
  obtain ⟨i, y, rfl⟩ := D.toLocallyRingedSpaceGlueData.ι_jointly_surjective x
  obtain ⟨Y, ⟨e⟩⟩ := D.isFormalScheme i
  obtain ⟨R, hR, hTR, I, hI, f, ⟨z, hz⟩, hf⟩ := Y.exists_openImmersion (e.inv.base y)
  refine ⟨R, hR, hTR, I, hI,
    f ≫ e.hom ≫ D.toLocallyRingedSpaceGlueData.toGlueData.ι i, ⟨z, ?_⟩, inferInstance⟩
  simp only [LocallyRingedSpace.comp_toHom, PresheafedSpace.comp_base, TopCat.hom_comp,
    ContinuousMap.coe_comp, Function.comp_apply]
  rw [hz]
  have hy : e.hom.base (e.inv.base y) = y := by simp
  rw [hy]

/-- The open immersion of the `i`-th piece into the glued formal scheme. -/
def ι (i : D.toLocallyRingedSpaceGlueData.J) :
    D.toLocallyRingedSpaceGlueData.U i ⟶ (D.gluedFormalScheme).toLocallyRingedSpace :=
  D.toLocallyRingedSpaceGlueData.toGlueData.ι i

instance ι_isOpenImmersion (i : D.toLocallyRingedSpaceGlueData.J) :
    LocallyRingedSpace.IsOpenImmersion (D.ι i) :=
  LocallyRingedSpace.GlueData.ι_isOpenImmersion _ i

theorem ι_jointly_surjective (x : (D.gluedFormalScheme).toLocallyRingedSpace) :
    ∃ (i : D.toLocallyRingedSpaceGlueData.J) (y : D.toLocallyRingedSpaceGlueData.U i),
      (D.ι i).base y = x :=
  D.toLocallyRingedSpaceGlueData.ι_jointly_surjective x

end GlueData

end FormalScheme

end AlgebraicGeometry
