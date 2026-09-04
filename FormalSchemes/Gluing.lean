import FormalSchemes.OpenImmersionIsoOfRangeEq
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

* `LocallyRingedSpace.HasAffineChartAt`: the per-point hypothesis of the local criterion, named
  so that it can be established one point at a time, with
  `LocallyRingedSpace.formalSchemeOfHasAffineChartAt` the criterion restated in those terms.
* `LocallyRingedSpace.hasAffineChartAt_of_isoRestrict`: an open of `X` *identified* with a formal
  spectrum gives a chart at each of its points. This is the converse of
  `LocallyRingedSpace.IsOpenImmersion.isoRestrictOfRangeEq`, and it is the whole content of
  `FormalScheme.exists_openImmersion`.
* `LocallyRingedSpace.hasAffineChartAt_of_restrict`: the same statement with the identification
  weakened to a chart — an open of `X` that merely *has* a chart at a point gives one on `X` at
  that point. `LocallyRingedSpace.hasAffineChartAt_of_isoRestrict` is its affine case.
* `FormalScheme.exists_openImmersion`: every point of a formal scheme is in the range of an
  open immersion from an affine formal scheme.
* `LocallyRingedSpace.IsOpenImmersion.formalScheme`: the converse; the local criterion.
* `FormalScheme.GlueData`: glue data of formal schemes (a `LocallyRingedSpace.GlueData` whose
  pieces are formal schemes), and `FormalScheme.GlueData.gluedFormalScheme`, the glued formal
  scheme, with `ι` the open immersions of the pieces into it.
* `uliftBool_not_pairwise_distinct`: the two-element index type carries no pairwise distinct
  triple. This is what discharges the triple-index fields of a *two-patch* glue datum. It lives
  here because fourteen files across the tree call it and this is the module about gluing that
  all fourteen of their import closures already contain.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4.
* [The Stacks Project, Tag 0AIL](https://stacks.math.columbia.edu/tag/0AIL)
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-! ### The two-element index type -/

/-- **On the two-element index type `ULift Bool` no triple of indices is pairwise distinct.**

Every two-patch construction in this development is a `CategoryTheory.GlueData'` (or one of the
tree's charted-datum wrappers) indexed by `ULift Bool`, and each of them has to supply the
triple-index fields — `t'`, `t_fac`, `cocycle` for a glue datum, `σ`, `hστ`, `hσc` for the
algebra data — which this lemma makes vacuous.

It is called from **fourteen** files, spread over the scheme-side, completion-side, Tate and
general-fibre-product lines. **Eleven** of those fourteen used to restate it, under **nine**
names — six of them carrying a file-specific two-letter prefix that no grep for either public
name could reach — and the remaining three already called one of the two public copies. Count
the callers, not the declarations: the two are not the same set, and the home measurement below
has to be made against the callers.

The lemma itself needs no import at all — `ULift`, `Bool`, `Ne` and `False` are everything that
occurs in it — so the home was chosen by measuring those fourteen import closures: their
intersection has 27 members and this module is one of them, so nothing had to gain an import. -/
theorem uliftBool_not_pairwise_distinct {i j k : ULift.{u} Bool}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : False := by
  obtain ⟨i⟩ := i
  obtain ⟨j⟩ := j
  obtain ⟨k⟩ := k
  cases i <;> cases j <;> cases k <;> simp_all

namespace LocallyRingedSpace.IsOpenImmersion

/-- **The formal-scheme condition is local**: a locally ringed space admitting, around every
point, an open immersion from the formal spectrum of an adic ring is a formal scheme. This
mirrors `LocallyRingedSpace.IsOpenImmersion.scheme` for schemes.

The chart datum the `FormalScheme.local_affine` field asks for is exactly
`LocallyRingedSpace.IsOpenImmersion.isoRestrictOpensRange`
(`FormalSchemes.OpenImmersionIsoOfRangeEq`), so both halves of the witness — the open and the
isomorphism — come from the open immersion itself. Until issue 1479 this file built them by hand,
the isomorphism through `PresheafedSpace.IsOpenImmersion.isoOfRangeEq`, as
`LocallyRingedSpace.IsOpenImmersion.scheme` still does in Mathlib; the locally-ringed-space
`LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq` removes the detour.

**On the three `set_option backward.isDefEq.respectTransparency false` blocks this file used to
carry** (here, on `FormalScheme.exists_openImmersion`, and on
`FormalScheme.GlueData.gluedFormalScheme`, the latter two justified only by "as in the criterion
above"): they were **already stale**, and not made stale by the rewrite. Checked rather than
assumed — stripping all three from the *unmodified* file compiles. They are gone; if a future change
to any of the three proofs needs reducible-transparency defeq again, that option is what to reach
for, and `LocallyRingedSpace.IsOpenImmersion.scheme` in Mathlib is the precedent. -/
protected def formalScheme (X : LocallyRingedSpace.{u})
    (h : ∀ x : X, ∃ (R : Type u) (_ : CommRing R) (_ : TopologicalSpace R) (I : Ideal R)
      (_ : IsAdicRing I) (f : FormalSpectrum.locallyRingedSpaceObj I ⟶ X),
        (x ∈ Set.range f.base :) ∧ LocallyRingedSpace.IsOpenImmersion f) :
    FormalScheme where
  toLocallyRingedSpace := X
  local_affine := by
    intro x
    obtain ⟨R, _, _, I, _, f, h₁, h₂⟩ := h x
    haveI := h₂
    refine ⟨⟨opensRange f, h₁⟩, R, ‹_›, ‹_›, I, ‹_›, ⟨?_⟩⟩
    exact isoRestrictOpensRange f

end LocallyRingedSpace.IsOpenImmersion

/-! ### Affine formal charts, one point at a time -/

namespace LocallyRingedSpace

/-- **`Q` has an affine formal chart at `x`**: some formal spectrum `Spf I` of an adic ring admits
an open immersion into `Q` whose range contains `x`. This is character-for-character the per-point
hypothesis of `LocallyRingedSpace.IsOpenImmersion.formalScheme` above, named so that it can be
established one point at a time — an action can be properly discontinuous at some points and not at
others, and then the global criterion says nothing while the pointwise one still produces charts
(`FormalSchemes.ActionQuotientChartAt`). -/
def HasAffineChartAt (Q : LocallyRingedSpace.{u}) (x : Q) : Prop :=
  ∃ (R : Type u) (_ : CommRing R) (_ : TopologicalSpace R) (I : Ideal R) (_ : IsAdicRing I)
    (f : FormalSpectrum.locallyRingedSpaceObj I ⟶ Q),
      (x ∈ Set.range f.base :) ∧ LocallyRingedSpace.IsOpenImmersion f

/-- **A locally ringed space with an affine formal chart at every point is a formal scheme.** This
is `LocallyRingedSpace.IsOpenImmersion.formalScheme` with its hypothesis spelled through
`HasAffineChartAt`; the content is entirely in that theorem. -/
def formalSchemeOfHasAffineChartAt (Q : LocallyRingedSpace.{u})
    (h : ∀ x : Q, HasAffineChartAt Q x) : FormalScheme.{u} :=
  LocallyRingedSpace.IsOpenImmersion.formalScheme Q h

/-- The formal scheme produced has `Q` itself as its underlying locally ringed space. -/
@[simp]
theorem formalSchemeOfHasAffineChartAt_toLocallyRingedSpace (Q : LocallyRingedSpace.{u})
    (h : ∀ x : Q, HasAffineChartAt Q x) :
    (formalSchemeOfHasAffineChartAt Q h).toLocallyRingedSpace = Q :=
  rfl

/-- **An open identified with a formal spectrum is a chart at each of its points.** If
`e : X|_U ≅ Spf L`, then `e.inv ≫ X.ofRestrict U.isOpenEmbedding` is an open immersion whose range
is `U`, so every `y ∈ U` has an affine formal chart.

This is the direction opposite to `LocallyRingedSpace.IsOpenImmersion.isoRestrictOfRangeEq`
(`FormalSchemes.OpenImmersionIsoOfRangeEq`), which converts an open immersion with range `U` into
such an identification. Every *cover-shaped* hypothesis on this tree — the
`AlgebraicGeometry.FormalScheme.local_affine` field,
`FormalSpectrum.isThickeningColimitTarget_of_cover`,
`FormalSpectrum.existsUnique_hom_thickeningMap_spfCover` — supplies data in the `≅` direction,
while `HasAffineChartAt` consumes it in the open-immersion direction; this is the one line between
them, and it is what makes a formal-affine chart *datum* on a target say something about the
target's points.

It is the first **named** form of that converse, not the first form of it: the
`FormalScheme.local_affine` field supplies exactly this datum, so
`FormalScheme.exists_openImmersion` below has been running this argument inline since this file was
written, and now cites it instead. -/
theorem hasAffineChartAt_of_isoRestrict {X : LocallyRingedSpace.{u}} (U : Opens X.toTopCat)
    {C : Type u} [CommRing C] [TopologicalSpace C] (L : Ideal C) [IsAdicRing L]
    (e : X.restrict U.isOpenEmbedding ≅ FormalSpectrum.locallyRingedSpaceObj L)
    {y : X} (hy : y ∈ U) : HasAffineChartAt X y := by
  refine ⟨C, inferInstance, inferInstance, L, inferInstance,
    e.inv ≫ X.ofRestrict U.isOpenEmbedding, ⟨e.hom.base ⟨y, hy⟩, ?_⟩, inferInstance⟩
  simp only [comp_toHom, PresheafedSpace.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply,
    iso_hom_base_inv_base_apply]
  rfl

/-- **A chart on an open subspace is a chart on the whole space.** Composing the chart of
`X|_U` with `X.ofRestrict U.isOpenEmbedding` — an open immersion, as is any composite of two —
leaves the range where it was, inside `U`.

This is the weaker hypothesis `hasAffineChartAt_of_isoRestrict` is the affine case of: there the
open *is* a formal spectrum, here it merely has a chart at the one point in question. So a
question about charts on `X` restricted to an open never becomes harder by being asked on the
open. -/
theorem hasAffineChartAt_of_restrict {X : LocallyRingedSpace.{u}} (U : Opens X.toTopCat)
    {y : X} (hy : y ∈ U)
    (h : HasAffineChartAt (X.restrict U.isOpenEmbedding) ⟨y, hy⟩) : HasAffineChartAt X y := by
  obtain ⟨C, _, _, L, _, f, ⟨z, hz⟩, hf⟩ := h
  haveI := hf
  refine ⟨C, inferInstance, inferInstance, L, inferInstance,
    f ≫ X.ofRestrict U.isOpenEmbedding, ⟨z, ?_⟩, inferInstance⟩
  simp only [comp_toHom, PresheafedSpace.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply]
  rw [hz]
  rfl

end LocallyRingedSpace

namespace FormalScheme

/-- Every point of a formal scheme lies in the range of an open immersion from an affine formal
scheme: the inverse of the local isomorphism, composed with the inclusion of the open. That is
`LocallyRingedSpace.hasAffineChartAt_of_isoRestrict` applied to the `FormalScheme.local_affine`
datum, the conclusion here being `HasAffineChartAt X.toLocallyRingedSpace x` unfolded. -/
theorem exists_openImmersion (X : FormalScheme.{u}) (x : X) :
    ∃ (R : Type u) (_ : CommRing R) (_ : TopologicalSpace R) (I : Ideal R) (_ : IsAdicRing I)
      (f : FormalSpectrum.locallyRingedSpaceObj I ⟶ X.toLocallyRingedSpace),
      (x ∈ Set.range f.base :) ∧ LocallyRingedSpace.IsOpenImmersion f := by
  obtain ⟨U, R, _, _, I, _, ⟨e⟩⟩ := X.local_affine x
  exact LocallyRingedSpace.hasAffineChartAt_of_isoRestrict U.1 I e U.2

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
