import FormalSchemes.BasicOpenImmersionLRS
import FormalSchemes.OpenCoverGlueMorphisms

set_option linter.style.header false

/-!
# `Spf R` is covered by its basic-open charts

A family of elements `r : ι → R` whose basic opens cover `|Spf R|` presents `Spf R` as a
`FormalScheme.OpenCover` whose pieces are the affine formal schemes `Spf R{1/r i}`
(`FormalSpectrum.basicOpenCover`). Both structural obligations are already on the tree:
`isOpenImmersion_basicOpenChart` says each chart `Spf R{1/r i} ⟶ Spf R` is an open immersion, and
`range_mapTop_basicOpen` says its range is `D(r i)`.

Nothing on the tree built this cover: `FormalScheme.affineCover` (`OpenCover.lean`),
`OpenCover.ofAffineCharts` (`GlobalSectionsHom.lean`), `LiftedBasicOpenCover.liftedBasicCover` and
the refined covers of the `GeneralFibreProduct*` line are all differently shaped — they cover a
*general* formal scheme by charts obtained from its local-affineness data, whereas this one covers
an *affine* formal scheme by the basic opens of a chosen family of ring elements, which is what a
descent argument along `exists_basicOpen_refinement` needs.
`FormalSchemes/FormalLineTwoChartCover.lean` is this construction at `R = ℤ⟦X⟧` with the two
elements `2`, `3`; this file is the general case, and the two agree field by field.

## The transparency accommodation

The `covers` field compares a point of `(FormalScheme.Spf I).toPresheafedSpace` with a point of
`FormalSpectrum I`. The two are `rfl` but not at `instances` transparency, which is what instance
search and `rw` work at, so the definition carries
`set_option backward.isDefEq.respectTransparency false`. Measured independently three times on
this tree, most recently by the two-chart cover named above.

## The adic hypothesis

`IsAdicRing (awayCompletionIdeal I (r i))` enters as an **instance hypothesis** rather than being
derived inside, because it appears in the *type* of the pieces: `FormalScheme.Spf` of the away
completion cannot be spelled without it. This is the shape `AdicOnSections.lean` and
`ThickeningChartSpfHom.lean` already use; a caller with `hI : I.FG` discharges it with
`FormalSpectrum.isAdicRing_awayCompletionIdeal`.

## Main definitions and results

* `FormalSpectrum.exists_mem_basicOpen_of_iSup_eq_top`: the pointwise form of the covering
  hypothesis.
* `FormalSpectrum.basicOpenCover`: the cover.
* `FormalSpectrum.basicOpenCover_cmap`: its cover maps are the basic-open charts, on the nose.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1, §10.4, §10.6.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable {ι : Type u} (r : ι → R)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The covering hypothesis, pointwise.** A family of basic opens whose supremum is `⊤` contains
every point of `|Spf R|` in one of its members. -/
theorem exists_mem_basicOpen_of_iSup_eq_top (hcov : (⨆ i, basicOpen I (r i)) = ⊤)
    (x : FormalSpectrum I) : ∃ i, x ∈ basicOpen I (r i) :=
  Opens.mem_iSup.mp (by rw [hcov]; trivial)

set_option linter.style.setOption false in
-- The `covers` field compares a point of `(FormalScheme.Spf I).toPresheafedSpace` with a point of
-- `FormalSpectrum I`; the two are `rfl` but not at `instances` transparency. See the module
-- docstring.
set_option backward.isDefEq.respectTransparency false in
/-- **`Spf R` covered by the basic-open charts of a covering family of elements.** The piece over
`i` is the affine formal scheme `Spf R{1/r i}`, included by `basicOpenChart`, and the point chosen
for `x` is the one `exists_mem_basicOpen_of_iSup_eq_top` produces. -/
def basicOpenCover (hI : I.FG) [∀ i, IsAdicRing (awayCompletionIdeal I (r i))]
    (hcov : (⨆ i, basicOpen I (r i)) = ⊤) :
    FormalScheme.OpenCover (FormalScheme.Spf I) where
  J := ι
  obj i := FormalScheme.Spf (awayCompletionIdeal I (r i))
  map i := FormalScheme.Hom.mk (basicOpenChart I (r i))
  f x := (exists_mem_basicOpen_of_iSup_eq_top I r hcov x).choose
  covers x :=
    (range_mapTop_basicOpen I _ hI).ge
      (exists_mem_basicOpen_of_iSup_eq_top I r hcov x).choose_spec
  isOpenImmersion i := isOpenImmersion_basicOpenChart I (r i) hI

/-- **The cover maps are the basic-open charts.** True by `rfl`; recorded because every consumer
has to rewrite `(basicOpenCover …).cmap i` into a statement about `basicOpenChart`, and because
`cmap` goes through `FormalScheme.Hom.mk`, which is exactly the sort of wrapper that can quietly
stop being definitional. -/
@[simp]
theorem basicOpenCover_cmap (hI : I.FG) [∀ i, IsAdicRing (awayCompletionIdeal I (r i))]
    (hcov : (⨆ i, basicOpen I (r i)) = ⊤) (i : ι) :
    (basicOpenCover I r hI hcov).cmap i = basicOpenChart I (r i) :=
  rfl

end FormalSpectrum

end
