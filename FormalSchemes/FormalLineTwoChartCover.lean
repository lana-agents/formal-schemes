import FormalSchemes.OpenCoverGlueMorphisms
import FormalSchemes.BasicOpenImmersionLRS
import FormalSchemes.ThickeningChartSpfHom

set_option linter.style.header false

/-!
# A two-piece open cover of `Spf ℤ⟦X⟧`, and the gluing combinator run on it

`FormalSchemes/OpenCoverGlueMorphisms.lean` builds `FormalScheme.OpenCover.glueMorphisms` in the
generality of an arbitrary open cover, and `FormalSchemes/GlueHomToSpf.lean` and
`FormalSchemes/GlobalSectionsHomGlue.lean` consume it. Neither exhibits a cover with **more than
one piece and a nonempty overlap**, and until one does, nothing checks that the compatibility
hypothesis of `glueMorphisms` is ever a real condition: over a one-piece cover it is a tautology,
and over disjoint pieces it never sees an overlap. This file supplies such a cover.

The cover is `FormalLineWitness.lean`'s `twoChart`: the basic opens `D(2)` and `D(3)` of
`|Spf ℤ⟦X⟧| = Spec ℤ`. That module already proves they cover (`exists_mem_twoChart`,
`iSup_twoChart`) and that neither is everything (`twoChart_ne_top`). This file adds the two facts a
witness for `glueMorphisms` needs on top of that — the pieces are *distinct*, and their *overlap is
nonempty* — assembles them into a `FormalScheme.OpenCover (FormalScheme.Spf ℤ⟦X⟧)`, and runs
`glueMorphisms_cmap` on it.

## Why this ring

`TwoAdicWitness.lean`'s `ℤ^` cannot serve: `|Spf ℤ^|` is a one-point space
(`TwoAdicDegeneracy.lean`), so every open cover of it has a member equal to `⊤` and every overlap
statement about it is vacuous. `ℤ⟦X⟧` is the witness on this tree whose formal spectrum is
infinite, and `D(2)`, `D(3)` is the smallest genuinely two-piece cover of it.

## What the cover is for beyond non-vacuity

It is also the shape umbrella 59's remaining assembly needs: a cover of `Spf R` by basic-open charts
`D(r)`, each of which is `Spf R{1/r}`. No cover on the tree had that shape when this file was
written — `AlgebraicGeometry.FormalScheme.affineCover`,
`AlgebraicGeometry.FormalScheme.OpenCover.ofAffineCharts`,
`AlgebraicGeometry.FormalScheme.liftedBasicCover` and the refined covers of the
`GeneralFibreProduct*` line all cover a *general* formal scheme from its local-affineness data —
and the general construction was a separate row. That row landed:
`FormalSpectrum.basicOpenCover` (`FormalSchemes.SpfBasicOpenCover`) is this construction at an
arbitrary `R` and an arbitrary family; that file's docstring records that the two agree field by
field. Neither module imports the other. This file is the construction at one
concrete `R` and one concrete pair of elements, and the two obligations it discharges
(`isOpenImmersion_basicOpenChart` for the maps, `range_mapTop_basicOpen` for the covering
condition) are the same two the general one discharges.

## Main definitions and results

* `FormalSpectrum.twoChart_ne`, `FormalSpectrum.twoChart_inf_ne_bot`: the two charts are distinct
  and their overlap is nonempty.
* `FormalScheme.OpenCover.formalLineTwoChartCover`: the cover.
* `FormalScheme.OpenCover.glueMorphisms_formalLineTwoChart_cmap`: the combinator run on it.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4, §10.6, §10.7.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology Polynomial

universe u

namespace FormalSpectrum

attribute [local instance] isAdicRing_formalLineIdeal

/-- **The two charts are distinct.** A prime of `ℤ` containing `2` gives a point outside `D(2)`,
and `exists_mem_twoChart` then puts that point in `D(3)`. Without this the cover below would be a
one-piece cover with a repeated index, and would witness nothing about `glueMorphisms`. -/
theorem twoChart_ne : twoChart true ≠ twoChart false := by
  obtain ⟨p, hp⟩ := exists_prime_mem 2 (by rw [Int.isUnit_iff]; decide)
  have hnot : ofPrimeInt p ∉ twoChart true := by
    rw [twoChart, if_pos rfl, mem_basicOpen_ofPrimeInt, map_ofNat, map_ofNat]
    exact fun hc => hc hp
  intro h
  obtain ⟨b, hb⟩ := exists_mem_twoChart (ofPrimeInt p)
  cases b with
  | true => exact hnot hb
  | false => exact hnot (h ▸ hb)

/-- **The two charts overlap.** The generic point of `Spec ℤ` — the prime `(0)` — lies in both,
since neither `2` nor `3` is zero. So the compatibility hypothesis of `glueMorphisms` at the cover
below is a condition over a nonempty formal scheme, which is what distinguishes this witness from a
cover by disjoint pieces. -/
theorem twoChart_inf_ne_bot : twoChart true ⊓ twoChart false ≠ ⊥ := by
  intro h
  have h2 : ofPrimeInt ⟨⊥, Ideal.isPrime_bot⟩ ∈ basicOpen formalLineIdeal 2 := by
    rw [mem_basicOpen_ofPrimeInt, map_ofNat, map_ofNat]; simp
  have h3 : ofPrimeInt ⟨⊥, Ideal.isPrime_bot⟩ ∈ basicOpen formalLineIdeal 3 := by
    rw [mem_basicOpen_ofPrimeInt, map_ofNat, map_ofNat]; simp
  have hmem : ofPrimeInt ⟨⊥, Ideal.isPrime_bot⟩ ∈ twoChart true ⊓ twoChart false := ⟨h2, h3⟩
  rw [h] at hmem
  exact hmem.elim

end FormalSpectrum

namespace AlgebraicGeometry.FormalScheme.OpenCover

open FormalSpectrum

attribute [local instance] isAdicRing_formalLineIdeal

/-- `ℤ⟦X⟧{1/2}` and `ℤ⟦X⟧{1/3}` are complete adic rings, uniformly in the chart index — which is
what lets `Spf` of them be spelled at all. Local, for the reason
`isAdicRing_awayCompletionIdeal`'s own docstring gives: it needs `I.FG`, which is not
synthesizable, so a global instance of this shape would be looked at by every unrelated search. -/
private theorem isAdicRing_twoChartRing (b : Bool) :
    IsAdicRing (awayCompletionIdeal formalLineIdeal (if b then 2 else 3)) :=
  isAdicRing_awayCompletionIdeal _ _ (polyXIdeal_fg.map _)

attribute [local instance] isAdicRing_twoChartRing

set_option linter.style.setOption false in
-- The `covers` field compares a point of `(Spf formalLineIdeal).toPresheafedSpace` with a point of
-- `FormalSpectrum formalLineIdeal`; the two are `rfl` but not at `instances` transparency, which is
-- the transparency instance search and `rw` work at. Same accommodation as `Gluing.lean` and
-- `OpenCoverGlueMorphisms.lean`.
set_option backward.isDefEq.respectTransparency false in
/-- **`D(2)` and `D(3)` as an open cover of `Spf ℤ⟦X⟧`**, by the two affine formal schemes
`Spf ℤ⟦X⟧{1/2}` and `Spf ℤ⟦X⟧{1/3}`.

The two structural obligations are exactly the two facts `BasicOpenImmersionLRS.lean` proves about
a basic-open chart: it is an open immersion (`isOpenImmersion_basicOpenChart`), and its range is
the basic open it is named after (`range_mapTop_basicOpen`). The covering condition is then
`exists_mem_twoChart`, and the index of the piece covering a point is the one that lemma chooses. -/
def formalLineTwoChartCover : OpenCover (FormalScheme.Spf formalLineIdeal) where
  J := Bool
  obj b := FormalScheme.Spf (awayCompletionIdeal formalLineIdeal (if b then 2 else 3))
  map b := FormalScheme.Hom.mk (basicOpenChart formalLineIdeal (if b then 2 else 3))
  f x := (exists_mem_twoChart x).choose
  covers x := by
    have h := (exists_mem_twoChart x).choose_spec
    rw [twoChart] at h
    exact (range_mapTop_basicOpen formalLineIdeal
      (if (exists_mem_twoChart x).choose then 2 else 3) (polyXIdeal_fg.map _)).ge h
  isOpenImmersion b := isOpenImmersion_basicOpenChart formalLineIdeal _ (polyXIdeal_fg.map _)

/-- **The gluing combinator, run on a genuinely two-piece cover.** Gluing the two chart inclusions
`Spf ℤ⟦X⟧{1/2} ⟶ Spf ℤ⟦X⟧` and `Spf ℤ⟦X⟧{1/3} ⟶ Spf ℤ⟦X⟧` returns the identity of `Spf ℤ⟦X⟧`.

The equation is `glueMorphisms_cmap`; what makes recording the instance worthwhile is the cover.
The two pieces are distinct (`twoChart_ne`), their overlap is nonempty (`twoChart_inf_ne_bot`), and
neither is the whole space (`twoChart_ne_top`) — so the hypothesis of `glueMorphisms` is checked
here at a pair `i ≠ j` over a nonempty overlap, which is the situation the general statement is
about and the one a one-piece cover cannot exhibit. -/
theorem glueMorphisms_formalLineTwoChart_cmap :
    formalLineTwoChartCover.glueMorphisms formalLineTwoChartCover.cmap
        (fun _ _ => pullback.condition) =
      𝟙 (FormalScheme.Spf formalLineIdeal).toLocallyRingedSpace :=
  formalLineTwoChartCover.glueMorphisms_cmap

end AlgebraicGeometry.FormalScheme.OpenCover
