import FormalSchemes.SpfHomOfFamily
import FormalSchemes.SpecTwoPatchNonAffine

set_option linter.style.header false

/-!
# EGA I, 10.6.10 at a target that is not affine

`FormalSchemes/SpfHomOfFamily.lean` proves that `Spf R` is the colimit of its infinitesimal
thickenings for a locally ringed space `X` covered by affine opens, and runs the construction end
to end at `X = Spec ℤ`. Four rows on umbrella 59 closed with the same recorded gap: **`X` is affine
in every witness on the tree.**

That gap is real. The theorem's hypothesis is that the *opens* `U i` are affine, not that `X` is,
and an affine `X` cannot tell the two apart: at `X = Spec ℤ` the affine identifications `e i` can
all be read off a single global one. This file removes it, and the non-vacuity paragraph of
`SpfHomOfFamily.lean` has been rewritten to point here.

The target is the **affine line over `ℤ` with a doubled origin**,
`specDouble (X : ℤ[X]) = Spec ℤ[X] ∪_{D(X)} Spec ℤ[X]`, which
`FormalSchemes/SpecTwoPatchNonAffine.lean` proves is not separated and hence **not affine**
(`not_isAffine_specDouble_of_not_isUnit`). Its two charts are the affine open cover, and the
compatible family is the reduction family of the completion map `ℤ[X] → ℤ⟦X⟧` pushed into the
first chart. So the instantiation

```
existsUnique_hom_thickeningMap_nonAffine :
  ∃! g : Spf ℤ⟦X⟧ ⟶ specDouble (X : ℤ[X]), ∀ n, thickeningMap n ≫ g = nonAffineFamily n
```

exercises the covering situation on **both** sides at once: `|Spf ℤ⟦X⟧| ≃ Spec ℤ` is covered by two
proper basic opens (the source-side non-degeneracy `SpfHomOfFamily.lean` already had), and the
target is covered by two affine opens neither of which is the whole space, of a space that is
provably not a spectrum.

## Why the family goes through one chart

`nonAffineFamily` is `specFamily formalLineIdeal ℤ[X] (algebraMap ℤ[X] ℤ⟦X⟧)` — the family of
reductions of the completion map, which is the canonical compatible family into `Spec ℤ[X]` —
postcomposed with the `A`-chart `Spec ℤ[X] ⟶ specDouble X`. It is *not* a family into an affine
scheme in disguise: the glued morphism it produces lands in the non-affine target, and the
uniqueness clause is uniqueness there. Which of the two lifts through the charts the family picks
is a genuine choice, and it is the doubled origin that makes the two choices different
(`specTwoPatchSchemeι₀_base_ne_specTwoPatchSchemeι₁_base`).

## Main definitions and results

* `FormalSpectrum.nonAffineTarget`: the doubled affine line over `ℤ`, as a locally ringed space,
  with `FormalSpectrum.not_isAffine_nonAffineTarget`: **it is not affine.**
* `FormalSpectrum.nonAffineChart`, `FormalSpectrum.nonAffineOpen`,
  `FormalSpectrum.nonAffineChartIso`: the two-chart affine open cover of the target, with
  `FormalSpectrum.iSup_nonAffineOpen`.
* `FormalSpectrum.nonAffineOpen_ne`, `FormalSpectrum.nonAffineOpen_true_ne_top`,
  `FormalSpectrum.nonAffineOpen_ne_bot`: the cover is genuinely two-piece and neither piece is
  empty.
* `FormalSpectrum.nonAffineFamily`, `FormalSpectrum.nonAffineFamily_compat`: the compatible
  family.
* `FormalSpectrum.existsUnique_hom_thickeningMap_nonAffine`: **the capstone at a non-affine
  target.**

## Scope

`nonAffineOpen_true_ne_top` is stated for the `B`-chart only. Properness of the `A`-chart's range
is just as true and is proved the same way, but the input it needs — the mirror of
`specTwoPatchι₀_base_notMem_range_specTwoPatchι₁` with the two indices exchanged — is not on the
tree, and adding it means a second range computation for the glue datum's `f ⟨true⟩ ⟨false⟩` in
`SpecTwoPatchNonAffine.lean`. That is a separate row; nothing here depends on it, because
`nonAffineOpen_ne` already rules out the one-piece reading of the cover.

Nothing here computes the glued morphism. `SpfHomOfFamily.lean`'s `spfHomOfFamily` needs the
source-side chart data spelled out; the `∃!` form is what makes the point about the target, and the
morphism it asserts is unique.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.10), §10.8.
* [The Stacks Project, Tag 01KP](https://stacks.math.columbia.edu/tag/01KP) (the line with doubled
  origin).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Polynomial

namespace FormalSpectrum

section NonAffineWitness

attribute [local instance] isAdicRing_formalLineIdeal

/-! ### The target -/

/-- **The affine line over `ℤ` with a doubled origin, as a locally ringed space.** This is the
target the capstone is instantiated at; it is a `Scheme`, but the capstone takes a bare locally
ringed space and supplies the affine data itself. -/
abbrev nonAffineTarget : LocallyRingedSpace.{0} :=
  (specDouble (X : ℤ[X])).toLocallyRingedSpace

/-- **The target is not affine.** `SpecTwoPatchNonAffine.lean` at `A = ℤ[X]`, `a = X`: `ℤ[X]` is a
domain and `X` is a non-zero non-unit, so the doubled `Spec ℤ[X]` is not separated, hence not the
spectrum of a ring. -/
theorem not_isAffine_nonAffineTarget : ¬ IsAffine (specDouble (X : ℤ[X])) :=
  not_isAffine_specDouble_of_not_isUnit (X : ℤ[X]) X_ne_zero not_isUnit_X

/-- The origin of the affine line over `ℤ`: the prime `(X) ⊆ ℤ[X]`. It is prime because `X` is
(`Polynomial.prime_X`, `ℤ` being a domain), and it is the point that gets doubled. -/
def originInt : PrimeSpectrum ℤ[X] :=
  ⟨Ideal.span {(X : ℤ[X])}, (Ideal.span_singleton_prime X_ne_zero).mpr prime_X⟩

theorem X_mem_originInt : (X : ℤ[X]) ∈ originInt.asIdeal :=
  Ideal.mem_span_singleton_self _

/-! ### The two-chart affine open cover -/

/-- The two charts of the doubled line, indexed by `Bool`: `false` is the `A`-chart and `true` the
`B`-chart, matching `specTwoPatchSchemeCover`'s `ULift Bool` indexing. Both are `Spec ℤ[X]`. -/
def nonAffineChart : Bool → (Spec (CommRingCat.of ℤ[X]) ⟶ specDouble (X : ℤ[X]))
  | true => specTwoPatchSchemeι₁ (X : ℤ[X]) X (RingEquiv.refl _)
  | false => specTwoPatchSchemeι₀ (X : ℤ[X]) X (RingEquiv.refl _)

instance nonAffineChart_isOpenImmersion (b : Bool) : IsOpenImmersion (nonAffineChart b) := by
  cases b
  · exact inferInstanceAs (IsOpenImmersion (specTwoPatchSchemeι₀ (X : ℤ[X]) X (RingEquiv.refl _)))
  · exact inferInstanceAs (IsOpenImmersion (specTwoPatchSchemeι₁ (X : ℤ[X]) X (RingEquiv.refl _)))

/-- The two affine opens of the target: the ranges of the two charts. -/
def nonAffineOpen : Bool → Opens nonAffineTarget.toTopCat := fun b => (nonAffineChart b).opensRange

/-- **The two charts cover the target**, which is `specTwoPatchScheme_jointly_surjective`. This is
the hypothesis the capstone takes in place of chart data. -/
theorem iSup_nonAffineOpen : (⨆ b, nonAffineOpen b) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  refine Opens.mem_iSup.mpr ?_
  rcases specTwoPatchScheme_jointly_surjective (X : ℤ[X]) X (RingEquiv.refl _) x with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

/-- The image of the origin under the `A`-chart: the point of the doubled line that the `B`-chart
misses. -/
private theorem doubledPoint_mem_false :
    (specTwoPatchSchemeι₀ (X : ℤ[X]) X (RingEquiv.refl _)).base originInt ∈ nonAffineOpen false :=
  ⟨originInt, rfl⟩

/-- **The two pieces of the cover are different opens.** The doubled origin, taken from the
`A`-chart, lies in the `A`-chart's range and — by
`specTwoPatchSchemeι₀_base_notMem_range_specTwoPatchSchemeι₁` — outside the `B`-chart's. -/
theorem nonAffineOpen_ne : nonAffineOpen false ≠ nonAffineOpen true := by
  intro h
  have hmem := doubledPoint_mem_false
  rw [h] at hmem
  exact specTwoPatchSchemeι₀_base_notMem_range_specTwoPatchSchemeι₁ (X : ℤ[X]) X
    (RingEquiv.refl _) X_mem_originInt hmem

/-- **The `B`-chart is a proper open** of the target: it misses the `A`-chart's copy of the doubled
origin. In particular the cover is not the degenerate one-piece cover by `⊤`. -/
theorem nonAffineOpen_true_ne_top : nonAffineOpen true ≠ ⊤ := by
  intro h
  have hmem : (specTwoPatchSchemeι₀ (X : ℤ[X]) X (RingEquiv.refl _)).base originInt ∈
      nonAffineOpen true := by rw [h]; trivial
  exact specTwoPatchSchemeι₀_base_notMem_range_specTwoPatchSchemeι₁ (X : ℤ[X]) X
    (RingEquiv.refl _) X_mem_originInt hmem

/-- **Neither piece is empty**: each contains the image of the origin under its own chart. -/
theorem nonAffineOpen_ne_bot (b : Bool) : nonAffineOpen b ≠ ⊥ := by
  intro h
  have hmem : (nonAffineChart b).base originInt ∈ nonAffineOpen b := ⟨originInt, rfl⟩
  rw [h] at hmem
  exact hmem.elim

/-- The coordinate rings of the two affine opens. Both charts are `Spec ℤ[X]`, so both are `ℤ[X]`
— the two opens are nevertheless different (`nonAffineOpen_ne`), which is exactly what a gluing
does. -/
def nonAffineChartRing : Bool → Type := fun _ => ℤ[X]

instance (b : Bool) : CommRing (nonAffineChartRing b) := inferInstanceAs (CommRing ℤ[X])

/-- **The affine identifications**, in the shape the capstone's data `e` is taken in: an open
immersion is an isomorphism onto its range (`Scheme.Hom.isoOpensRange`), and
`Scheme.forgetToLocallyRingedSpace` takes `(nonAffineChart b).opensRange.toScheme` to
`nonAffineTarget.restrict (nonAffineOpen b).isOpenEmbedding` definitionally — the same
no-transport argument `openTwoIsoSpecLRS` (`ThickeningChartSpfHom.lean`) makes. -/
def nonAffineChartIso (b : Bool) :
    nonAffineTarget.restrict (nonAffineOpen b).isOpenEmbedding ≅
      Spec.locallyRingedSpaceObj (CommRingCat.of (nonAffineChartRing b)) :=
  Scheme.forgetToLocallyRingedSpace.mapIso (nonAffineChart b).isoOpensRange.symm

/-! ### The compatible family -/

/-- The canonical compatible family into the `A`-chart `Spec ℤ[X]`: the reductions of the
completion map `ℤ[X] → ℤ⟦X⟧`, i.e. `Spec` of `ℤ[X] → ℤ⟦X⟧ ⧸ (X)ⁿ⁺¹`. Compatibility is
`specMap_mk_comp_compatible`, packaged by `specFamily`. -/
def nonAffineFamilyAffine : ThickeningFamily formalLineIdeal ℤ[X] :=
  specFamily formalLineIdeal ℤ[X] (algebraMap ℤ[X] (AdicCompletion polyXIdeal ℤ[X]))

/-- **The compatible family into the non-affine target**: the family above, pushed into the doubled
line along the `A`-chart. -/
def nonAffineFamily (n : ℕ) :
    Spec.locallyRingedSpaceObj (CommRingCat.of
        (AdicCompletion polyXIdeal ℤ[X] ⧸ formalLineIdeal ^ (n + 1))) ⟶ nonAffineTarget :=
  nonAffineFamilyAffine.1 n ≫ (nonAffineChart false).toLRSHom

/-- …and it is compatible: postcomposing a compatible family with a fixed morphism preserves the
tower equations. -/
theorem nonAffineFamily_compat (n : ℕ) :
    Spec.locallyRingedSpaceMap (stepRingHom formalLineIdeal n) ≫ nonAffineFamily (n + 1) =
      nonAffineFamily n := by
  rw [nonAffineFamily, nonAffineFamily, ← Category.assoc, nonAffineFamilyAffine.2 n]

/-! ### The capstone at a non-affine target -/

/-- **EGA I, 10.6.10 at a target that is not affine.** `Spf ℤ⟦X⟧` is the colimit of its
infinitesimal thickenings as a functor into the affine line over `ℤ` with a doubled origin — a
locally ringed space that is covered by two proper affine opens and is provably not the spectrum
of a ring (`not_isAffine_nonAffineTarget`).

Nothing but the cover of the target is supplied: the basic opens of `|Spf ℤ⟦X⟧|`, the index map and
the refinement containments are produced inside by `exists_basicOpen_refinement`, exactly as in
`existsUnique_hom_thickeningMap_formalLine`. This is the witness the non-vacuity paragraph of
`SpfHomOfFamily.lean` says is missing, and like that one it is hypothesis-free. -/
theorem existsUnique_hom_thickeningMap_nonAffine :
    ∃! g : locallyRingedSpaceObj formalLineIdeal ⟶ nonAffineTarget,
      ∀ n : ℕ, thickeningMap formalLineIdeal n ≫ g = nonAffineFamily n :=
  existsUnique_hom_thickeningMap formalLineIdeal nonAffineFamily nonAffineFamily_compat
    (polyXIdeal_fg.map _) nonAffineOpen iSup_nonAffineOpen nonAffineChartRing nonAffineChartIso

end NonAffineWitness

end FormalSpectrum

end
