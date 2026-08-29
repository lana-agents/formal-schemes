import FormalSchemes.BasicOpenChart

set_option linter.style.header false

/-!
# The image of a basic open of a basic-open chart is a basic open

Let `(R, I)` be an adic ring with `I.FG` and let `f : R`. The basic open `D(f) ⊆ Spf R` is realised
by the affine chart `Spf R{1/f} → Spf R` (`FormalSchemes/BasicOpenChart.lean`), whose underlying map
is `FormalSpectrum.basicOpenChartBase I f`. This file proves that the chart carries basic opens to
basic opens: for `h : R{1/f}`, the image of `D(h) ⊆ Spf R{1/f}` is `D(f') ⊆ Spf R` for some
`f' : R`.

This is the formal-geometry analogue of
`AlgebraicGeometry.IsAffineOpen.basicOpen_basicOpen_is_basicOpen`
(`Mathlib/AlgebraicGeometry/AffineScheme.lean`), and it is the step that turns a *chain* of nested
basic opens into an *equality*, which is what `FormalSchemes/TwoChartBasicOpen.lean` consumes.

## Why this is not a completion-theoretic statement

`FormalSpectrum I` is `PrimeSpectrum (R ⧸ I)` by definition, and `FormalSpectrum.basicOpen I f` is
`PrimeSpectrum.basicOpen (Ideal.Quotient.mk I f)`; so the question of *which opens are basic* never
leaves `PrimeSpectrum`. The completion is invisible to it because the residue ring of the completed
localization is an honest localization of the residue ring:
`FormalSpectrum.awayCompletionResidueEquiv` identifies `R{1/f} ⧸ (I·R{1/f})` with
`(R ⧸ I)_{f mod I}`, and `FormalSpectrum.awayCompletionResidueEquiv_comp_residueRingHom` identifies
the chart's residue map with the localization map. Everything below is therefore a statement about
`IsLocalization.Away`, transported once.

In particular no identification of `R{1/f}` with a completed localization of a *different*
presentation is needed: the away-of-away algebra isomorphisms of
`FormalSchemes/AwayCompletionNested.lean` do not appear here.

## Main results

* `PrimeSpectrum.basicOpen_eq_top_of_isUnit`: a unit cuts out the whole spectrum.
* `PrimeSpectrum.exists_image_comap_algebraMap_basicOpen`: the `Spec`-level statement — for an
  away-localization `S` of `A` at `r`, the image of `D(a)`, `a : S`, under
  `Spec S → Spec A` is `D(r * b)` for some `b : A`. This is the ring-theoretic content, and it is
  Mathlib's `basicOpen_basicOpen_is_basicOpen` argument with the scheme-theoretic wrapping removed.
* `FormalSpectrum.basicOpen_basicOpenChart_is_basicOpen`: the statement for `Spf`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1, §10.13.
* [The Stacks Project, Tag 01HR](https://stacks.math.columbia.edu/tag/01HR).
-/

noncomputable section

open TopologicalSpace

universe u

namespace PrimeSpectrum

variable {A : Type u} [CommRing A]

/-- A unit cuts out the whole prime spectrum: no prime contains a unit. -/
theorem basicOpen_eq_top_of_isUnit {v : A} (hv : IsUnit v) : basicOpen v = ⊤ := by
  apply Opens.ext
  rw [Opens.coe_top, Set.eq_univ_iff_forall]
  intro p
  exact fun hmem => p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hv)

/-- **The image of a basic open of an away-localization is a basic open.** If `S` is the
localization of `A` away from `r` and `a : S`, then `Spec S → Spec A` maps `D(a)` onto
`D(r * b)`, where `b : A` is any numerator of `a`.

This is the ring-theoretic core of `IsAffineOpen.basicOpen_basicOpen_is_basicOpen`, in the form the
formal-spectrum statement below consumes: the numerator `b` satisfies `D(a) = D(b/1)` because the
denominator is a unit, and `Spec S → Spec A` is a homeomorphism onto `D(r)`, so the image of the
preimage of `D(b)` is `D(b) ∩ D(r) = D(r * b)`. -/
theorem exists_image_comap_algebraMap_basicOpen (r : A) (S : Type u) [CommRing S] [Algebra A S]
    [IsLocalization.Away r S] (a : S) :
    ∃ b : A, comap (algebraMap A S) '' (basicOpen a : Set (PrimeSpectrum S))
      = (basicOpen (r * b) : Set (PrimeSpectrum A)) := by
  obtain ⟨⟨b, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers r) a
  refine ⟨b, ?_⟩
  -- The denominator is a unit, so `D(mk' b m) = D(b/1)`.
  have hmk : (basicOpen (IsLocalization.mk' S b m) : Set (PrimeSpectrum S))
      = (basicOpen (algebraMap A S b) : Set (PrimeSpectrum S)) := by
    rw [← IsLocalization.mk'_spec S b m, basicOpen_mul,
      basicOpen_eq_top_of_isUnit (IsLocalization.map_units S m)]
    simp
  have hpre : (basicOpen (algebraMap A S b) : Set (PrimeSpectrum S))
      = comap (algebraMap A S) ⁻¹' (basicOpen b : Set (PrimeSpectrum A)) := rfl
  rw [hmk, hpre, Set.image_preimage_eq_inter_range, localization_away_comap_range S r,
    basicOpen_mul, Opens.coe_inf, Set.inter_comm]

end PrimeSpectrum

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R) (f : R)

/-- The chart's residue ring map is the localization map `R ⧸ I → (R ⧸ I)_{f mod I}` conjugated by
`awayCompletionResidueEquiv`. This is `awayCompletionResidueEquiv_comp_residueRingHom` solved for
the residue map; `FormalSchemes/BasicOpenChart.lean` proves the same equation privately for its
own use. -/
theorem residueRingHom_basicOpenChart_eq (hI : I.FG) :
    residueRingHom I (awayCompletionIdeal I f) (awayCompletionHom I f)
        (le_comap_awayCompletionHom I f) =
      (awayCompletionResidueEquiv I f hI).symm.toRingHom.comp
        (algebraMap (R ⧸ I) (Localization.Away (Ideal.Quotient.mk I f))) := by
  rw [← awayCompletionResidueEquiv_comp_residueRingHom I f hI, ← RingHom.comp_assoc,
    RingEquiv.symm_toRingHom_comp_toRingHom, RingHom.id_comp]

/-- **The affine basic-open chart carries basic opens to basic opens.** For `h : R{1/f}` the image
of `D(h) ⊆ Spf R{1/f}` under the chart `Spf R{1/f} → Spf R` is `D(f') ⊆ Spf R` for some `f' : R`.

The formal-geometry analogue of
`AlgebraicGeometry.IsAffineOpen.basicOpen_basicOpen_is_basicOpen`. The proof passes to residue
rings, where the chart becomes `Spec (R ⧸ I)_{f mod I} → Spec (R ⧸ I)` up to the isomorphism
`awayCompletionResidueEquiv`, and applies
`PrimeSpectrum.exists_image_comap_algebraMap_basicOpen`; the completed localization plays no role
beyond that identification. -/
theorem basicOpen_basicOpenChart_is_basicOpen (hI : I.FG) (h : awayCompletion I f) :
    ∃ f' : R, basicOpenChartBase I f ''
        (basicOpen (awayCompletionIdeal I f) h : Set (FormalSpectrum (awayCompletionIdeal I f)))
      = (basicOpen I f' : Set (FormalSpectrum I)) := by
  set σ := awayCompletionResidueEquiv I f hI with hσ
  -- The chart is the comap of the residue map, which factors through the localization map.
  have hbase : basicOpenChartBase I f =
      PrimeSpectrum.comap (algebraMap (R ⧸ I) (Localization.Away (Ideal.Quotient.mk I f))) ∘
        PrimeSpectrum.comap σ.symm.toRingHom := by
    rw [basicOpenChartBase, map, show Ideal.quotientMap (awayCompletionIdeal I f)
        (awayCompletionHom I f) (le_comap_awayCompletionHom I f) =
      residueRingHom I (awayCompletionIdeal I f) (awayCompletionHom I f)
        (le_comap_awayCompletionHom I f) from rfl,
      residueRingHom_basicOpenChart_eq I f hI, PrimeSpectrum.comap_comp]
  -- `comap σ.symm` is the inverse homeomorphism of `comap σ`, so images along it are preimages.
  have hinv : ∀ x, PrimeSpectrum.comap σ.toRingHom
      (PrimeSpectrum.comap σ.symm.toRingHom x) = x := by
    intro x
    rw [← PrimeSpectrum.comap_comp_apply, RingEquiv.symm_toRingHom_comp_toRingHom]
    rfl
  have hinv' : ∀ y, PrimeSpectrum.comap σ.symm.toRingHom
      (PrimeSpectrum.comap σ.toRingHom y) = y := by
    intro y
    rw [← PrimeSpectrum.comap_comp_apply, RingEquiv.toRingHom_comp_symm_toRingHom]
    rfl
  have himg : PrimeSpectrum.comap σ.symm.toRingHom ''
      (basicOpen (awayCompletionIdeal I f) h : Set (FormalSpectrum (awayCompletionIdeal I f)))
      = (PrimeSpectrum.basicOpen
          (σ (Ideal.Quotient.mk (awayCompletionIdeal I f) h)) :
        Set (PrimeSpectrum (Localization.Away (Ideal.Quotient.mk I f)))) := by
    rw [Set.image_eq_preimage_of_inverse hinv hinv']
    rfl
  obtain ⟨b, hb⟩ := PrimeSpectrum.exists_image_comap_algebraMap_basicOpen
    (Ideal.Quotient.mk I f) (Localization.Away (Ideal.Quotient.mk I f))
    (σ (Ideal.Quotient.mk (awayCompletionIdeal I f) h))
  obtain ⟨f', hf'⟩ := exists_basicOpen_eq I (Ideal.Quotient.mk I f * b)
  refine ⟨f', ?_⟩
  have himg2 : basicOpenChartBase I f ''
      (basicOpen (awayCompletionIdeal I f) h : Set (FormalSpectrum (awayCompletionIdeal I f)))
      = PrimeSpectrum.comap (algebraMap (R ⧸ I) (Localization.Away (Ideal.Quotient.mk I f))) ''
        (PrimeSpectrum.basicOpen (σ (Ideal.Quotient.mk (awayCompletionIdeal I f) h)) :
          Set (PrimeSpectrum (Localization.Away (Ideal.Quotient.mk I f)))) := by
    rw [← himg, ← Set.image_comp]
    exact congrArg (fun g => g ''
      (basicOpen (awayCompletionIdeal I f) h : Set (FormalSpectrum (awayCompletionIdeal I f))))
      hbase
  rw [himg2, hb, hf']
  rfl

end FormalSpectrum
