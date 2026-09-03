import FormalSchemes.AdicCofinalOpenImmersion
import FormalSchemes.StructureSheafSections
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

set_option linter.style.header false

/-!
# Opens of `Spf R` whose infinitesimal thickenings are affine

`FormalSchemes.AdicCofinalOpenImmersion` reduces the adicity of an affine open immersion of formal
spectra to one containment, `J ≤ √(I · B)` — its **openness half** — and records a sketch of the
only route anyone has proposed for it:

> Write `B` as the inverse limit of `Bₙ = Γ (U, O_{Spec (R ⧸ Iⁿ)})`. If `U` is an affine open of
> `Spec (R ⧸ I)` then each `Uₙ` is affine, so the transition maps `Bₙ₊₁ → Bₙ` are surjective,
> `B ↠ Bₙ`, and `ker (Bₙ₊₁ → Bₙ) = Iⁿ · Bₙ₊₁`. Successive approximation against a finite
> generating set of `I` then gives `ker (B ↠ B₁) = I · B` on the nose.

and names its missing input as *"that the reduction of the open is an affine **scheme**, not merely
a quasi-compact spectral space"*, "not currently derivable on this tree from
`LocallyRingedSpace.IsOpenImmersion` alone". This file supplies the hypothesis in the form the
sketch consumes, and proves the first two of its three inputs from it. **It does not prove the
openness half**, and nothing here should be read as claiming it.

**Status.** The quoted "not currently derivable" is superseded.
`FormalSpectrum.hasAffineThickenings_opensRange`
(`FormalSchemes.AffineThickeningsOpenImmersion`) proves that the range of an arbitrary affine open
immersion of formal spectra has affine thickenings, with no hypothesis at all. Everything this
file states about *itself* is unchanged — the hypothesis is still a hypothesis here, and this file
still does not prove the openness half — but the hypothesis is no longer an open question, and
the paragraph below headed "Why at every level" has one sentence that the later file refutes and
that is corrected in place.

## The affineness is a predicate, not data

The tree's standing convention, in `FormalSchemes.SpfHomScheme`,
`FormalSchemes.ThickeningChartSpfHom`, `FormalSchemes.SpfHomOfFamily` and
`FormalSchemes.IndSchemeColimitEquivLRS`, is that an affine identification of an open of a *bare*
`LocallyRingedSpace` has to be carried as **data** — a ring together with an isomorphism — because
`IsAffineOpen` is a predicate on the opens of a `Scheme` and a bare locally ringed space is not
one. That convention is right in general and does **not** apply here: `FormalSpectrum I` is
*definitionally* `PrimeSpectrum (R ⧸ I)` (`FormalSchemes.FormalSpectrum`), which is the carrier of
the scheme `Spec (R ⧸ I)`, so an `Opens (FormalSpectrum I)` **is** a `(Spec (R ⧸ I)).Opens` and
`IsAffineOpen` applies to it with no bridging at all. The same holds at every infinitesimal
thickening, `thickeningOpen I n U` being an open of `Spec (R ⧸ I ^ (n + 1))`. So the hypothesis can
be a `Prop` about the open subset, as `HasAffineThickenings` is, and a theorem carrying it is a
genuine conditional rather than a statement about extra structure.

## Why at every level, rather than at the reduction only

`HasAffineThickenings I U` asks for `thickeningOpen I n U` to be affine for **every** `n`, not just
for `n = 0`. Deducing the former from the latter is the statement that a nilpotent thickening of an
affine open is affine, whose standard proof is Serre's cohomological criterion, which Mathlib does
not have. The elementary criterion it does have,
`AlgebraicGeometry.isAffine_of_isAffineOpen_basicOpen` (Stacks 01QF), cannot be substituted: it
needs `Ideal.span s = ⊤` in `Γ (X, ⊤)`, and a cover of `X` by its own basic opens does **not** give
that when `X` is not already affine — `𝔸² ∖ {0}` is covered by `D(x) ∪ D(y)` while `span {x, y}` is
not `⊤` in `k[x, y]`.

That much is right. The sentence that used to follow it — *"recovering the span is exactly the
surjectivity of `Γ (Uₙ) → Γ (U₀)`, i.e. the statement one is trying to prove"* — is **false**, and
`FormalSchemes.AffineThickeningsOpenImmersion` is the refutation. The span does not have to be
recovered at the level the criterion is applied at: a ring map carries a spanning family to a
spanning family, so a span in `Γ (U, O_{Spf R})` pushes forward to every `Γ (Uₙ)` at once through
`FormalSpectrum.sectionsPi`, and no surjectivity is involved. What the span needs is a source, and
for the range of an open immersion the source is `B` — see
`FormalSpectrum.span_globalSectionsMap_eq_top`. `𝔸² ∖ {0}` is not a counterexample to *that*
argument because it is not the range of an open immersion from a formal spectrum.

Asking at every level costs nothing wherever the tree can supply the hypothesis at all:
`hasAffineThickenings_top` and `hasAffineThickenings_basicOpen` are unconditional, and
`hasAffineThickenings_opensRange_of_range_eq_basicOpenChart` covers precisely the case in which
`FormalSpectrum.isCofinal_map_of_range_eq_basicOpenChart` already settles the openness half. So the
hypothesis is not vacuous, and it does not exclude the one case that is known.

## What the hypothesis buys

* `FormalSpectrum.surjective_stepSheafHom_app`: the transition maps of the tower of sections,
  `Γ (U, thickeningSheaf I (n + 1)) → Γ (U, thickeningSheaf I n)`, are **surjective**. The
  transition is `StructureSheaf.comap` along `R ⧸ I ^ (n + 2) ↠ R ⧸ I ^ (n + 1)`
  (`FormalSpectrum.stepSheafHom_hom_app`), `Spec` of a surjection is a closed immersion, and a
  closed immersion has surjective `Scheme.Hom.app` at an affine open of the target.
* `FormalSpectrum.surjective_sectionsPi_zero`: therefore
  `Γ (U, O_{Spf R}) ↠ Γ (U, thickeningSheaf I 0)`, the **reduction map on sections is surjective**.
  `FormalSpectrum.sectionsLimitIso` (`FormalSchemes.StructureSheafSections`) presents the left-hand
  side as the limit of that tower, and a sequential limit of surjections in a concrete category
  whose forgetful functor preserves sequential limits surjects onto its bottom level.

Those are the sketch's first two inputs, `Bₙ₊₁ ↠ Bₙ` and `B ↠ B₀`.

## What is deliberately not here

* **The third input**, `ker (Bₙ₊₁ → Bₙ) = Iⁿ⁺¹ · Bₙ₊₁`, and the successive approximation that turns
  the three into `ker (B ↠ B₀) = I · B`. That kernel is the sections over `Uₙ₊₁` of the ideal sheaf
  of the closed immersion, and identifying it with the extension of `Iⁿ⁺¹` needs quasi-coherence,
  which is not used anywhere in this file.
* **Any claim that `HasAffineThickenings` holds for an arbitrary open immersion of formal spectra.**
  It does hold — `FormalSpectrum.hasAffineThickenings_opensRange` — but that is proved in
  `FormalSchemes.AffineThickeningsOpenImmersion`, downstream of this file and of
  `FormalSchemes.AdicOpennessHalf`, and not here. What this file contributes to it is the
  observation that the affineness is a **predicate** rather than data, which is what makes the
  statement expressible at all. The openness half `J ≤ √(I · B)` is untouched here, and so is
  everything in `FormalSchemes.AdicCofinalOpenImmersion`.

## Main definitions

* `FormalSpectrum.HasAffineThickenings I U`: every `thickeningOpen I n U` is an affine open of
  `Spec (R ⧸ I ^ (n + 1))`.
* `FormalSpectrum.sectionsPi`: the level-`n` component
  `Γ (U, O_{Spf R}) ⟶ Γ (U, thickeningSheaf I n)`.

## Main results

* `AlgebraicGeometry.surjective_structureSheaf_comap`: `StructureSheaf.comap` along a surjection is
  surjective over an affine open.
* `FormalSpectrum.HasAffineThickenings.isAffineOpen`: the hypothesis unpacked at one level.
* `FormalSpectrum.hasAffineThickenings_top`, `FormalSpectrum.hasAffineThickenings_basicOpen`,
  `FormalSpectrum.hasAffineThickenings_of_range_eq_basicOpenChart`,
  `FormalSpectrum.hasAffineThickenings_opensRange_of_range_eq_basicOpenChart`: the hypothesis
  holds unconditionally on `⊤`, on every basic open, and on the range of any open immersion whose
  range is that of a basic-open chart. The range is taken as
  `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.opensRange`, which
  `FormalSchemes.OpenImmersionIsoOfRangeEq` already provides at the locally-ringed-space level.
* `FormalSpectrum.surjective_stepSheafHom_app`, `FormalSpectrum.surjective_sectionsPi_zero`: the
  tower is surjective, and so is the reduction map on sections.
* `FormalSpectrum.surjective_sectionsPi_zero_top`,
  `FormalSpectrum.surjective_sectionsPi_zero_basicOpen`: the two hypothesis-free instances of that
  surjection.
## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.12.
* [The Stacks Project, Tag 01QF](https://stacks.math.columbia.edu/tag/01QF).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

/-- If `φ : A ⟶ C` is surjective then over an **affine** open `V ⊆ Spec A` the induced map on
sections `StructureSheaf.comap` is surjective, `W` being the preimage of `V`.

`Spec φ` is a closed immersion (`AlgebraicGeometry.IsClosedImmersion.spec_of_surjective`), and a
closed immersion has surjective `Scheme.Hom.app` at every affine open of its target
(`AlgebraicGeometry.Scheme.Hom.app_surjective`); that `(Spec.map φ).app V` *is*
`StructureSheaf.comap φ V (φ ⁻¹ V)` holds by definition.

Affineness of `V` is not decoration: for a general open of `Spec A` the map on sections need not be
surjective, which is the whole reason `FormalSpectrum.HasAffineThickenings` is a hypothesis. -/
theorem surjective_structureSheaf_comap {A C : CommRingCat} (φ : A ⟶ C)
    (hφ : Function.Surjective φ.hom) (V : Opens (PrimeSpectrum A))
    (hV : IsAffineOpen (X := Spec A) V) {W : Opens (PrimeSpectrum C)}
    (hW : W = (Opens.map (Spec.topMap φ)).obj V)
    (h : (W : Set (PrimeSpectrum C)) ⊆ PrimeSpectrum.comap φ.hom ⁻¹' (V : Set (PrimeSpectrum A))) :
    Function.Surjective (StructureSheaf.comap φ.hom V W h) := by
  subst hW
  haveI : IsClosedImmersion (Spec.map φ) := IsClosedImmersion.spec_of_surjective φ hφ
  exact Scheme.Hom.app_surjective (Spec.map φ) V hV

end AlgebraicGeometry

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

/-- An open `U ⊆ Spf R` **has affine thickenings** if for every `n` the corresponding open
`thickeningOpen I n U` of the `n`-th infinitesimal thickening `Spec (R ⧸ I ^ (n + 1))` is an affine
open *of that scheme*.

This is a predicate and not data: `FormalSpectrum I` is definitionally `PrimeSpectrum (R ⧸ I)`, so
an open of `Spf R` is an open of a scheme and `IsAffineOpen` applies to it directly. See the module
docstring for why it is stated at every level rather than at the reduction alone. -/
def HasAffineThickenings (U : Opens (FormalSpectrum I)) : Prop :=
  ∀ n : ℕ, IsAffineOpen (X := Spec (CommRingCat.of (R ⧸ I ^ (n + 1)))) (thickeningOpen I n U)

variable {I}

omit [TopologicalSpace R] [IsAdicRing I] in
theorem HasAffineThickenings.isAffineOpen {U : Opens (FormalSpectrum I)}
    (hU : HasAffineThickenings I U) (n : ℕ) :
    IsAffineOpen (X := Spec (CommRingCat.of (R ⧸ I ^ (n + 1)))) (thickeningOpen I n U) :=
  hU n

variable (I)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- `Spf R` itself has affine thickenings: every `thickeningOpen I n ⊤` is `⊤`. -/
theorem hasAffineThickenings_top : HasAffineThickenings I ⊤ := fun n => by
  rw [thickeningOpen_top]
  exact isAffineOpen_top _

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Every basic open of `Spf R` has affine thickenings**, unconditionally: `thickeningOpen`
carries `D(f)` to `D(f mod I ^ (n + 1))` (`FormalSpectrum.thickeningOpen_basicOpen`), and a basic
open of an affine scheme is affine. -/
theorem hasAffineThickenings_basicOpen (f : R) :
    HasAffineThickenings I (basicOpen I f) := fun n => by
  rw [thickeningOpen_basicOpen]
  exact IsAffineOpen.Spec_basicOpen _

variable {I}

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The tower of sections over an open with affine thickenings has surjective transition maps.**

Over `U` the transition map of the tower is `StructureSheaf.comap` along the surjection
`R ⧸ I ^ (n + 2) ↠ R ⧸ I ^ (n + 1)` (`FormalSpectrum.stepSheafHom_hom_app`), taken between the
opens `thickeningOpen I (n + 1) U` and `thickeningOpen I n U`, which correspond under that
surjection (`FormalSpectrum.map_topMap_thickeningOpen`). The hypothesis is used exactly once, at
level `n + 1`, to make the open of the ambient thickening affine. -/
theorem surjective_stepSheafHom_app {U : Opens (FormalSpectrum I)}
    (hU : HasAffineThickenings I U) (n : ℕ) :
    Function.Surjective ((stepSheafHom I n).hom.app (op U)).hom := by
  rw [stepSheafHom_hom_app]
  exact surjective_structureSheaf_comap (stepRingHom I n)
    (Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) _
    (hU (n + 1)) (map_topMap_thickeningOpen I n U).symm _

/-- The level-`n` component of the structure sheaf of `Spf R`, on sections over `U`: the map
`Γ (U, O_{Spf R}) ⟶ Γ (U, thickeningSheaf I n)`, i.e. the projection of the defining limit. -/
def sectionsPi (I : Ideal R) [IsAdicRing I] (n : ℕ) (U : Opens (FormalSpectrum I)) :
    (structureSheaf I).presheaf.obj (op U) ⟶ (thickeningSheaf I n).presheaf.obj (op U) :=
  (limit.π (structureSheafFunctor I) ⟨n⟩).hom.app (op U)

/-- **Sections of `O_{Spf R}` over an open with affine thickenings surject onto sections of its
reduction.** This is the sketch's `B ↠ B₀`.

`FormalSpectrum.sectionsLimitIso` presents `Γ (U, O_{Spf R})` as the limit of the tower
`n ↦ Γ (U, thickeningSheaf I n)`, whose transition maps are surjective by
`FormalSpectrum.surjective_stepSheafHom_app`; a sequential limit of surjections in a concrete
category whose forgetful functor preserves sequential limits surjects onto its bottom level
(`CategoryTheory.Limits.Concrete.surjective_π_app_zero_of_surjective_map`). -/
theorem surjective_sectionsPi_zero {U : Opens (FormalSpectrum I)}
    (hU : HasAffineThickenings I U) :
    Function.Surjective (sectionsPi I 0 U).hom := by
  have hstep : ∀ n : ℕ, Function.Surjective
      ((structureSheafFunctor I ⋙ sectionsFunctor I (op U)).map (homOfLE (Nat.le_succ n)).op) := by
    intro n
    have h : (structureSheafFunctor I ⋙ sectionsFunctor I (op U)).map
        (homOfLE (Nat.le_succ n)).op = (stepSheafHom I n).hom.app (op U) := by
      simp only [Functor.comp_map, structureSheafFunctor_map_succ]
      rfl
    rw [h]
    exact surjective_stepSheafHom_app hU n
  have hpi : Function.Surjective
      (limit.π (structureSheafFunctor I ⋙ sectionsFunctor I (op U)) ⟨0⟩) :=
    Concrete.surjective_π_app_zero_of_surjective_map (limit.isLimit _) hstep
  rw [show sectionsPi I 0 U = (sectionsLimitIso I (op U)).hom ≫
      limit.π (structureSheafFunctor I ⋙ sectionsFunctor I (op U)) ⟨0⟩ from
    (sectionsLimitIso_hom_π I (op U) 0).symm]
  exact hpi.comp (ConcreteCategory.bijective_of_isIso (sectionsLimitIso I (op U)).hom).surjective

variable (I)

/-- **Unconditional corollary at the top open**: global sections of `O_{Spf R}` surject onto
`R ⧸ I ^ 1`, the sections of the zeroth thickening sheaf over `⊤`. No hypothesis at all — `⊤` has
affine thickenings by `FormalSpectrum.hasAffineThickenings_top`. -/
theorem surjective_sectionsPi_zero_top : Function.Surjective (sectionsPi I 0 ⊤).hom :=
  surjective_sectionsPi_zero (hasAffineThickenings_top I)

/-- **Unconditional corollary on a basic open**: `Γ (D(f), O_{Spf R})` surjects onto
`Γ (D(f), thickeningSheaf I 0)`, which is the localization of `R ⧸ I ^ 1` away from `f`
(`FormalSpectrum.isLocalization_away_basicOpen_sections`). No hypothesis: a basic open has affine
thickenings by `FormalSpectrum.hasAffineThickenings_basicOpen`. -/
theorem surjective_sectionsPi_zero_basicOpen (f : R) :
    Function.Surjective (sectionsPi I 0 (basicOpen I f)).hom :=
  surjective_sectionsPi_zero (hasAffineThickenings_basicOpen I f)

variable {I}

section OpenImmersion

variable {B : Type u} [CommRing B] [TopologicalSpace B] {J : Ideal B} [IsAdicRing J]

omit [TopologicalSpace R] [IsAdicRing I] in
/-- An open of `Spf R` that is the range of a basic-open chart has affine thickenings. -/
theorem hasAffineThickenings_of_range_eq_basicOpenChart (hI : I.FG) (f : R)
    {U : Opens (FormalSpectrum I)}
    (hU : (U : Set (FormalSpectrum I)) = Set.range (basicOpenChart I f).base) :
    HasAffineThickenings I U := by
  have hUeq : U = basicOpen I f := Opens.ext (by rw [hU, range_basicOpenChart_base I f hI])
  rw [hUeq]
  exact hasAffineThickenings_basicOpen I f

omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace B] [IsAdicRing J] in
/-- **The hypothesis holds in the one case where the openness half is already known.**

`FormalSpectrum.isCofinal_map_of_range_eq_basicOpenChart` settles the cofinality, unconditionally,
for an open immersion whose range is that of a basic-open chart — for an arbitrary presentation of
that open. `HasAffineThickenings` holds there too, so the hypothesis this file introduces does not
exclude the one case the tree can discharge. -/
theorem hasAffineThickenings_opensRange_of_range_eq_basicOpenChart (hI : I.FG) (f : R)
    (m : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    [LocallyRingedSpace.IsOpenImmersion m]
    (hrange : Set.range m.base = Set.range (basicOpenChart I f).base) :
    HasAffineThickenings I (LocallyRingedSpace.IsOpenImmersion.opensRange m) :=
  hasAffineThickenings_of_range_eq_basicOpenChart hI f hrange

end OpenImmersion

end FormalSpectrum
