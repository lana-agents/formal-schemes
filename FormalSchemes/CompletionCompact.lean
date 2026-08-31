import FormalSchemes.CompletionGlueTwoPatch
import FormalSchemes.GlueDataCompact

set_option linter.style.header false

/-!
# The formal completion is quasi-compact (EGA I, 10.8)

`FormalSchemes/Completion.lean` builds `formalCompletion R I = Spf R^`, the completion of `Spec R`
along `V(I)`, and `FormalSchemes/CompletionGlueTwoPatch.lean` glues two of them into
`completionTwoPatch`, the completion of the two-chart scheme
`Spec A ∪_{D(a) ≅ D(b)} Spec B`. This file records that both are **quasi-compact**.

The affine case is free once the coercions are spelled out: `FormalSpectrum I` is by definition
`PrimeSpectrum (R ⧸ I)` and is already known to be a spectral space
(`FormalSpectrum.instSpectralSpace`), hence quasi-compact. The glued case is
`FormalScheme.GlueData.compactSpace` (`FormalSchemes/GlueDataCompact.lean`) applied to the
two-element index of `completionTwoPatchFormalGlueData`.

This is the completion-side counterpart of `specTwoPatchScheme_compactSpace`
(`FormalSchemes/SpecTwoPatchScheme.lean`), which says the glued *scheme* is quasi-compact. Together
they say that both ends of the morphism `X_{/Y} ⟶ X` of `CompletionTwoPatchToScheme.lean` are
quasi-compact.

## Why the non-emptiness results are here

A `CompactSpace` instance on an empty space is vacuously true, so the compactness statements below
would be worth nothing without a witness that these spaces have points. `formalCompletion_nonempty`
and `completionTwoPatch_nonempty` supply that, and the closing `example` instantiates the whole
stack at `R = ℤ`, `I = (2)`, where the glued completion is provably nonempty.

## Main results

* `AlgebraicGeometry.formalCompletion_compactSpace`: `Spf R^` is quasi-compact.
* `AlgebraicGeometry.formalCompletion_nonempty`: it has points as soon as `R ⧸ I` is nontrivial,
  i.e. as soon as `I ≠ ⊤`, and `AlgebraicGeometry.formalCompletion_isEmpty` for the converse half —
  it is empty when `R ⧸ I` is trivial.
* `AlgebraicGeometry.completionTwoPatch_compactSpace`: the glued two-patch formal completion is
  quasi-compact, with `AlgebraicGeometry.completionTwoPatch_nonempty` for its non-emptiness.

## Implementation note

Neither `CompactSpace (formalCompletion R I hI).toLocallyRingedSpace` nor
`Finite (completionTwoPatchFormalGlueData …).toLocallyRingedSpaceGlueData.J` is found by
`inferInstance`, although the first is `CompactSpace (FormalSpectrum …)` and the second is
`Finite (ULift Bool)`. In both cases the two spellings are definitionally equal but not *reducibly*
so — the first through `FormalScheme`'s carrier coercion, the second through the
`GlueData.ofGlueData'` projection — and instance search works up to reducible transparency. Naming
the reduced form with `inferInstanceAs` is the fix; no transparency `set_option` is involved or
needed.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **The affine formal completion `Spf R^` is quasi-compact.** Its underlying space is
`FormalSpectrum (idealOfDefinition I)`, which is by definition a prime spectrum and is already
known to be a spectral space. -/
instance formalCompletion_compactSpace {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) :
    CompactSpace (formalCompletion R I hI).toLocallyRingedSpace :=
  haveI := AdicCompletion.isAdicRing_map I hI
  inferInstanceAs (CompactSpace (FormalSpectrum (AdicCompletion.idealOfDefinition I)))

/-- **`Spf R^` has points whenever `I ≠ ⊤`.** Its space is homeomorphic to `Spec (R ⧸ I)`
(`formalCompletion.homeo`), which is nonempty for a nontrivial quotient. Together with
`formalCompletion_compactSpace` this rules out the vacuous reading of quasi-compactness. -/
theorem formalCompletion_nonempty {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
    [Nontrivial (R ⧸ I)] : Nonempty (formalCompletion R I hI).toLocallyRingedSpace :=
  haveI := AdicCompletion.isAdicRing_map I hI
  ⟨(formalCompletion.homeo I hI).symm (Classical.arbitrary (PrimeSpectrum (R ⧸ I)))⟩

/-- **`Spf R^` is empty when `I = ⊤`.** The converse half of `formalCompletion_nonempty`, by the
same homeomorphism: the space is `Spec (R ⧸ I)`, and a trivial quotient has no primes. Consumed by
`AlgebraicGeometry.isEmpty_projectiveLine_chart_true`
(`FormalSchemes.ProjectiveLineCompletion`), where the closed subset being completed along misses
the second chart entirely. -/
theorem formalCompletion_isEmpty {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
    [Subsingleton (R ⧸ I)] : IsEmpty (formalCompletion R I hI).toLocallyRingedSpace :=
  haveI := AdicCompletion.isAdicRing_map I hI
  Function.isEmpty (formalCompletion.homeo I hI)

section TwoPatch

variable {A B : Type u} [CommRing A] [CommRing B] (I : Ideal A) (hI : I.FG) (a : A)
  (J : Ideal B) (hJ : J.FG) (b : B)
  (θ : Localization.Away a ≃+* Localization.Away b)
  (hθ : (I.map (algebraMap A (Localization.Away a))).map θ.toRingHom =
    J.map (algebraMap B (Localization.Away b)))

/-- The index type of the two-patch completion glue datum is finite, being `ULift Bool`. Stated
because instance search does not see through the `GlueData.ofGlueData'` projection to it. -/
instance completionTwoPatch_finite_J :
    Finite (completionTwoPatchFormalGlueData I hI a J hJ b θ
      hθ).toLocallyRingedSpaceGlueData.J :=
  inferInstanceAs (Finite (ULift.{u} Bool))

/-- **The glued two-patch formal completion is quasi-compact**: it is glued from two pieces, each
an affine formal completion and hence quasi-compact. -/
instance completionTwoPatch_compactSpace :
    CompactSpace (completionTwoPatch I hI a J hJ b θ hθ).toLocallyRingedSpace :=
  FormalScheme.GlueData.compactSpace _ (by
    rintro ⟨_ | _⟩
    · exact inferInstanceAs (CompactSpace (formalCompletion A I hI).toLocallyRingedSpace)
    · exact inferInstanceAs (CompactSpace (formalCompletion B J hJ).toLocallyRingedSpace))

/-- **The glued two-patch formal completion has points** as soon as the `A`-chart does: the `A`-side
patch is an open formal subscheme of it, so any point of `Spf A^` pushes forward. -/
theorem completionTwoPatch_nonempty [Nontrivial (A ⧸ I)] :
    Nonempty (completionTwoPatch I hI a J hJ b θ hθ).toLocallyRingedSpace := by
  obtain ⟨x⟩ := formalCompletion_nonempty I hI
  exact ⟨(completionTwoPatchι₀ I hI a J hJ b θ hθ).base x⟩

end TwoPatch

/-- **The compactness statements are not vacuous.** At `R = ℤ`, `I = J = (2)`, `a = b = 2` and
`θ` the identity, the glued two-patch formal completion is a nonempty quasi-compact space. -/
example : Nonempty (completionTwoPatch (Ideal.span {(2 : ℤ)})
      (Submodule.fg_span (Set.finite_singleton _)) (2 : ℤ) (Ideal.span {(2 : ℤ)})
      (Submodule.fg_span (Set.finite_singleton _)) (2 : ℤ)
      (RingEquiv.refl _) (Ideal.map_id _)).toLocallyRingedSpace := by
  haveI : Nontrivial (ℤ ⧸ Ideal.span {(2 : ℤ)}) :=
    Ideal.Quotient.nontrivial_iff.mpr (by
      rw [Ne, Ideal.eq_top_iff_one, Ideal.mem_span_singleton]
      decide)
  exact completionTwoPatch_nonempty _ _ _ _ _ _ _ _

end AlgebraicGeometry
