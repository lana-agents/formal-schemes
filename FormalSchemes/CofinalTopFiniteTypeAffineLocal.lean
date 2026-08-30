import FormalSchemes.CofinalAdicComplete
import FormalSchemes.CofinalTopFiniteType
import FormalSchemes.TopFiniteTypeAffineLocal

set_option linter.style.header false

/-!
# Affine-locality of topological finite type, at an ideal given only up to cofinality

`AlgebraicGeometry.IsTopologicallyFiniteType.of_span_awayCompletion`
(`FormalSchemes.TopFiniteTypeAffineLocal`, issue 1202) assembles a tf-type algebra from a cover of
it by tf-type basic opens, but it pins the ideal of definition of the assembled ring **on the
nose**: it carries `I · A = L` as a hypothesis, and `IsTopologicallyFiniteType.map_eq`
(`FormalSchemes.TopFiniteType`) means it could not do otherwise. This file relaxes that to
`Ideal.IsCofinal L (I · A)`.

## Why the relaxation is not optional

The consumer is conservativity of `AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom`, where `A`
is the ring of an affine open of `Spf I` and `L` is *its* ideal of definition. An ideal of
definition is not determined by the formal spectrum — only its radical is
(`FormalSpectrum.isCofinal_map_spfIsoRingEquiv`, `FormalSchemes.SpfIsoIdealRecovery`) — so a
geometric input never supplies `I · A = L`, and the on-the-nose statement is simply not applicable
there. `L` versus `L ^ 2` is the standing counterexample.

Three things change, and each is charged to a different lemma:

* the completeness instance, which is stated against `L` and needed against `I · A`:
  `Ideal.IsCofinal.isAdicComplete` (`FormalSchemes.CofinalAdicComplete`);
* the chart algebras, which are the completions of `A_g` at two cofinal ideals and so are
  isomorphic but not equal: `AdicCompletion.cofinalAlgEquiv`
  (`FormalSchemes.CofinalCompletionAlg`), through
  `IsTopologicallyFiniteType.ofAlgEquiv`;
* the cover condition `Ideal.span s ⊔ L = ⊤`, which survives because `IsCoprime.pow_right`
  moves it to a power of `L` and a power of `L` sits inside `I · A`.

## The chart hypothesis has to be restated too

The on-the-nose theorem asks for
`IsTopologicallyFiniteType R I (A{1/g}^) (awayCompletionIdeal L g)`.
That form is **unusable here**: `IsTopologicallyFiniteType.map_eq` forces the ideal of a tf-type
algebra to be the extension of `I`, and `awayCompletionIdeal L g` is the extension of `L`. When
`L` is merely cofinal with `I · A` those are different ideals, so the hypothesis as spelled would
be false rather than merely inconvenient. The chart hypothesis below is therefore spelled with
`I.map (algebraMap R _)`, which is also exactly what
`IsTopologicallyFiniteType.ofAlgEquiv` produces.

## What this does *not* close

Conservativity is still open, and after this file the missing step is **not** the chart
identification. `FormalSpectrum.spfAlgEquivOfComm` (`FormalSchemes.SpfIsoOverBase`) supplies the
`R`-algebra isomorphism between the two presentations of a basic open of an affine open, and this
file consumes an ideal known only up to cofinality. What is missing is the hypothesis
`Ideal.IsCofinal L (I · A)` itself, for `A` the ring of an arbitrary affine open of `Spf I`: that
an affine open immersion of formal spectra is **adic up to cofinality**. The on-the-nose form of
that statement — `I · A ≤ L`, i.e. adicity on global sections — is *false*, and
`FormalSchemes.AdicOnSections` records the refutation (issue 460); the cofinality form is the
invariant repair, and the tree does not have it.

## Main results

* `Ideal.sup_eq_top_of_pow_le`: the cover condition is invariant under cofinality.
* `AlgebraicGeometry.IsTopologicallyFiniteType.of_span_awayCompletion_of_isCofinal`: **the
  relaxation.**
* `AlgebraicGeometry.IsTopologicallyFiniteType.self_of_two_charts_pow`: non-vacuity, through a
  genuinely non-reflexive cofinality — the two-chart cover of `Spf I` read against `I ^ 2`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.5, §10.13.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.3.
-/
noncomputable section

universe u

open FormalSpectrum

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {A : Type u} [CommRing A] [Algebra R A] {L : Ideal A}

/-- **The cover condition is invariant under cofinality.** If `s` together with `L` generates the
unit ideal and some power of `L` lies in `K`, then `s` together with `K` generates the unit ideal:
`Ideal.isCoprime_iff_sup_eq` and `IsCoprime.pow_right` move the statement to `L ^ m`, and
monotonicity of `⊔` finishes it.

Geometrically this is the statement that `V (L) = V (K)` for cofinal `L` and `K`, so a family of
basic opens covers one exactly when it covers the other. -/
theorem _root_.Ideal.sup_eq_top_of_pow_le {K : Ideal A} {s : Set A}
    (hspan : Ideal.span s ⊔ L = ⊤) {m : ℕ} (hm : L ^ m ≤ K) : Ideal.span s ⊔ K = ⊤ := by
  have hcop : IsCoprime (Ideal.span s) L := Ideal.isCoprime_iff_sup_eq.mpr hspan
  have hpow : Ideal.span s ⊔ L ^ m = ⊤ :=
    Ideal.isCoprime_iff_sup_eq.mp (hcop.pow_right (n := m))
  exact top_le_iff.mp (hpow.ge.trans (sup_le_sup_left hm _))

/-- **Affine-locality of topological finite type, with the ideal of definition given only up to
cofinality.** If `L` is cofinal with `I · A`, the ring `A` is `L`-adically complete, the basic
opens `D(g)` for `g ∈ s` cover `Spf L`, and each chart algebra `A{1/g}^` — formed against `L` — is
topologically of finite type over `(R, I)`, then `A` itself is topologically of finite type over
`(R, I)`.

The conclusion's ideal is `I · A`, not `L`, and it must be: `IsTopologicallyFiniteType.map_eq`
pins the ideal of a tf-type algebra to the extension of the base ideal, so no statement concluding
against `L` could be true. What survives is that the two are cofinal, which is the hypothesis, so
the adic topology of `A` is unchanged.

As in `AlgebraicGeometry.IsTopologicallyFiniteType.of_span_awayCompletion`, `s` is an **arbitrary**
set: `RingHom.OfLocalizationSpanTarget` performs the reduction to a finite subset, so no
quasi-compactness hypothesis is needed here or upstream of here. -/
theorem IsTopologicallyFiniteType.of_span_awayCompletion_of_isCofinal (hI : I.FG)
    [IsAdicComplete L A] (hcof : Ideal.IsCofinal L (I.map (algebraMap R A))) (s : Set A)
    (hspan : Ideal.span s ⊔ L = ⊤)
    (H : ∀ g ∈ s, IsTopologicallyFiniteType R I (FormalSpectrum.awayCompletion L g)
      (I.map (algebraMap R (FormalSpectrum.awayCompletion L g)))) :
    IsTopologicallyFiniteType R I A (I.map (algebraMap R A)) := by
  haveI : IsAdicComplete (I.map (algebraMap R A)) A := hcof.isAdicComplete (M := A)
  obtain ⟨m, hm⟩ := hcof.exists_pow_le
  refine IsTopologicallyFiniteType.of_span_awayCompletion hI rfl s
    (Ideal.sup_eq_top_of_pow_le hspan hm) ?_
  intro g hg
  have hgcof := hcof.map (algebraMap A (Localization.Away g))
  have hstep := (H g hg).ofAlgEquiv
    (AdicCompletion.cofinalAlgEquiv (T := R) hgcof.1.choose_spec hgcof.2.choose_spec)
  rwa [map_algebraMap_awayCompletion_eq I g] at hstep

/-- **Non-vacuity, through a cofinality that is not reflexive.** A complete adic `(R, I)` is
topologically of finite type over itself, recovered from the two-chart cover
`Spf I = D(a) ∪ D(1 - a)` read against the ideal `I ^ 2` rather than against `I`.

This exercises the whole relaxation rather than only its statement: `I ^ 2` is not `I · R`, so
`AlgebraicGeometry.IsTopologicallyFiniteType.of_span_awayCompletion` does not apply; the
completeness instance is produced by `IsAdicComplete.pow` (`FormalSchemes.CofinalAdicComplete`),
the cover condition by `Ideal.sup_eq_top_of_pow_le`, and each chart hypothesis by transporting
`IsTopologicallyFiniteType.awayCompletion_base` — which is stated against `I` — across
`AdicCompletion.cofinalAlgEquiv`. The conclusion `IsTopologicallyFiniteType R I R I` agrees with
`IsTopologicallyFiniteType.self`, proved by the unrelated zero-variable presentation, and is not
closed by `rfl`: the chart algebras are completions of localizations of `R`, at a *square* of the
ideal of definition. -/
theorem IsTopologicallyFiniteType.self_of_two_charts_pow [IsAdicComplete I R] (hI : I.FG) (a : R) :
    IsTopologicallyFiniteType R I R I := by
  haveI : IsAdicComplete (I ^ 2) R := IsAdicComplete.pow (M := R) two_ne_zero
  have hself : I.map (algebraMap R R) = I := by rw [Algebra.algebraMap_self, Ideal.map_id]
  have hcof : Ideal.IsCofinal (I ^ 2) (I.map (algebraMap R R)) := by
    rw [hself]
    exact (Ideal.IsCofinal.pow I two_ne_zero).symm
  have hchart : ∀ g : R, IsTopologicallyFiniteType R I
      (FormalSpectrum.awayCompletion (I ^ 2) g)
      (I.map (algebraMap R (FormalSpectrum.awayCompletion (I ^ 2) g))) := by
    intro g
    have hgcof := (Ideal.IsCofinal.pow I two_ne_zero).map (algebraMap R (Localization.Away g))
    exact (IsTopologicallyFiniteType.awayCompletion_base hI g).ofAlgEquiv
      (AdicCompletion.cofinalAlgEquiv (T := R) hgcof.1.choose_spec hgcof.2.choose_spec)
  have hspan : Ideal.span ({a, 1 - a} : Set R) ⊔ I ^ 2 = ⊤ := by
    have hone : Ideal.span ({a, 1 - a} : Set R) = ⊤ := by
      refine (Ideal.eq_top_iff_one _).mpr ?_
      have h1 : (1 : R) = a + (1 - a) := by ring
      rw [h1]
      exact Ideal.add_mem _ (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
    rw [hone, top_sup_eq]
  have := IsTopologicallyFiniteType.of_span_awayCompletion_of_isCofinal (A := R) (L := I ^ 2) hI
    hcof {a, 1 - a} hspan fun g _ => hchart g
  rwa [hself] at this

end AlgebraicGeometry
