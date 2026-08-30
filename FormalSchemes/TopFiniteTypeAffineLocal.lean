import FormalSchemes.AwayTopFiniteType
import FormalSchemes.TopFiniteTypeSpecialFibre
import Mathlib.RingTheory.RingHom.FiniteType

set_option linter.style.header false

/-!
# Affine-locality of topological finite type

> If the basic opens `D(g)`, `g ∈ s`, cover `Spf L` and each chart algebra `A{1/g}^` is
> topologically of finite type over `(R, I)`, then so is `A`.

That is `AlgebraicGeometry.IsTopologicallyFiniteType.of_span_awayCompletion`. It is the adic
analogue of the algebra theorem "if `g₁, …, gₙ` generate the unit ideal and every `S_{gᵢ}` is of
finite type over `R`, then so is `S`", which is the statement
`FormalSchemes.RelativeTopFiniteTypeTrans` names as the missing general case, and which
`FormalSchemes.TopFiniteTypeHom`, `FormalSchemes.TwoChartBasicOpen` and three further module
docstrings record as absent. It is absent no longer.

## The route, and why it is not the expected one

The expected route is to run the classical partition-of-unity argument — pick generators of each
`A{1/gᵢ}^`, clear denominators, assemble — in the completed setting. That is a real theorem and
would have to be checked rather than transcribed.

It is not needed. `FormalSchemes.TopFiniteTypeSpecialFibre` characterises topological finite type
of a complete `(A, L)` with `L = I·A` as ordinary finite type of `A ⧸ L` over `R ⧸ I`, and
ordinary finite type is *already* known to be affine-local, by
`RingHom.finiteType_ofLocalizationSpanTarget`. What remains is the identification of the special
fibre of a basic-open chart with the corresponding localization of the special fibre, and the tree
already had that too —
`FormalSpectrum.awayCompletionResidueEquiv_comp_residueRingHom` (`FormalSchemes.BasicOpenChart`),
proved for the *topology* of the basic-open chart. So the whole statement is assembled from parts,
and the only new ingredient is the characterisation in the companion file.

**Two consequences of taking this route are worth recording**, because they change what a
successor needs.

* **No quasi-compactness hypothesis appears, and none is needed.** The obvious plan for
  conservativity is "an arbitrary open of `Spf I` is quasi-compact, hence a finite union of basic
  opens; then apply affine-locality". The first step is unnecessary:
  `RingHom.OfLocalizationSpanTarget` takes an **arbitrary** spanning set `s` and does the
  reduction to a finite subset itself. `IsTopologicallyFiniteType.of_span_awayCompletion`
  accordingly takes an arbitrary `s : Set A`. Whatever else conservativity needs, it does not
  need quasi-compactness of an open of `Spf I`, and the tree does not have to acquire
  `TopologicalSpace.NoetherianSpace`.
* **The cover condition is upstairs.** `Ideal.span s ⊔ L = ⊤` — the `D(g)` cover `Spf L` — rather
  than a condition on residues; the passage to `A ⧸ L` happens inside the proof.

## What this does *not* close

**Conservativity of `AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom` at an affine target**
(that at `Y = FormalScheme.Spf I` the general notion implies
`AlgebraicGeometry.FormalScheme.IsRelativelyTopFiniteType`) is still open, and the module
docstrings that record it stay — but the blocker has moved and they are amended to say so.

What is left is: for an **arbitrary affine open** `V ⊆ Spf I` and a basic open `D(f) ⊆ V` of the
ambient `Spf I`, identify the chart algebra of `D(f)` *as a basic open of `V`* — that is
`Γ (V){1/f|V}^` — with `R{1/f}^`. The two are chart presentations of one open of one formal
scheme, so by `FormalSchemes.SpfIsoIdealRecovery` they agree only up to an **equivalent ideal of
definition**, exactly the phenomenon `FormalSchemes.CofinalTopFiniteType` was built for (issue
1185). Affine-locality then finishes the argument, since the `D(f) ⊆ V` are a basis of `V` and
`Ideal.span` of their defining elements is `⊤` in `Γ (V) ⧸ L_V`.

So the obstruction is no longer an algebra theorem; it is the chart-identification bookkeeping.

## Main results

* `AlgebraicGeometry.awayCompletionResidueEquiv_comp_residueRingHom_algebraMap`: the special fibre
  of a basic-open chart, over the base rather than over `A`.
* `AlgebraicGeometry.IsTopologicallyFiniteType.of_span_awayCompletion`: **affine-locality.**
* `AlgebraicGeometry.IsTopologicallyFiniteType.of_awayCompletion_compl`: the two-chart case, which
  needs no side condition.
* `AlgebraicGeometry.IsTopologicallyFiniteType.self_of_two_charts`: non-vacuity.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.3.
* [The Stacks Project, Tag 00F6](https://stacks.math.columbia.edu/tag/00F6)
-/
noncomputable section

universe u

open FormalSpectrum

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {A : Type u} [CommRing A] [Algebra R A] {L : Ideal A}

/-- **The special fibre of a basic-open chart, over the base.** Along
`FormalSpectrum.awayCompletionResidueEquiv`, the special fibre map `R ⧸ I → A{1/g}^ ⧸ (I·A{1/g}^)`
of the chart is the special fibre map of `A` followed by the localization map
`A ⧸ L → (A ⧸ L)_{ḡ}`.

`FormalSpectrum.awayCompletionResidueEquiv_comp_residueRingHom` (`FormalSchemes.BasicOpenChart`)
is this statement over `A`; the only content added here is that
`algebraMap R (A{1/g}^)` factors as `algebraMap A (A{1/g}^) ∘ algebraMap R A`, which is
`FormalSpectrum.awayCompletionHom_comp_algebraMap`. -/
theorem awayCompletionResidueEquiv_comp_residueRingHom_algebraMap (hL : L.FG) (g : A)
    (hIL : I ≤ L.comap (algebraMap R A))
    (hIL' : I ≤ (awayCompletionIdeal L g).comap (algebraMap R (awayCompletion L g))) :
    (awayCompletionResidueEquiv L g hL).toRingHom.comp
        (residueRingHom I (awayCompletionIdeal L g)
          (algebraMap R (awayCompletion L g)) hIL') =
      (algebraMap (A ⧸ L) (Localization.Away (Ideal.Quotient.mk L g))).comp
        (residueRingHom I L (algebraMap R A) hIL) := by
  have hbase := awayCompletionResidueEquiv_comp_residueRingHom L g hL
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
  have hstep : (residueRingHom I (awayCompletionIdeal L g)
      (algebraMap R (awayCompletion L g)) hIL') (Ideal.Quotient.mk I r) =
      (residueRingHom L (awayCompletionIdeal L g) (awayCompletionHom L g)
        (le_comap_awayCompletionHom L g)) (Ideal.Quotient.mk L (algebraMap R A r)) := by
    rw [show (residueRingHom I (awayCompletionIdeal L g)
        (algebraMap R (awayCompletion L g)) hIL') (Ideal.Quotient.mk I r) =
        Ideal.Quotient.mk (awayCompletionIdeal L g)
          (algebraMap R (awayCompletion L g) r) from Ideal.quotientMap_mk,
      show (residueRingHom L (awayCompletionIdeal L g) (awayCompletionHom L g)
        (le_comap_awayCompletionHom L g)) (Ideal.Quotient.mk L (algebraMap R A r)) =
        Ideal.Quotient.mk (awayCompletionIdeal L g)
          (awayCompletionHom L g (algebraMap R A r)) from Ideal.quotientMap_mk,
      show algebraMap R (awayCompletion L g) r = awayCompletionHom L g (algebraMap R A r) from
        (RingHom.congr_fun
          (awayCompletionHom_comp_algebraMap (R := R) (A := A) (L := L) g) r).symm]
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [hstep, show (residueRingHom I L (algebraMap R A) hIL) (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk L (algebraMap R A r) from Ideal.quotientMap_mk]
  exact RingHom.congr_fun hbase (Ideal.Quotient.mk L (algebraMap R A r))

/-- **Affine-locality of topological finite type.** If the basic opens `D(g)`, `g ∈ s`, cover
`Spf L` — that is, if `s` together with `L` generates the unit ideal — and each chart algebra
`A{1/g}^` is topologically of finite type over `(R, I)`, then so is `A` itself.

`s` is an **arbitrary** set, not a finite one: `RingHom.OfLocalizationSpanTarget` performs the
reduction to a finite subset, so no quasi-compactness hypothesis is needed here or upstream of
here.

The proof is `isTopologicallyFiniteType_iff_finiteType_residueRingHom` in both directions —
once to turn each chart hypothesis into finite type of an ordinary ring map, once to turn the
conclusion back — with `RingHom.finiteType_ofLocalizationSpanTarget` in between. Completeness of
`A` is used, in the backward direction only. -/
theorem IsTopologicallyFiniteType.of_span_awayCompletion (hI : I.FG) [IsAdicComplete L A]
    (h : I.map (algebraMap R A) = L) (s : Set A) (hspan : Ideal.span s ⊔ L = ⊤)
    (H : ∀ g ∈ s, IsTopologicallyFiniteType R I
      (FormalSpectrum.awayCompletion L g) (awayCompletionIdeal L g)) :
    IsTopologicallyFiniteType R I A L := by
  have hIL : I ≤ L.comap (algebraMap R A) := Ideal.map_le_iff_le_comap.mp h.le
  have hL : L.FG := h ▸ hI.map _
  refine IsTopologicallyFiniteType.of_finiteType_residueRingHom hI h hIL ?_
  refine RingHom.finiteType_ofLocalizationSpanTarget _ (Ideal.Quotient.mk L '' s) ?_ ?_
  · have htop : Ideal.map (Ideal.Quotient.mk L) (Ideal.span s ⊔ L) = ⊤ := by
      rw [hspan]; exact Ideal.map_top _
    rwa [Ideal.map_sup, Ideal.map_span, Ideal.map_quotient_self, sup_bot_eq] at htop
  · rintro ⟨-, g, hg, rfl⟩
    have hIL' : I ≤ (awayCompletionIdeal L g).comap
        (algebraMap R (FormalSpectrum.awayCompletion L g)) :=
      Ideal.map_le_iff_le_comap.mp (map_algebraMap_awayCompletion g h).le
    have hft := IsTopologicallyFiniteType.finiteType_residueRingHom hI hIL' (H g hg)
    have hiso := RingHom.finiteType_respectsIso.1 _ (awayCompletionResidueEquiv L g hL) hft
    rwa [awayCompletionResidueEquiv_comp_residueRingHom_algebraMap hL g hIL hIL'] at hiso

/-- **The two-chart case**, which carries no side condition at all: `a` and `1 - a` generate the
unit ideal of `A` for every `a`, so the two basic opens `D(a)` and `D(1 - a)` cover `Spf L`
whatever `a` is. -/
theorem IsTopologicallyFiniteType.of_awayCompletion_compl (hI : I.FG) [IsAdicComplete L A]
    (h : I.map (algebraMap R A) = L) (a : A)
    (H₀ : IsTopologicallyFiniteType R I
      (FormalSpectrum.awayCompletion L a) (awayCompletionIdeal L a))
    (H₁ : IsTopologicallyFiniteType R I
      (FormalSpectrum.awayCompletion L (1 - a)) (awayCompletionIdeal L (1 - a))) :
    IsTopologicallyFiniteType R I A L := by
  refine IsTopologicallyFiniteType.of_span_awayCompletion hI h {a, 1 - a} ?_ ?_
  · have hone : Ideal.span ({a, 1 - a} : Set A) = ⊤ := by
      refine (Ideal.eq_top_iff_one _).mpr ?_
      have h1 : (1 : A) = a + (1 - a) := by ring
      rw [h1]
      exact Ideal.add_mem _ (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
    rw [hone, top_sup_eq]
  · rintro g (rfl | rfl)
    · exact H₀
    · exact H₁

/-- **Non-vacuity.** A complete adic `(R, I)` is topologically of finite type over itself,
recovered from the genuine two-chart cover `Spf I = D(a) ∪ D(1 - a)` for an arbitrary `a : R`:
both charts are tf-type by `IsTopologicallyFiniteType.awayCompletion_base`
(`FormalSchemes.AwayTopFiniteType`) and `IsTopologicallyFiniteType.of_awayCompletion_compl`
glues them.

The conclusion is `IsTopologicallyFiniteType.self`, proved independently and by a different route
(the zero-variable presentation). That is the point: the hypotheses of
`IsTopologicallyFiniteType.of_span_awayCompletion`
are simultaneously satisfiable at a cover with more than one chart, the instance is not closed by
`rfl` — `awayCompletion I a` is the completion of a localization, not `R` — and the two routes
agree. -/
theorem IsTopologicallyFiniteType.self_of_two_charts [IsAdicComplete I R] (hI : I.FG) (a : R) :
    IsTopologicallyFiniteType R I R I :=
  IsTopologicallyFiniteType.of_awayCompletion_compl (A := R) (L := I) hI
    (by rw [Algebra.algebraMap_self, Ideal.map_id]) a
    (IsTopologicallyFiniteType.awayCompletion_base hI a)
    (IsTopologicallyFiniteType.awayCompletion_base hI (1 - a))

end AlgebraicGeometry
