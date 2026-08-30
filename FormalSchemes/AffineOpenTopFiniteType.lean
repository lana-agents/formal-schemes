import FormalSchemes.AdicOnSections
import FormalSchemes.CofinalTopFiniteTypeAffineLocal
import FormalSchemes.SpfIsoOverBase

set_option linter.style.header false

/-!
# An affine open of `Spf I` is topologically of finite type over `(R, I)`

This is conservativity's long-standing missing step, modulo one hypothesis that is named and
isolated below.

> Let `(R, I)` be a complete adic ring with `I` finitely generated and let
> `m : Spf J ⟶ Spf I` be an **open immersion** from an affine formal spectrum, so `B` is the ring
> of an affine open of `Spf I`. If `J` is cofinal with `I · B`, then `B` is topologically of
> finite type over `(R, I)`.

That is `AlgebraicGeometry.IsTopologicallyFiniteType.of_openImmersion_of_isCofinal`.

## What each ingredient does

The proof is an application of three landed results and nothing else.

* At each point of `Spf J`, `FormalSpectrum.exists_basicOpenChart_inter_iso`
  (`FormalSchemes.TwoChartBasicOpen`) produces a basic open `D(g)` of `Spf J` which is *also* a
  basic open `D(f)` of the ambient `Spf I`, together with an isomorphism of the two chart formal
  spectra **over** `Spf I`.
* `FormalSpectrum.spfAlgEquivOfComm` (`FormalSchemes.SpfIsoOverBase`) makes that isomorphism
  `R`-linear, so `IsTopologicallyFiniteType.ofAlgEquiv` can carry
  `IsTopologicallyFiniteType.awayCompletion_base` — the statement that `R{1/f}^` is tf-type over
  `(R, I)` — from the ambient chart to the chart of `B`.
* `AlgebraicGeometry.IsTopologicallyFiniteType.of_span_awayCompletion_of_isCofinal`
  (`FormalSchemes.CofinalTopFiniteTypeAffineLocal`) assembles `B` from those charts. Its
  cofinality tolerance is what the hypothesis `Ideal.IsCofinal J (I · B)` feeds.

No quasi-compactness of the open appears, and none is needed: the charts are collected into a set
`s` of *all* elements of `B` whose chart is tf-type, and `RingHom.OfLocalizationSpanTarget`
performs the reduction to a finite subset inside `of_span_awayCompletion`.

## The one hypothesis, and why it is a hypothesis

`Ideal.IsCofinal J (I.map (algebraMap R B))` says the open immersion is **adic up to
cofinality**. It is not derivable on this tree, and it is not an oversight:

* Its on-the-nose form `I · B ≤ J` — adicity of an open immersion on global sections — is
  **false**. `FormalSchemes.AdicOnSections` records the refutation (issue 460): `IsAdicRing J`
  fixes only the topology of `B`, not the ideal `J`, and `FormalSpectrum.cofinalSpfIso`
  (`FormalSchemes.CofinalSheafComparisonIso`) builds an open immersion — an isomorphism, even —
  for which `J` is the *square* of the right ideal.
* Cofinality is the invariant repair of that false statement: the counterexample's two ideals are
  cofinal, so it does not refute this form, and for an isomorphism the statement is a theorem,
  `FormalSpectrum.isCofinal_map_spfIsoRingEquiv` (`FormalSchemes.SpfIsoIdealRecovery`).
* The tree has nothing of the shape "an open immersion of formal spectra is adic up to
  cofinality":
  `git grep -nE "IsCofinal.*globalSectionsMap|globalSectionsMap.*IsCofinal" -- FormalSchemes/`
  returns `rc = 1`, measured on `2ec245a`, `rc` taken from a redirect rather than through a pipe.

So conservativity's residue is now exactly one statement about open immersions, with no algebra
left in it. It is a statement about the structure sheaf of `Spf I` on an affine open — that the
extension of the base ideal is again an ideal of definition — and it is the natural successor to
this file.

## Main results

* `FormalSpectrum.sup_eq_top_of_forall_exists_mem_basicOpen`: a family of basic opens covering
  `Spf J`, read as an ideal-theoretic statement in `B`.
* `AlgebraicGeometry.IsTopologicallyFiniteType.of_openImmersion_of_isCofinal`: **the affine open
  is tf-type.**
* `AlgebraicGeometry.IsTopologicallyFiniteType.of_basicOpenChart`: non-vacuity — the hypotheses
  are simultaneously satisfiable at a basic-open chart of `Spf I`, where the cofinality hypothesis
  is an equality and the conclusion is `IsTopologicallyFiniteType.awayCompletion_base` reached by
  the covering route.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.12, §10.13.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.3.
-/
noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FormalSpectrum

/-- **A cover by basic opens, read in the ring.** If every point of `Spf J` lies in `D(g)` for
some `g ∈ s`, then `s` together with `J` generates the unit ideal of `B`.

Passing to `B ⧸ J` turns the covering statement into `Ideal.span (s mod J) = ⊤`
(`PrimeSpectrum.iSup_basicOpen_eq_top_iff`), and `Ideal.comap_map_of_surjective` brings it back
up, adding exactly the kernel `J`. This is the converse of the reading of `Ideal.span s ⊔ L = ⊤`
that `AlgebraicGeometry.IsTopologicallyFiniteType.of_span_awayCompletion`'s docstring gives, and
it is what lets a geometric cover discharge that theorem's hypothesis. -/
theorem sup_eq_top_of_forall_exists_mem_basicOpen {B : Type u} [CommRing B] (J : Ideal B)
    (s : Set B) (h : ∀ x : FormalSpectrum J, ∃ g ∈ s, x ∈ basicOpen J g) :
    Ideal.span s ⊔ J = ⊤ := by
  have hcov : (⨆ g : s, PrimeSpectrum.basicOpen (Ideal.Quotient.mk J (g : B))) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨g, hg, hxg⟩ := h x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, hg⟩, hxg⟩
  have hquot : Ideal.span (Ideal.Quotient.mk J '' s) = ⊤ := by
    rw [Set.image_eq_range]
    exact PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp hcov
  have hmap : Ideal.map (Ideal.Quotient.mk J) (Ideal.span s) = ⊤ := by
    rw [Ideal.map_span]; exact hquot
  have hcomap := Ideal.comap_map_of_surjective (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective (Ideal.span s)
  have hker : Ideal.comap (Ideal.Quotient.mk J) (⊥ : Ideal (B ⧸ J)) = J := by
    rw [← RingHom.ker_eq_comap_bot]
    exact Ideal.mk_ker
  rw [hmap, Ideal.comap_top, hker] at hcomap
  exact hcomap.symm

end FormalSpectrum

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {I : Ideal R} [TopologicalSpace R] [IsAdicRing I]
variable {B : Type u} [CommRing B] [TopologicalSpace B] {J : Ideal B} [IsAdicRing J]
variable [Algebra R B]

/-- **An affine open of `Spf I` is topologically of finite type over `(R, I)`**, given that the
open immersion presenting it is adic up to cofinality.

`m : Spf J ⟶ Spf I` is an open immersion of formal spectra, `halg` says the `R`-algebra structure
on `B` is the one `m` induces on global sections, and `hcof` is the hypothesis discussed at length
in this file's module docstring: the ideal of definition `J` of the open is cofinal with the
extension `I · B` of the base ideal. The conclusion's ideal is `I · B` and could not be `J`, since
`IsTopologicallyFiniteType.map_eq` pins it.

Every point of `Spf J` is covered by a basic open of `Spf J` that is simultaneously a basic open
of `Spf I`; over such a chart the two presentations are isomorphic as `R`-algebras, so the chart
inherits tf-type from `IsTopologicallyFiniteType.awayCompletion_base`, and affine-locality
assembles `B`. -/
theorem IsTopologicallyFiniteType.of_openImmersion_of_isCofinal (hI : I.FG)
    (hJ : J.FG) (m : FormalSpectrum.locallyRingedSpaceObj J ⟶
      FormalSpectrum.locallyRingedSpaceObj I)
    [LocallyRingedSpace.IsOpenImmersion m]
    (halg : algebraMap R B = FormalSpectrum.globalSectionsMap I J m)
    (hcof : Ideal.IsCofinal J (I.map (algebraMap R B))) :
    IsTopologicallyFiniteType R I B (I.map (algebraMap R B)) := by
  haveI : IsAdicComplete J B := ‹IsAdicRing J›.toIsAdicComplete
  haveI : IsAdicComplete I R := ‹IsAdicRing I›.toIsAdicComplete
  haveI : ∀ g : B, IsAdicRing (FormalSpectrum.awayCompletionIdeal J g) := fun g =>
    FormalSpectrum.isAdicRing_awayCompletionIdeal J g hJ
  haveI : ∀ f : R, IsAdicRing (FormalSpectrum.awayCompletionIdeal I f) := fun f =>
    FormalSpectrum.isAdicRing_awayCompletionIdeal I f hI
  -- The chart condition, as a predicate on elements of `B`.
  set P : B → Prop := fun g => IsTopologicallyFiniteType R I
    (FormalSpectrum.awayCompletion J g)
    (I.map (algebraMap R (FormalSpectrum.awayCompletion J g))) with hP
  -- Every point of `Spf J` lies in `D(g)` for some `g` satisfying it.
  have key : ∀ x : FormalSpectrum J, ∃ g, P g ∧ x ∈ FormalSpectrum.basicOpen J g := by
    intro x
    obtain ⟨g, f, e, hfac, -, hxg⟩ :=
      FormalSpectrum.exists_basicOpenChart_inter_iso hJ hI m (𝟙 _) (m.base x)
        ⟨x, rfl⟩ ⟨m.base x, by simp⟩
    have hcomp : FormalSpectrum.basicOpenChart I f ≫ 𝟙 _ =
        FormalSpectrum.basicOpenChart I f := Category.comp_id _
    have h₁ : algebraMap R (FormalSpectrum.awayCompletion J g) =
        FormalSpectrum.globalSectionsMap I (FormalSpectrum.awayCompletionIdeal J g)
          (FormalSpectrum.basicOpenChart J g ≫ m) := by
      rw [FormalSpectrum.globalSectionsMap_comp,
        FormalSpectrum.globalSectionsMap_basicOpenChart, ← halg,
        FormalSpectrum.awayCompletionHom_comp_algebraMap]
    have h₂ : algebraMap R (FormalSpectrum.awayCompletion I f) =
        FormalSpectrum.globalSectionsMap I (FormalSpectrum.awayCompletionIdeal I f)
          (FormalSpectrum.basicOpenChart I f ≫ 𝟙 _) := by
      rw [hcomp, FormalSpectrum.globalSectionsMap_basicOpenChart,
        ← FormalSpectrum.awayCompletionHom_comp_algebraMap (R := R) (A := R) (L := I) f,
        Algebra.algebraMap_self, RingHom.comp_id]
    refine ⟨g, (IsTopologicallyFiniteType.awayCompletion_base hI f).ofAlgEquiv
      (FormalSpectrum.spfAlgEquivOfComm e _ _ hfac h₁ h₂), ?_⟩
    -- `m` is injective on points, so the ambient membership descends.
    rw [FormalSpectrum.range_basicOpenChart_comp hJ m g] at hxg
    obtain ⟨y, hy, hyx⟩ := hxg
    exact (‹LocallyRingedSpace.IsOpenImmersion m›.base_open.injective hyx) ▸ hy
  refine IsTopologicallyFiniteType.of_span_awayCompletion_of_isCofinal hI hcof {g | P g}
    (FormalSpectrum.sup_eq_top_of_forall_exists_mem_basicOpen J _
      fun x => (key x).imp fun _ h => ⟨h.1, h.2⟩)
    fun g hg => hg

/-- **Non-vacuity.** The hypotheses of
`AlgebraicGeometry.IsTopologicallyFiniteType.of_openImmersion_of_isCofinal` are simultaneously
satisfiable at a basic-open chart `Spf R{1/f}^ ⟶ Spf I`, which is an open immersion
(`FormalSpectrum.isOpenImmersion_basicOpenChart`) whose ideal of definition is on the nose the
extension of `I` (`FormalSpectrum.map_algebraMap_awayCompletion`), so the cofinality hypothesis is
satisfied by reflexivity.

This is an application, not a restatement. Its conclusion agrees with
`AlgebraicGeometry.IsTopologicallyFiniteType.awayCompletion_base`
(`FormalSchemes.AwayTopFiniteType`), which is proved by an entirely different route — the explicit
presentation `awayEval` with one extra variable — whereas the proof here covers `D(f)` by basic
opens of itself and reassembles. It is not closed by `rfl`: the two sides are the same proposition
reached through `RingHom.finiteType_ofLocalizationSpanTarget`, and the covering is by the whole
set `{g | …}` rather than by `{1}`. -/
theorem IsTopologicallyFiniteType.of_basicOpenChart (hI : I.FG) (f : R) :
    IsTopologicallyFiniteType R I (FormalSpectrum.awayCompletion I f)
      (I.map (algebraMap R (FormalSpectrum.awayCompletion I f))) := by
  haveI := FormalSpectrum.isAdicRing_awayCompletionIdeal I f hI
  haveI : LocallyRingedSpace.IsOpenImmersion (FormalSpectrum.basicOpenChart I f) :=
    FormalSpectrum.isOpenImmersion_basicOpenChart I f hI
  have hself : I.map (algebraMap R R) = I := by rw [Algebra.algebraMap_self, Ideal.map_id]
  have hideal : I.map (algebraMap R (FormalSpectrum.awayCompletion I f)) =
      FormalSpectrum.awayCompletionIdeal I f :=
    FormalSpectrum.map_algebraMap_awayCompletion (I := I) (A := R) f hself
  have hJfg : (FormalSpectrum.awayCompletionIdeal I f).FG := by
    rw [← FormalSpectrum.map_awayCompletionHom I f]
    exact hI.map _
  refine IsTopologicallyFiniteType.of_openImmersion_of_isCofinal hI hJfg
    (FormalSpectrum.basicOpenChart I f) ?_ ?_
  · rw [FormalSpectrum.globalSectionsMap_basicOpenChart,
      ← FormalSpectrum.awayCompletionHom_comp_algebraMap (R := R) (A := R) (L := I) f,
      Algebra.algebraMap_self, RingHom.comp_id]
  · rw [hideal]

end AlgebraicGeometry
