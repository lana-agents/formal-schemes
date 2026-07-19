import Mathlib.RingTheory.AdicCompletion.Topology

set_option linter.style.header false

/-!
# Adic rings

Formal schemes are built by gluing formal spectra of *adic rings*: topological commutative
rings that are linearly topologized by the powers of a distinguished ideal, and are complete
and Hausdorff for that topology. This file records that notion on top of the algebraic
`I`-adic completeness API (`IsAdicComplete`) and the `I`-adic topology API (`IsAdic`) that
already exist in Mathlib, and relates it to the topological notions of completeness and
Hausdorffness.

## Main definitions

* `IsAdicRing I`: `R` carries the `I`-adic topology and is `I`-adically complete, i.e. `I` is
  an *ideal of definition* of `R`.

## Main results

* `isAdicRing_iff_completeSpace_and_t2Space`: for a ring whose topology is the `I`-adic
  topology, being an adic ring with ideal of definition `I` is equivalent to being a complete
  Hausdorff topological ring.
* `instIsAdicRingBotOfDiscreteTopology`: every discrete topological ring is (trivially) adic
  with ideal of definition `⊥`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. 0, §7.
* [The Stacks Project, Tag 07E7](https://stacks.math.columbia.edu/tag/07E7)
-/

variable {R : Type*} [CommRing R]

/-- `R` is an **adic ring** with ideal of definition `I` if the topology on `R` is the
`I`-adic topology and `R` is `I`-adically complete, i.e. complete and Hausdorff for that
topology. Formal schemes are glued from formal spectra of such rings. -/
class IsAdicRing [TopologicalSpace R] (I : Ideal R) : Prop extends IsAdicComplete I R where
  isAdic : IsAdic I

theorem isAdicRing_iff_completeSpace_and_t2Space [UniformSpace R] [IsUniformAddGroup R]
    {I : Ideal R} (hI : IsAdic I) :
    IsAdicRing I ↔ CompleteSpace R ∧ T2Space R := by
  constructor
  · intro h
    exact ⟨hI.isPrecomplete_iff.mp h.toIsAdicComplete.toIsPrecomplete,
      hI.isHausdorff_iff.mp h.toIsAdicComplete.toIsHausdorff⟩
  · rintro ⟨hc, ht⟩
    exact
      { isAdic := hI
        toIsAdicComplete :=
          { toIsHausdorff := hI.isHausdorff_iff.mpr ht
            toIsPrecomplete := hI.isPrecomplete_iff.mpr hc } }

/-- A discrete topological ring is adic with ideal of definition `⊥`: the powers of `⊥` are
already a neighbourhood basis of `0` (namely `{0}` itself), so completeness and Hausdorffness
are automatic. -/
instance instIsAdicRingBotOfDiscreteTopology [TopologicalSpace R] [DiscreteTopology R] :
    IsAdicRing (⊥ : Ideal R) where
  isAdic := is_bot_adic_iff.mpr ‹DiscreteTopology R›
