import FormalSchemes.IdealsOfDefinition
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.Topology.Algebra.TopologicallyNilpotent

set_option linter.style.header false

/-!
# The largest ideal of definition of a Noetherian adic ring

An *ideal of definition* of a topological ring `R` is an ideal `I` for which the topology on `R`
is the `I`-adic one (`IsAdic I`). Such an ideal is far from unique, but the collection of ideals
of definition is well controlled: they all have the same radical (`IsAdic.radical_eq`, from
`FormalSchemes.IdealsOfDefinition`), and this common radical is the *largest* ideal of definition
whenever `R` is Noetherian. Geometrically this is the statement that the reduced closed subscheme
underlying `Spf R` is intrinsic, EGA I, §10.3, in particular 10.3.6.

## Main results

* `IsAdic.isTopologicalRing`: the ambient topology of an ideal of definition is a ring topology.
  This is what discharges the `[IsTopologicalRing R]` instance argument of the next result.
* `IsAdic.of_le_of_pow_le`: two cofinal ideals define the same adic topology — if `I` is an ideal
  of definition, `I ≤ J`, and some power `J ^ n ≤ I`, then `J` is again an ideal of definition.
  This is the elementary comparison underlying everything below.
* `IsAdic.isTopologicallyNilpotent_iff_mem_radical`: an element of an adic ring is topologically
  nilpotent (its powers converge to `0`) iff it lies in the radical of an ideal of definition. No
  finiteness hypothesis is needed.
* `IsAdic.topologicalNilradical_eq_radical`: consequently the `topologicalNilradical` of `R` (the
  ideal of topologically nilpotent elements) equals the radical of any ideal of definition.
* `IsAdic.isAdic_radical`: for a Noetherian adic ring, the radical of an ideal of definition is
  itself an ideal of definition.
* `IsAdic.isGreatest_radical` / `IsAdic.isAdic_topologicalNilradical`: for a Noetherian adic ring,
  the radical of an ideal of definition — equivalently the ideal of topologically nilpotent
  elements — is the *largest* ideal of definition (EGA I 10.3.6).

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], §10.3 (esp. 10.3.6).
* [The Stacks Project, Tag 0AHZ](https://stacks.math.columbia.edu/tag/0AHZ).
-/

open TopologicalSpace Topology

variable {R : Type*} [CommRing R] [TopologicalSpace R] {I J : Ideal R}

namespace IsAdic

/-- **The ambient topology of an ideal of definition is a ring topology.** If the topology on `R`
is the `I`-adic one (`IsAdic I`), then `R` is a topological ring — the `I`-adic topology is
nonarchimedean, hence a ring topology.

Stated here rather than downstream because `IsAdic.of_le_of_pow_le` below takes
`[IsTopologicalRing R]` as an instance argument, so without this lemma the file's own main
comparison theorem cannot be applied to a bare `IsAdic` hypothesis. -/
theorem isTopologicalRing {R : Type*} [CommRing R] [inst : TopologicalSpace R]
    {I : Ideal R} (hI : IsAdic I) : IsTopologicalRing R := by
  have h : inst = I.adicTopology := hI
  rw [h]
  exact (Ideal.nonarchimedean I).toIsTopologicalRing

/-- The topology underlying an ideal of definition is a linear topology. -/
theorem isLinearTopology (hI : IsAdic I) : IsLinearTopology R R := by
  have h := Ideal.isLinearTopology I
  rwa [← hI] at h

/-- Two cofinal ideals define the same adic topology: if `I` is an ideal of definition, `I ≤ J`,
and some power of `J` is contained in `I`, then `J` is an ideal of definition too. The powers of
`J` are then open (each contains the open ideal `I ^ m`) and cofinal with the powers of `I`. -/
theorem of_le_of_pow_le [IsTopologicalRing R] (hI : IsAdic I) (hle : I ≤ J) {n : ℕ}
    (hn : J ^ n ≤ I) : IsAdic J := by
  rw [isAdic_iff] at hI ⊢
  obtain ⟨hopen, hbasis⟩ := hI
  refine ⟨fun m => ?_, fun s hs => ?_⟩
  · exact Submodule.isOpen_mono (Ideal.pow_right_mono hle m) (hopen m)
  · obtain ⟨p, hp⟩ := hbasis s hs
    refine ⟨n * p, ?_⟩
    have hle' : (J ^ (n * p) : Ideal R) ≤ I ^ p := by
      rw [pow_mul]; exact Ideal.pow_right_mono hn p
    exact (SetLike.coe_subset_coe.mpr hle').trans hp

/-- An element of an adic ring is topologically nilpotent — its powers converge to `0` — precisely
when it lies in the radical of an ideal of definition `I`. One direction is that `I` is a
neighbourhood of `0`; the other uses that if `a ^ k ∈ I` then `a ^ m ∈ I ^ p` for all large `m`,
and the powers `I ^ p` form a basis of neighbourhoods of `0`. No finiteness hypothesis is
needed. -/
theorem isTopologicallyNilpotent_iff_mem_radical (hI : IsAdic I) {a : R} :
    IsTopologicallyNilpotent a ↔ a ∈ I.radical := by
  constructor
  · intro ha
    have hInhds : (I : Set R) ∈ 𝓝 (0 : R) := by
      have := hI.hasBasis_nhds_zero.mem_of_mem (i := 1) trivial
      rwa [pow_one] at this
    obtain ⟨n, hn⟩ := ha.exists_pow_mem_of_mem_nhds hInhds
    exact Ideal.mem_radical_iff.mpr ⟨n, hn⟩
  · intro hmem
    obtain ⟨k, hk⟩ := Ideal.mem_radical_iff.mp hmem
    rw [IsTopologicallyNilpotent, hI.hasBasis_nhds_zero.tendsto_right_iff]
    intro m _
    rw [Filter.eventually_atTop]
    refine ⟨k * m, fun l hl => ?_⟩
    have hkm : a ^ (k * m) ∈ I ^ m := by rw [pow_mul]; exact Ideal.pow_mem_pow hk m
    have hsplit : a ^ l = a ^ (l - k * m) * a ^ (k * m) := by
      rw [← pow_add, Nat.sub_add_cancel hl]
    rw [SetLike.mem_coe, hsplit]
    exact Ideal.mul_mem_left _ _ hkm

/-- The `topologicalNilradical` of an adic ring — the ideal of its topologically nilpotent
elements — equals the radical of any ideal of definition. -/
theorem topologicalNilradical_eq_radical [IsLinearTopology R R] (hI : IsAdic I) :
    topologicalNilradical R = I.radical := by
  ext a
  rw [IsTopologicallyNilpotent.mem_topologicalNilradical_iff]
  exact hI.isTopologicallyNilpotent_iff_mem_radical

/-- For a Noetherian adic ring, the radical of an ideal of definition is again an ideal of
definition: the radical is finitely generated, so some power of it lies inside `I`. -/
theorem isAdic_radical [IsTopologicalRing R] [IsNoetherianRing R] (hI : IsAdic I) :
    IsAdic I.radical := by
  obtain ⟨n, hn⟩ := I.exists_radical_pow_le_of_fg (IsNoetherian.noetherian _)
  exact hI.of_le_of_pow_le Ideal.le_radical hn

/-- **EGA I 10.3.6.** For a Noetherian adic ring, the radical of an ideal of definition is the
largest ideal of definition: it is itself an ideal of definition (`isAdic_radical`), and every
ideal of definition is contained in it (`IsAdic.le_radical`). -/
theorem isGreatest_radical [IsTopologicalRing R] [IsNoetherianRing R] (hI : IsAdic I) :
    IsGreatest {J : Ideal R | IsAdic J} I.radical :=
  ⟨hI.isAdic_radical, fun _ hJ => hI.le_radical hJ⟩

/-- **EGA I 10.3.6.** For a Noetherian adic ring, the ideal of topologically nilpotent elements is
the largest ideal of definition. Combining `topologicalNilradical_eq_radical` with
`isGreatest_radical`. -/
theorem isGreatest_topologicalNilradical [IsTopologicalRing R] [IsNoetherianRing R]
    [IsLinearTopology R R] (hI : IsAdic I) :
    IsGreatest {J : Ideal R | IsAdic J} (topologicalNilradical R) := by
  rw [hI.topologicalNilradical_eq_radical]
  exact hI.isGreatest_radical

/-- For a Noetherian adic ring, the ideal of topologically nilpotent elements is itself an ideal
of definition. -/
theorem isAdic_topologicalNilradical [IsTopologicalRing R] [IsNoetherianRing R]
    [IsLinearTopology R R] (hI : IsAdic I) : IsAdic (topologicalNilradical R) := by
  rw [hI.topologicalNilradical_eq_radical]
  exact hI.isAdic_radical

end IsAdic
