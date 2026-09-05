import FormalSchemes.StructureSheafStalkBot

set_option linter.style.header false

/-!
# `FormalSpectrum.IsStalkLimit` at a nilpotent ideal of definition

`FormalSchemes.StructureSheafStalkBot` gave `FormalSpectrum.IsStalkLimit` its first value, at
`I = ⊥`. This file widens that value to **every finitely generated nilpotent ideal of definition**:
`FormalSpectrum.isStalkLimit_of_isNilpotent` says `FormalSpectrum.IsStalkLimit J x` holds at every
point of `Spf (R, J)` whenever `J` is finitely generated and some power of `J` is `⊥`. The `⊥`
value is the case `J ^ 1 = ⊥`.

The point of the widening is not the extra rings. It is that **the `⊥` proof did not use `⊥`.**
`FormalSchemes.StructureSheafStalkBot` factored five lemmas out at a general ideal of definition —
`FormalSpectrum.awayToAtPrimeCompletion_algebraMap`, `FormalSpectrum.awayToAtPrime_mk'`,
`FormalSpectrum.algebraMap_mk'_mul_awayCompletionHom`,
`FormalSpectrum.mem_basicOpen_of_notMem_pointPrime` and
`FormalSpectrum.basicOpenRes_eq_zero_of_mul_eq_zero` — and every one of them is reused here
unchanged. Nothing below reproves anything from that file.

## The correction this file pays for

`FormalSchemes.StructureSheafStalkBot` discharges the `[TopologicalSpace R]` and `IsAdicRing ⊥`
hypotheses of `FormalSpectrum.basicOpenRes_comp_awayCompletionHom` inside a proof, by giving `R`
the discrete topology, and said of that manoeuvre that at a general ideal of definition "no choice
of topology makes it hold, so the trick has no analogue above `⊥`". **That was wrong**, and its
docstring is corrected in the same commit as this file.

`IsAdicRing I` (`FormalSchemes.AdicRing`) extends `IsAdicComplete I R` and adds `IsAdic I`, which
unfolds to the assertion that the ambient topology *is* `Ideal.adicTopology I`. So the choice
`Ideal.adicTopology I` discharges the `IsAdic` half **by `rfl`, at every ideal** — that is
`isAdicRing_adicTopology` below, and it is the declaration the corrected paragraph points at. What
no choice of topology supplies is `IsAdicComplete I R`, which is a condition on `I` and `R`.

The manoeuvre therefore reaches exactly as far as `I`-adic completeness does, and nilpotency is
the widest hypothesis under which that is free: `IsAdicComplete.of_pow_eq_bot`.

## What is *not* proved here, and the overclaim this file refuses

**This is not the first value outside the degenerate case, and must not be read as one.** For
`J ^ k = ⊥` the sections of the structure sheaf over a basic open are
`FormalSpectrum.awayCompletion J f`, whose ideal of definition is nilpotent too
(`FormalSpectrum.pow_map_away_eq_bot`), so that completion is `Localization.Away f` and
`Spf (R, J)` carries the ordinary structure sheaf of `Spec R` on the space of `Spec (R ⧸ J)`. No
completion actually happens at a nilpotent ideal of definition, exactly as none happens at `⊥`.
The value is a second point in the same regime, not a point outside it.

**The recorded obstruction is finite here, not absent — and neither word is "surmounted".**
`FormalSchemes.StructureSheafStalkComparison` records that the element killing witness `g` may
depend on the level `n`, while the injectivity half needs one `g` serving every level. At `⊥` the
stalk tower is constant from level 0, so there is nothing to be uniform over; at `J ^ k = ⊥` with
`k ≥ 2` that is **not** the situation — the tower is constant only from level `k - 1` on, so
finitely many levels are genuine and a uniform witness could in principle be assembled from
finitely many. Neither is the difficulty of the general case, where infinitely many levels differ,
and nothing below addresses that difficulty. The proof in this file in fact never reaches the
levels at all: it goes through `FormalSpectrum.isStalkLimit_iff_awayCompletion`, where nilpotency
has already collapsed both completions to the rings they complete. **A reader must not restate the
general question as open only in the Noetherian case.**

**`FormalSpectrum.IsStalkLimit` at an ideal of definition that is not nilpotent is exactly as open
as it was**, in both directions, and nothing below is evidence in either direction about it. In
particular no argument here survives the failure of `IsAdicComplete J R`, which is what the
general case is about.

**Nothing under a Noetherian hypothesis.** `Ideal.FG` of `J` is assumed because
`FormalSpectrum.isStalkLimit_iff_awayCompletion` and
`FormalSpectrum.isUnit_awayCompletionHom_of_basicOpen_le` require it, and nilpotency does not
imply it; no other finiteness is used.

**No comparison with `Spec`.** `FormalSchemes.SpfDiscrete` is not imported, for the reason
`FormalSchemes.StructureSheafStalkBot` gives, and no statement below is made through
`FormalSpectrum.specIsoSpfBot`.

## Placement

A new leaf over `FormalSchemes.StructureSheafStalkBot`: forward closure **40** modules besides
itself, reverse closure **0**.

`IsAdicComplete.of_pow_eq_bot` and `isAdicRing_adicTopology` mention no formal geometry and would
sit naturally in `FormalSchemes.AdicRing` beside `instIsAdicRingBotOfDiscreteTopology`. They are
**not** put there: `FormalSchemes.AdicRing`'s reverse closure is **487** of the project's 531
modules, so a declaration added to it rebuilds nine tenths of the tree, and neither has a consumer
outside this file. If a second consumer appears the move is worth re-costing; at one consumer it
is not.

## Main results

* `IsAdicComplete.of_pow_eq_bot`: a ring is `J`-adically complete when `J ^ k = ⊥`.
* `isAdicRing_adicTopology`: `IsAdicRing J` for the `J`-adic topology, given only
  `IsAdicComplete J R` — the declaration behind the correction above.
* `FormalSpectrum.exists_awayToAtPrimeCompletion_eq_of_pow_eq_bot`,
  `FormalSpectrum.exists_basicOpenRes_eq_zero_of_pow_eq_bot`: the surjectivity and injectivity
  halves of `FormalSpectrum.isStalkLimit_iff_awayCompletion`.
* `FormalSpectrum.isStalkLimit_of_pow_eq_bot`, `FormalSpectrum.isStalkLimit_of_isNilpotent`:
  **the value**.
* `FormalSpectrum.exists_isStalkLimit_nilpotentWitnessIdeal`: the value is attained at a
  **nonzero** ideal of definition, so the widening is not vacuous.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX).
-/

noncomputable section

universe u

/-! ### Nilpotent ideals of definition need no topology -/

/-- **A ring is `J`-adically complete as soon as some power of `J` is `⊥`**, with no further
hypothesis on `J` or on the ring — in particular no finite generation and no Noetherian
assumption. Hausdorffness is level `k`, where the filtration is already `⊥`; for precompleteness
the limit of a compatible system `f` is `f k`, and for `n ≥ k` the compatibility hypothesis at
`k ≤ n` is an equation rather than a congruence, again because `J ^ k = ⊥`.

Mathlib has `IsAdicComplete.bot` and `IsAdicComplete.of_subsingleton` but nothing for a nilpotent
ideal, and a library search over this statement turns nothing up. -/
theorem IsAdicComplete.of_pow_eq_bot {R : Type u} [CommRing R] {J : Ideal R} {k : ℕ}
    (hk : J ^ k = ⊥) : IsAdicComplete J R := by
  haveI : IsHausdorff J R := by
    constructor
    intro x hx
    have h := hx k
    rw [hk] at h
    simpa using h
  haveI : IsPrecomplete J R := by
    constructor
    intro f hf
    refine ⟨f k, fun n => ?_⟩
    rcases le_total n k with hnk | hkn
    · exact hf hnk
    · have hn : J ^ n = ⊥ := le_bot_iff.mp (hk ▸ Ideal.pow_le_pow_right hkn)
      have h := hf hkn
      rw [hk] at h
      have hfe : f k = f n := by simpa using h
      rw [hn, hfe]
  exact ⟨⟩

/-- **A choice of topology always discharges the `IsAdic` half of `IsAdicRing`.** `IsAdic J` is
the assertion that the ambient topology is `Ideal.adicTopology J`, so at that topology it is
`rfl`, at every ideal of every commutative ring. What remains — and what no topology supplies — is
the `IsAdicComplete J R` that `IsAdicRing` extends, which is a condition on `J` and `R`.

This is the declaration `FormalSchemes.StructureSheafStalkBot`'s corrected "No topology
hypothesis" paragraph points at: the manoeuvre of picking a topology inside a proof, to reach the
lemmas that carry `[TopologicalSpace R]` and `IsAdicRing`, is available exactly where `R` is
`J`-adically complete, and is not special to `⊥`.

Read the statement with the topology argument printed: suppressed, the conclusion reads
`IsAdicRing J`, which is not what is claimed. It is `@IsAdicRing R _ (Ideal.adicTopology J) J`,
and no other topology is asserted to work. -/
theorem isAdicRing_adicTopology {R : Type u} [CommRing R] (J : Ideal R) [IsAdicComplete J R] :
    @IsAdicRing R _ J.adicTopology J :=
  @IsAdicRing.mk R _ J.adicTopology J ‹_› rfl

namespace FormalSpectrum

variable {R : Type u} [CommRing R]

/-! ### Nilpotency passes to the two ideals the criterion names -/

/-- The ideal of definition of the stalk tower is nilpotent when the ideal of definition is: it is
the extension of `J` along `Ideal.Quotient.mk` composed with a localization, and `Ideal.map_pow`
carries the power across. -/
theorem pow_pointIdeal_eq_bot {J : Ideal R} {k : ℕ} (hk : J ^ k = ⊥) (x : FormalSpectrum J) :
    pointIdeal J x ^ k = ⊥ := by
  rw [pointIdeal, ← Ideal.map_pow, hk, Ideal.map_bot]

/-- The ideal of definition of `R{1/f}` is nilpotent when the ideal of definition is. -/
theorem pow_map_away_eq_bot {J : Ideal R} {k : ℕ} (hk : J ^ k = ⊥) (f : R) :
    (J.map (algebraMap R (Localization.Away f))) ^ k = ⊥ := by
  rw [← Ideal.map_pow, hk, Ideal.map_bot]

/-- **`R{1/f}` is `Localization.Away f` at a nilpotent ideal of definition**, in the direction the
surjectivity half needs. -/
theorem surjective_algebraMap_awayCompletion_of_pow_eq_bot {J : Ideal R} {k : ℕ} (hk : J ^ k = ⊥)
    (f : R) : Function.Surjective (algebraMap (Localization.Away f) (awayCompletion J f)) := by
  haveI := IsAdicComplete.of_pow_eq_bot (pow_map_away_eq_bot hk f)
  exact (AdicCompletion.ofAlgEquiv _).surjective

/-- **The completion of `Localization.AtPrime (pointPrime J x)` is itself at a nilpotent ideal of
definition**, in the direction the injectivity half needs. -/
theorem injective_algebraMap_atPrimeCompletion_of_pow_eq_bot {J : Ideal R} {k : ℕ}
    (hk : J ^ k = ⊥) (x : FormalSpectrum J) :
    Function.Injective (algebraMap (Localization.AtPrime (pointPrime J x))
      (AdicCompletion (pointIdeal J x) (Localization.AtPrime (pointPrime J x)))) := by
  haveI := IsAdicComplete.of_pow_eq_bot (pow_pointIdeal_eq_bot hk x)
  exact (AdicCompletion.ofAlgEquiv _).injective

/-! ### The two halves of the criterion -/

/-- **The surjectivity half at a nilpotent ideal of definition**, and it needs no topology on `R`:
every element of the completed local ring is `r / s` with `s ∉ pointPrime J x`, that says
`x ∈ D(s)` by `FormalSpectrum.mem_basicOpen_of_notMem_pointPrime`, and the same fraction read in
`R{1/s}` maps to it by `FormalSpectrum.awayToAtPrime_mk'`.

This is `FormalSpectrum.exists_awayToAtPrimeCompletion_eq_bot`'s proof with `⊥` replaced by `J`;
the only thing `⊥` supplied there was the completeness that `IsAdicComplete.of_pow_eq_bot` now
supplies. -/
theorem exists_awayToAtPrimeCompletion_eq_of_pow_eq_bot {J : Ideal R} (hJ : J.FG) {k : ℕ}
    (hk : J ^ k = ⊥) (x : FormalSpectrum J)
    (b : AdicCompletion (pointIdeal J x) (Localization.AtPrime (pointPrime J x))) :
    ∃ (f : R) (hf : x ∈ basicOpen J f) (a : awayCompletion J f),
      awayToAtPrimeCompletion J x hJ hf a = b := by
  haveI := IsAdicComplete.of_pow_eq_bot (pow_pointIdeal_eq_bot hk x)
  obtain ⟨c, rfl⟩ := (AdicCompletion.ofAlgEquiv (pointIdeal J x)).surjective b
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (pointPrime J x).primeCompl c
  refine ⟨(s : R), mem_basicOpen_of_notMem_pointPrime _ x s.2,
    algebraMap (Localization.Away (s : R)) _
      (IsLocalization.mk' (Localization.Away (s : R)) r ⟨(s : R), Submonoid.mem_powers _⟩), ?_⟩
  rw [awayToAtPrimeCompletion_algebraMap, awayToAtPrime_mk' _ x _ r _ s.2]
  rfl

/-- **The injectivity half at a nilpotent ideal of definition.** The two instance hypotheses of
`FormalSpectrum.basicOpenRes_eq_zero_of_mul_eq_zero` are discharged inside the proof by giving `R`
the `J`-adic topology, at which `IsAdic J` is `rfl` (`isAdicRing_adicTopology`) and
`IsAdicComplete J R` is `IsAdicComplete.of_pow_eq_bot`. That is legitimate because
`FormalSpectrum.basicOpenRes` takes no topology argument, so the term in the goal and the term in
the lemma are the same term.

The mathematics is unchanged from `FormalSpectrum.exists_basicOpenRes_eq_zero_bot`: an element
`r / f ^ n` of `Localization.Away f` dying in `Localization.AtPrime (pointPrime J x)` has
`g * r = 0` for some `g ∉ pointPrime J x` by `IsLocalization.mk'_eq_zero_iff`, and `D(f * g)` is a
basic open through `x` inside `D(f)` on which `g` is invertible. `D(f)` itself does not serve —
that would assert `Localization.Away f → Localization.AtPrime (pointPrime J x)` is injective,
which fails as soon as `R` has a zero-divisor killed away from the prime. -/
theorem exists_basicOpenRes_eq_zero_of_pow_eq_bot {J : Ideal R} (hJ : J.FG) {k : ℕ}
    (hk : J ^ k = ⊥) (x : FormalSpectrum J) (f : R) (hf : x ∈ basicOpen J f)
    (a : awayCompletion J f) (ha : awayToAtPrimeCompletion J x hJ hf a = 0) :
    ∃ (e : R) (_ : x ∈ basicOpen J e) (hle : basicOpen J e ≤ basicOpen J f),
      basicOpenRes J hle a = 0 := by
  letI : TopologicalSpace R := J.adicTopology
  haveI : IsAdicComplete J R := IsAdicComplete.of_pow_eq_bot hk
  haveI : IsAdicRing J := isAdicRing_adicTopology J
  obtain ⟨α, rfl⟩ := surjective_algebraMap_awayCompletion_of_pow_eq_bot hk f a
  obtain ⟨⟨r, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) α
  rw [awayToAtPrimeCompletion_algebraMap] at ha
  have hmc : (↑m : R) ∈ (pointPrime J x).primeCompl :=
    Submonoid.powers_le.mpr (notMem_pointPrime_of_mem_basicOpen J x hf) m.2
  rw [awayToAtPrime_mk' _ x hf r m hmc, ← map_zero (algebraMap
    (Localization.AtPrime (pointPrime J x))
    (AdicCompletion (pointIdeal J x) (Localization.AtPrime (pointPrime J x))))] at ha
  replace ha := injective_algebraMap_atPrimeCompletion_of_pow_eq_bot hk x ha
  obtain ⟨⟨g, hg⟩, hgr⟩ := (IsLocalization.mk'_eq_zero_iff r ⟨(m : R), hmc⟩).mp ha
  have hle : basicOpen J (f * g) ≤ basicOpen J f := by
    rw [basicOpen_mul]
    exact inf_le_left
  have hleg : basicOpen J (f * g) ≤ basicOpen J g := by
    rw [basicOpen_mul]
    exact inf_le_right
  have hxe : x ∈ basicOpen J (f * g) := by
    rw [basicOpen_mul]
    exact ⟨hf, mem_basicOpen_of_notMem_pointPrime J x hg⟩
  exact ⟨f * g, hxe, hle, basicOpenRes_eq_zero_of_mul_eq_zero J hJ m.2 hle hleg
    (algebraMap_mk'_mul_awayCompletionHom _ r m) hgr⟩

/-! ### The value -/

/-- **`FormalSpectrum.IsStalkLimit` holds at every finitely generated ideal of definition some
power of which is `⊥`**, at every point of `Spf (R, J)` and for every commutative ring `R`.

`FormalSpectrum.isStalkLimit_bot` is the case `k = 1`; the `example` below checks that rather than
asserting it. **This says nothing about an ideal of definition that is not nilpotent**, where the
question is exactly as open as before — see the module docstring for why the obstruction to the
general case does not arise here rather than being surmounted. -/
theorem isStalkLimit_of_pow_eq_bot {J : Ideal R} (hJ : J.FG) {k : ℕ} (hk : J ^ k = ⊥)
    (x : FormalSpectrum J) : IsStalkLimit J x := by
  rw [isStalkLimit_iff_awayCompletion J x hJ]
  exact ⟨fun f hf a ha => exists_basicOpenRes_eq_zero_of_pow_eq_bot hJ hk x f hf a ha,
    exists_awayToAtPrimeCompletion_eq_of_pow_eq_bot hJ hk x⟩

example (x : FormalSpectrum (⊥ : Ideal R)) : IsStalkLimit (⊥ : Ideal R) x :=
  isStalkLimit_of_pow_eq_bot Submodule.fg_bot (k := 1) (pow_one _) x

/-- **`FormalSpectrum.IsStalkLimit` holds at every finitely generated nilpotent ideal of
definition.** `IsNilpotent J` in the semiring of ideals is `∃ k, J ^ k = ⊥`, so this is
`FormalSpectrum.isStalkLimit_of_pow_eq_bot` with the power existentially quantified. -/
theorem isStalkLimit_of_isNilpotent {J : Ideal R} (hJ : J.FG) (hn : IsNilpotent J)
    (x : FormalSpectrum J) : IsStalkLimit J x :=
  let ⟨_, hk⟩ := hn
  isStalkLimit_of_pow_eq_bot hJ hk x

/-! ### The widening is not vacuous: a nonzero nilpotent ideal of definition -/

/-- **A nonzero nilpotent ideal of definition**, so that the value above is attained somewhere
`FormalSpectrum.isStalkLimit_bot` does not reach: the ideal generated by `2` in `ZMod 4`, whose
square is generated by `4 = 0`.

Without a witness of this shape, "holds at every nilpotent ideal of definition" would be
compatible with `⊥` being the only finitely generated nilpotent ideal in sight, and the widening
would say nothing. This is the check
`FormalSchemes.IndSchemeLimitComponents` writes as a theorem rather than a remark. -/
def nilpotentWitnessIdeal : Ideal (ZMod 4) := Ideal.span {2}

theorem pow_nilpotentWitnessIdeal_eq_bot : nilpotentWitnessIdeal ^ 2 = ⊥ := by
  rw [nilpotentWitnessIdeal, Ideal.span_singleton_pow, Ideal.span_singleton_eq_bot]
  decide

theorem fg_nilpotentWitnessIdeal : nilpotentWitnessIdeal.FG :=
  ⟨{2}, by simp [nilpotentWitnessIdeal]⟩

theorem nilpotentWitnessIdeal_ne_bot : nilpotentWitnessIdeal ≠ ⊥ := by
  rw [nilpotentWitnessIdeal, Ne, Ideal.span_singleton_eq_bot]
  decide

theorem nilpotentWitnessIdeal_ne_top : nilpotentWitnessIdeal ≠ ⊤ := by
  rw [nilpotentWitnessIdeal, Ne, Ideal.span_singleton_eq_top]
  decide

/-- `Spf (ZMod 4, (2))` has a point: `(2)` is not the whole ring, so the quotient is nontrivial and
its prime spectrum is nonempty. -/
theorem nonempty_formalSpectrum_nilpotentWitnessIdeal :
    Nonempty (FormalSpectrum nilpotentWitnessIdeal) := by
  haveI : Nontrivial (ZMod 4 ⧸ nilpotentWitnessIdeal) :=
    Ideal.Quotient.nontrivial_iff.mpr nilpotentWitnessIdeal_ne_top
  exact inferInstanceAs (Nonempty (PrimeSpectrum (ZMod 4 ⧸ nilpotentWitnessIdeal)))

/-- **`FormalSpectrum.IsStalkLimit` holds at a nonzero ideal of definition.** Together with
`FormalSpectrum.nilpotentWitnessIdeal_ne_bot` this is what makes
`FormalSpectrum.isStalkLimit_of_isNilpotent` a widening of
`FormalSpectrum.isStalkLimit_bot` rather than a restatement of it.

It is **not** a value outside the degenerate regime: `(2 : ZMod 4)` is nilpotent, so no completion
happens at this ideal of definition either. See the module docstring. -/
theorem exists_isStalkLimit_nilpotentWitnessIdeal :
    ∃ x : FormalSpectrum nilpotentWitnessIdeal, IsStalkLimit nilpotentWitnessIdeal x :=
  ⟨nonempty_formalSpectrum_nilpotentWitnessIdeal.some,
    isStalkLimit_of_pow_eq_bot fg_nilpotentWitnessIdeal pow_nilpotentWitnessIdeal_eq_bot _⟩

end FormalSpectrum
