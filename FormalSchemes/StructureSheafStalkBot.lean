import FormalSchemes.StructureSheafStalkComparison
import FormalSchemes.AwayCompletionRestrict

set_option linter.style.header false

/-!
# `FormalSpectrum.IsStalkLimit` at `I = ⊥`: the predicate's first value

`FormalSpectrum.IsStalkLimit I x` (`FormalSchemes.StructureSheafStalks`) is the stalk half of
EGA I 10.8 at a point `x` of `Spf (R, I)`: the assertion that
`FormalSpectrum.stalkToLimit I x` is an isomorphism, i.e. that the stalk of `O_{Spf R}` at `x` is
the limit of the stalks of the thickenings. Every module on this tree that mentions it says in as
many words that it is undecided, and a search over the whole library confirms that: every
occurrence is its definition, one of the five `Iff`s that restate it, or a paragraph declining to
decide it.
**No ring and no point had ever been supplied at which it is known to hold or to fail.**

This file supplies one, positively and for every commutative ring:
`FormalSpectrum.isStalkLimit_bot` says `FormalSpectrum.IsStalkLimit (⊥ : Ideal R) x` holds at every
point `x` of `Spf (R, ⊥)`, and `FormalSpectrum.exists_isStalkLimit_bot` records that there is such
a point whenever `R` is nontrivial, so the predicate is **not vacuous**.

## Why `⊥` is the case that can be decided

At `⊥` every adic completion in the criterion is the ring it completes: `AdicCompletion ⊥ A` is
`A` because `IsAdicComplete (⊥ : Ideal A) A` holds for every `A` with no hypotheses at all, and
both `FormalSpectrum.pointIdeal (⊥ : Ideal R) x` and the extension of `⊥` to
`Localization.Away f` are `⊥` by `Ideal.map_bot`. So
`FormalSpectrum.isStalkLimit_iff_awayCompletion` degenerates to two standard facts about
localizations, and this file proves exactly those two:

* *surjectivity* — every element of `Localization.AtPrime (pointPrime I x)` is `r / s` with
  `s ∉ pointPrime I x`, which is the image of the same fraction in `Localization.Away s`, and
  `s ∉ pointPrime I x` says exactly `x ∈ D(s)`;
* *injectivity* — an element `r / f ^ n` of `Localization.Away f` dying in
  `Localization.AtPrime (pointPrime I x)` has `g * r = 0` for some `g ∉ pointPrime I x`, and then
  it dies already in `Localization.Away (f * g)`, in which `g` is invertible.

## Which criterion this is proved against, and why not the other one

`FormalSpectrum.isStalkLimit_iff_awayCompletion` (`FormalSchemes.StructureSheafStalkComparison`),
whose injectivity half names `FormalSpectrum.basicOpenRes` — the structure-sheaf restriction — and
**not** `FormalSpectrum.isStalkLimit_iff_awayCompletionRestrict`
(`FormalSchemes.StructureSheafStalkAlgebraic`), whose two halves are both algebraic.

The sheaf in `FormalSpectrum.basicOpenRes` costs nothing at `⊥`. The element the injectivity half
is handed is `r / f ^ n` with `r` and `f` in `R`, so the only property of the restriction the
argument uses is that it is a map **under `R`** — which is exactly
`FormalSpectrum.basicOpenRes_comp_awayCompletionHom`, the square that pins `basicOpenRes` down on
the image of `R`. That image is where the whole computation lives, so the identification of
`basicOpenRes` with `FormalSpectrum.awayCompletionRestrict` is never needed. Taking the algebraic
criterion instead would import `FormalSchemes.BasicOpenRestrictionIdentification` and carry this
file's forward closure from **39** to **47** in exchange for nothing.

## No topology hypothesis, and what that does *not* say

`FormalSpectrum.basicOpenRes_comp_awayCompletionHom` carries `[TopologicalSpace R]` and
`IsAdicRing I`. At `⊥` both are discharged **inside the proof**: `FormalSpectrum.IsStalkLimit`,
`FormalSpectrum I`, `FormalSpectrum.basicOpen`, `FormalSpectrum.basicOpenRes` and
`FormalSpectrum.awayCompletion` are all instance-free, so no statement below mentions a topology
and a proof is free to pick one; the `⊥`-adic topology *is* the discrete topology, so
`instIsAdicRingBotOfDiscreteTopology` (`FormalSchemes.AdicRing`) supplies `IsAdicRing ⊥` from
`DiscreteTopology R`, which every ring admits.

**This must not be read as making the general case instance-free**, but the reason is narrower
than an earlier version of this paragraph claimed. `IsAdicRing I` extends `IsAdicComplete I R` and
adds `IsAdic I`, which is the assertion that the ambient topology *is* `Ideal.adicTopology I`; so a
choice of topology discharges the `IsAdic` half by `rfl` at **every** ideal, not only at `⊥`
(`isAdicRing_adicTopology`, `FormalSchemes.StructureSheafStalkNilpotent`). What no topology
supplies is `IsAdicComplete I R`, which is a condition on `I` and `R`. The manoeuvre therefore
reaches exactly as far as `I`-adic completeness does — here, and at every nilpotent ideal of
definition (`FormalSpectrum.isStalkLimit_of_isNilpotent`, same module) — and no further. Whether
`FormalSpectrum.basicOpenRes_comp_awayCompletionHom` — whose statement is instance-free — admits an
instance-free *proof* at a general `I` is the question `FormalSchemes.StructureSheafStalkAlgebraic`
records as open, and nothing here answers it.
`FormalSpectrum.basicOpenRes_eq_zero_of_mul_eq_zero` below is stated at a general `I`, and there it
carries both hypotheses.

## Placement

A leaf over `FormalSchemes.StructureSheafStalkComparison` and
`FormalSchemes.AwayCompletionRestrict`: forward closure **39**, reverse closure **1** — only
`FormalSchemes.StructureSheafStalkNilpotent`, which widens the value below to every nilpotent
ideal of definition and reuses the general-`I` lemmas here rather than reproving them.

`FormalSchemes.AwayCompletionRestrict` is the second import and buys three modules; what it buys
is `FormalSpectrum.isUnit_awayCompletionHom_of_basicOpen_le`, and the special case needed below —
that `f` and `g` are invertible in `R{1/f * g}` — is elementary enough to reprove, which would
save those three modules at the price of a second proof of a lemma the tree already has. The
reuse is the better trade at three modules; it would not be at thirty.

## Main results

* `FormalSpectrum.awayToAtPrimeCompletion_algebraMap`: the comparison map on the image of the
  localization is the localization map — true at every `I`, and the identification the `⊥` case
  runs on.
* `FormalSpectrum.basicOpenRes_eq_zero_of_mul_eq_zero`: at every `I`, the restriction to `D(e)`
  kills an element of `R{1/f}` whose numerator is killed by a `g` invertible on `D(e)`.
* `FormalSpectrum.exists_awayToAtPrimeCompletion_eq_bot`,
  `FormalSpectrum.exists_basicOpenRes_eq_zero_bot`: the surjectivity and injectivity halves at `⊥`.
* `FormalSpectrum.isStalkLimit_bot`: **`FormalSpectrum.IsStalkLimit (⊥ : Ideal R) x` holds**, at
  every point of every `Spf (R, ⊥)`.
* `FormalSpectrum.exists_isStalkLimit_bot`: the predicate is non-vacuous.

## What is *not* proved here

**Anything at all about a nonzero ideal of definition.** `FormalSpectrum.IsStalkLimit` at `I ≠ ⊥`
is exactly as open as it was before this file, in both directions, and nothing below is evidence
in either direction about it.

**The recorded obstruction is not surmounted here — it does not arise.**
`FormalSchemes.StructureSheafStalkComparison` records that an element killed by
`FormalSpectrum.awayToAtPrimeCompletion` is killed at each level `n` by a `g` that may depend on
`n`, while the injectivity half needs one `g` serving every level. At `⊥` the tower
`R_p ⧸ (I · R_p) ^ (n + 1)` is constant at `Localization.AtPrime (pointPrime ⊥ x)` from level 0
on, so there are no levels to be uniform over and the difficulty is absent rather than defeated. A
reader must **not** take this file as licence to restate the general question as open only in the
Noetherian case: it is open at every nonzero ideal of definition, Noetherian or not.

**Nothing under a Noetherian hypothesis.** `Submodule.fg_bot` is the only finiteness fact used and
it is free.

**No comparison with `Spec`.** `FormalSpectrum.specIsoSpfBot` (`FormalSchemes.SpfDiscrete`,
EGA I 10.1.6) identifies `Spec A` with `Spf (A, ⊥)` for `A` discrete, which is the geometric reason
`⊥` is the degenerate case; that module is deliberately **not** imported — it would take this
file's forward closure from 39 to 84 — and no statement below is made through that isomorphism. In
particular nothing here says that the two structure sheaves or their stalks agree.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1.6 and §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX).
-/

noncomputable section

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R]

/-! ### Three computations that need no `⊥` -/

/-- **A point avoiding `f` in the prime below it lies in `D(f)`**, the converse of
`FormalSpectrum.notMem_pointPrime_of_mem_basicOpen`. Both directions are definitional:
`FormalSpectrum.pointPrime` is the contraction of the point's prime along `Ideal.Quotient.mk I`,
and `FormalSpectrum.mem_basicOpen` is `Iff.rfl`. The tree carried only the forward direction; this
is the other one, and it is what turns the denominator of a fraction in
`Localization.AtPrime (pointPrime I x)` into a basic open through `x`. -/
theorem mem_basicOpen_of_notMem_pointPrime (I : Ideal R) (x : FormalSpectrum I) {f : R}
    (hf : f ∉ pointPrime I x) : x ∈ basicOpen I f :=
  hf

/-- **The comparison map on the image of the localization is the localization map.** This is
`AdicCompletion.mapCompletion_of` at `FormalSpectrum.awayToAtPrime`, and it holds at every ideal of
definition; at `⊥` the two structural maps are bijections, which is what makes it a complete
description of `FormalSpectrum.awayToAtPrimeCompletion` there. -/
theorem awayToAtPrimeCompletion_algebraMap (I : Ideal R) (x : FormalSpectrum I) (hI : I.FG)
    {f : R} (hf : x ∈ basicOpen I f) (a : Localization.Away f) :
    awayToAtPrimeCompletion I x hI hf (algebraMap (Localization.Away f) (awayCompletion I f) a) =
      algebraMap (Localization.AtPrime (pointPrime I x))
        (AdicCompletion (pointIdeal I x) (Localization.AtPrime (pointPrime I x)))
        (awayToAtPrime I x hf a) :=
  AdicCompletion.mapCompletion_of _ _ _ a

/-- **`FormalSpectrum.awayToAtPrime` carries a fraction to the fraction with the same numerator and
denominator.** The denominator is a power of `f`, hence avoids the prime under a point of `D(f)`,
so it is a legitimate denominator on the right as well. Both sides are pinned by
`IsLocalization.eq_mk'_iff_mul_eq` against `FormalSpectrum.awayToAtPrime_algebraMap`. -/
theorem awayToAtPrime_mk' (I : Ideal R) (x : FormalSpectrum I) {f : R} (hf : x ∈ basicOpen I f)
    (r : R) (m : Submonoid.powers f) (hm : (↑m : R) ∈ (pointPrime I x).primeCompl) :
    awayToAtPrime I x hf (IsLocalization.mk' (Localization.Away f) r m) =
      IsLocalization.mk' (Localization.AtPrime (pointPrime I x)) r ⟨(m : R), hm⟩ := by
  rw [IsLocalization.eq_mk'_iff_mul_eq, ← awayToAtPrime_algebraMap I x hf (m : R), ← map_mul,
    IsLocalization.mk'_spec, awayToAtPrime_algebraMap]

/-- **A fraction of `R{1/f}` cleared of its denominator.** `IsLocalization.mk'_spec` pushed along
the structural map `R_f → R{1/f}`, which is what lets the injectivity half below be run entirely on
the image of `R`, where `FormalSpectrum.basicOpenRes_comp_awayCompletionHom` determines the
restriction. -/
theorem algebraMap_mk'_mul_awayCompletionHom (I : Ideal R) {f : R} (r : R)
    (m : Submonoid.powers f) :
    algebraMap (Localization.Away f) (awayCompletion I f)
        (IsLocalization.mk' (Localization.Away f) r m) * awayCompletionHom I f (m : R) =
      awayCompletionHom I f r := by
  rw [awayCompletionHom, RingHom.comp_apply, RingHom.comp_apply, ← map_mul,
    IsLocalization.mk'_spec]

/-! ### The restriction kills a fraction whose numerator is killed -/

section Restriction

variable [TopologicalSpace R]

/-- **The restriction to `D(e)` kills `r / m` when `g * r = 0` and `g` is invertible on `D(e)`**,
at any ideal of definition. The hypothesis `ha` is the fraction cleared of its denominator, so the
proof only ever applies `FormalSpectrum.basicOpenRes` to elements of the image of `R`, where
`FormalSpectrum.basicOpenRes_comp_awayCompletionHom` says what it does. The two invertibility facts
are `FormalSpectrum.isUnit_awayCompletionHom_of_basicOpen_le`, once at `g` and once at `f`, the
latter raised to the power that produced `m`.

This is where the two instance hypotheses of this file's route live; see the module docstring for
why the `⊥` statements below carry neither. -/
theorem basicOpenRes_eq_zero_of_mul_eq_zero (I : Ideal R) [IsAdicRing I] (hI : I.FG)
    {f g e r m : R} (hm : m ∈ Submonoid.powers f) (hle : basicOpen I e ≤ basicOpen I f)
    (hleg : basicOpen I e ≤ basicOpen I g) {a : awayCompletion I f}
    (ha : a * awayCompletionHom I f m = awayCompletionHom I f r) (hgr : g * r = 0) :
    basicOpenRes I hle a = 0 := by
  have key : ∀ t : R, awayCompletionHom I e t = basicOpenRes I hle (awayCompletionHom I f t) :=
    fun t => (RingHom.congr_fun (basicOpenRes_comp_awayCompletionHom I hle) t).symm
  have hug : IsUnit (awayCompletionHom I e g) :=
    isUnit_awayCompletionHom_of_basicOpen_le I _ _ hI hleg
  obtain ⟨n, rfl⟩ := hm
  have hum : IsUnit (awayCompletionHom I e (f ^ n)) := by
    rw [map_pow]
    exact (isUnit_awayCompletionHom_of_basicOpen_le I _ _ hI hle).pow n
  have h1 : basicOpenRes I hle a * awayCompletionHom I e (f ^ n) = awayCompletionHom I e r := by
    rw [key (f ^ n), key r, ← map_mul, ha]
  have h2 : awayCompletionHom I e r = 0 := by
    refine hug.mul_right_eq_zero.mp ?_
    rw [← map_mul, hgr, map_zero]
  rw [h2] at h1
  exact hum.mul_left_eq_zero.mp h1

end Restriction

/-! ### `Spf (R, ⊥)`: every completion in the criterion is the ring it completes -/

/-- The ideal of definition of the stalk tower is `⊥` when the ideal of definition is: it is the
extension of `I` to `Localization.AtPrime (pointPrime I x)`, and `Ideal.map_bot`. -/
theorem pointIdeal_bot (x : FormalSpectrum (⊥ : Ideal R)) : pointIdeal (⊥ : Ideal R) x = ⊥ := by
  rw [pointIdeal, Ideal.map_bot]

/-- The local ring is `⊥`-adically complete for the ideal of definition of the stalk tower. Every
ring is `⊥`-adically complete with no hypotheses; the only work is transporting that along
`FormalSpectrum.pointIdeal_bot`, which is possible because `IsAdicComplete` is a `Prop`. -/
instance instIsAdicCompletePointIdealBot (x : FormalSpectrum (⊥ : Ideal R)) :
    IsAdicComplete (pointIdeal (⊥ : Ideal R) x)
      (Localization.AtPrime (pointPrime (⊥ : Ideal R) x)) := by
  rw [pointIdeal_bot]
  infer_instance

/-- `Localization.Away f` is complete for the ideal of definition of `R{1/f}` at `⊥`. -/
instance instIsAdicCompleteAwayBot (f : R) :
    IsAdicComplete ((⊥ : Ideal R).map (algebraMap R (Localization.Away f)))
      (Localization.Away f) := by
  rw [Ideal.map_bot]
  infer_instance

/-- **`R{1/f}` is `Localization.Away f` at `⊥`**, in the direction the surjectivity half needs. -/
theorem surjective_algebraMap_awayCompletion_bot (f : R) :
    Function.Surjective (algebraMap (Localization.Away f) (awayCompletion (⊥ : Ideal R) f)) :=
  (AdicCompletion.ofAlgEquiv _).surjective

/-- **The completion of `Localization.AtPrime (pointPrime ⊥ x)` is itself at `⊥`**, in the
direction the injectivity half needs. -/
theorem injective_algebraMap_atPrimeCompletion_bot (x : FormalSpectrum (⊥ : Ideal R)) :
    Function.Injective (algebraMap (Localization.AtPrime (pointPrime (⊥ : Ideal R) x))
      (AdicCompletion (pointIdeal (⊥ : Ideal R) x)
        (Localization.AtPrime (pointPrime (⊥ : Ideal R) x)))) :=
  (AdicCompletion.ofAlgEquiv _).injective

/-- **The comparison map at `⊥` is the localization map `R_f → R_p`**, conjugated by
`AdicCompletion.ofAlgEquiv` on both sides. Since both conjugating maps are ring isomorphisms at
`⊥`, this determines `FormalSpectrum.awayToAtPrimeCompletion` completely there; it is
`FormalSpectrum.awayToAtPrimeCompletion_algebraMap` read through
`AdicCompletion.ofAlgEquiv_apply`. -/
theorem awayToAtPrimeCompletion_bot (x : FormalSpectrum (⊥ : Ideal R)) {f : R}
    (hf : x ∈ basicOpen (⊥ : Ideal R) f) (a : Localization.Away f) :
    awayToAtPrimeCompletion (⊥ : Ideal R) x Submodule.fg_bot hf
        (AdicCompletion.ofAlgEquiv _ a) =
      AdicCompletion.ofAlgEquiv _ (awayToAtPrime (⊥ : Ideal R) x hf a) :=
  awayToAtPrimeCompletion_algebraMap _ x _ hf a

/-! ### The two halves of the criterion at `⊥` -/

/-- **The surjectivity half at `⊥`**, and it needs no topology on `R` whatever: every element of
the completed local ring is `r / s` with `s ∉ p`, `s ∉ p` says `x ∈ D(s)`
(`FormalSpectrum.mem_basicOpen_of_notMem_pointPrime`), and the same fraction read in `R{1/s}` maps
to it by `FormalSpectrum.awayToAtPrime_mk'`. -/
theorem exists_awayToAtPrimeCompletion_eq_bot (x : FormalSpectrum (⊥ : Ideal R))
    (b : AdicCompletion (pointIdeal (⊥ : Ideal R) x)
      (Localization.AtPrime (pointPrime (⊥ : Ideal R) x))) :
    ∃ (f : R) (hf : x ∈ basicOpen (⊥ : Ideal R) f) (a : awayCompletion (⊥ : Ideal R) f),
      awayToAtPrimeCompletion (⊥ : Ideal R) x Submodule.fg_bot hf a = b := by
  obtain ⟨c, rfl⟩ := (AdicCompletion.ofAlgEquiv (pointIdeal (⊥ : Ideal R) x)).surjective b
  obtain ⟨⟨r, s⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (pointPrime (⊥ : Ideal R) x).primeCompl c
  refine ⟨(s : R), mem_basicOpen_of_notMem_pointPrime _ x s.2,
    algebraMap (Localization.Away (s : R)) _
      (IsLocalization.mk' (Localization.Away (s : R)) r ⟨(s : R), Submonoid.mem_powers _⟩), ?_⟩
  rw [awayToAtPrimeCompletion_algebraMap, awayToAtPrime_mk' _ x _ r _ s.2]
  rfl

/-- **The injectivity half at `⊥`**, and it carries no topology either: the two hypotheses that
`FormalSpectrum.basicOpenRes_eq_zero_of_mul_eq_zero` needs are discharged inside the proof by
giving `R` the discrete topology, which is legitimate because the statement mentions no topology
and the `⊥`-adic topology is the discrete one. See the module docstring; the manoeuvre is
available wherever `R` is adically complete for the ideal of definition, which at `⊥` is free.

The mathematics is the standard fact: an element `r / f ^ n` of `Localization.Away f` dying in
`Localization.AtPrime (pointPrime ⊥ x)` has `g * r = 0` for some `g ∉ pointPrime ⊥ x`
(`IsLocalization.mk'_eq_zero_iff`), and `D(f * g)` is then a basic open through `x` inside `D(f)`
on which `g` is invertible, so the restriction kills it. -/
theorem exists_basicOpenRes_eq_zero_bot (x : FormalSpectrum (⊥ : Ideal R)) (f : R)
    (hf : x ∈ basicOpen (⊥ : Ideal R) f) (a : awayCompletion (⊥ : Ideal R) f)
    (ha : awayToAtPrimeCompletion (⊥ : Ideal R) x Submodule.fg_bot hf a = 0) :
    ∃ (e : R) (_ : x ∈ basicOpen (⊥ : Ideal R) e)
      (hle : basicOpen (⊥ : Ideal R) e ≤ basicOpen (⊥ : Ideal R) f),
      basicOpenRes (⊥ : Ideal R) hle a = 0 := by
  letI : TopologicalSpace R := ⊥
  haveI : DiscreteTopology R := ⟨rfl⟩
  obtain ⟨α, rfl⟩ := surjective_algebraMap_awayCompletion_bot f a
  obtain ⟨⟨r, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) α
  rw [awayToAtPrimeCompletion_algebraMap] at ha
  have hmc : (↑m : R) ∈ (pointPrime (⊥ : Ideal R) x).primeCompl :=
    Submonoid.powers_le.mpr (notMem_pointPrime_of_mem_basicOpen (⊥ : Ideal R) x hf) m.2
  rw [awayToAtPrime_mk' _ x hf r m hmc, ← map_zero (algebraMap
    (Localization.AtPrime (pointPrime (⊥ : Ideal R) x))
    (AdicCompletion (pointIdeal (⊥ : Ideal R) x)
      (Localization.AtPrime (pointPrime (⊥ : Ideal R) x))))] at ha
  replace ha := injective_algebraMap_atPrimeCompletion_bot x ha
  obtain ⟨⟨g, hg⟩, hgr⟩ := (IsLocalization.mk'_eq_zero_iff r ⟨(m : R), hmc⟩).mp ha
  have hle : basicOpen (⊥ : Ideal R) (f * g) ≤ basicOpen (⊥ : Ideal R) f := by
    rw [basicOpen_mul]
    exact inf_le_left
  have hleg : basicOpen (⊥ : Ideal R) (f * g) ≤ basicOpen (⊥ : Ideal R) g := by
    rw [basicOpen_mul]
    exact inf_le_right
  have hxe : x ∈ basicOpen (⊥ : Ideal R) (f * g) := by
    rw [basicOpen_mul]
    exact ⟨hf, mem_basicOpen_of_notMem_pointPrime (⊥ : Ideal R) x hg⟩
  exact ⟨f * g, hxe, hle, basicOpenRes_eq_zero_of_mul_eq_zero (⊥ : Ideal R) Submodule.fg_bot m.2
    hle hleg (algebraMap_mk'_mul_awayCompletionHom _ r m) hgr⟩

/-! ### The value -/

/-- **`FormalSpectrum.IsStalkLimit` holds at `I = ⊥`**, at every point of `Spf (R, ⊥)` and for
every commutative ring `R`: the stalk of `O_{Spf (R, ⊥)}` at `x` is the limit of the stalks of the
thickenings.

**This is the first value the predicate has been given at any ring, in either direction.** It is
`FormalSpectrum.isStalkLimit_iff_awayCompletion` with its two halves supplied by
`FormalSpectrum.exists_basicOpenRes_eq_zero_bot` and
`FormalSpectrum.exists_awayToAtPrimeCompletion_eq_bot`.

**It says nothing about a nonzero ideal of definition**, where the question is exactly as open as
before; the module docstring records why the obstruction to the general case does not arise at
`⊥` rather than being surmounted here. -/
theorem isStalkLimit_bot (x : FormalSpectrum (⊥ : Ideal R)) : IsStalkLimit (⊥ : Ideal R) x := by
  rw [isStalkLimit_iff_awayCompletion (⊥ : Ideal R) x Submodule.fg_bot]
  exact ⟨fun f hf a ha => exists_basicOpenRes_eq_zero_bot x f hf a ha,
    exists_awayToAtPrimeCompletion_eq_bot x⟩

/-- `Spf (R, ⊥)` has a point when `R` is nontrivial: it is `Spec (R ⧸ ⊥)`, and `⊥ ≠ ⊤`. -/
theorem nonempty_formalSpectrum_bot [Nontrivial R] : Nonempty (FormalSpectrum (⊥ : Ideal R)) := by
  haveI : Nontrivial (R ⧸ (⊥ : Ideal R)) := Ideal.Quotient.nontrivial_iff.mpr bot_ne_top
  exact inferInstanceAs (Nonempty (PrimeSpectrum (R ⧸ (⊥ : Ideal R))))

/-- **`FormalSpectrum.IsStalkLimit` is not vacuous.** `FormalSpectrum.isStalkLimit_bot` holds at
every point of `Spf (R, ⊥)`, and `Spf (R, ⊥)` has a point as soon as `R` is nontrivial, so there
really is a ring, an ideal of definition and a point at which the predicate holds. Without this a
later reader could not distinguish `FormalSpectrum.IsStalkLimit` from a predicate that is false
everywhere. -/
theorem exists_isStalkLimit_bot [Nontrivial R] :
    ∃ x : FormalSpectrum (⊥ : Ideal R), IsStalkLimit (⊥ : Ideal R) x :=
  ⟨(nonempty_formalSpectrum_bot (R := R)).some, isStalkLimit_bot _⟩

end FormalSpectrum
