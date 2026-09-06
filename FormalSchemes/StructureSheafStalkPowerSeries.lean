import FormalSchemes.StructureSheafStalkAlgebraic
import FormalSchemes.StructureSheafStalkNilpotent
import Mathlib.RingTheory.PowerSeries.Inverse

set_option linter.style.header false

/-!
# `FormalSpectrum.IsStalkLimit` at `(X) ⊆ R⟦X⟧`

`FormalSpectrum.IsStalkLimit` — the stalk half of EGA I 10.8 — had two values before this file,
`FormalSpectrum.isStalkLimit_bot` at `I = ⊥` and `FormalSpectrum.isStalkLimit_of_isNilpotent` at
every finitely generated nilpotent ideal of definition. Both are in the same degenerate regime:
`FormalSchemes.StructureSheafStalkNilpotent`'s own docstring records that for `J ^ k = ⊥` the two
completions in `FormalSpectrum.isStalkLimit_iff_awayCompletion` collapse to the rings they
complete before the argument starts, so the recorded obstruction is never faced.

This file moves to `R⟦X⟧ = PowerSeries R` with the ideal of definition `Ideal.span {X}`, which is
**not** nilpotent (`FormalSpectrum.not_isNilpotent_powerSeriesXIdeal`), and does three things.

**The sheaf-free criterion becomes applicable, and instance-free.**
`FormalSpectrum.isStalkLimit_iff_awayCompletionRestrict`
(`FormalSchemes.StructureSheafStalkAlgebraic`) carries `[TopologicalSpace R]` and `IsAdicRing I`,
and that module's docstring settles that the two are not removable from its signature. Until
`FormalSchemes.StructureSheafStalkNilpotent` there was no way to *pay* that price above `⊥`:
`instIsAdicRingBotOfDiscreteTopology` is stated at `⊥` only. `isAdicRing_adicTopology` supplies
`@IsAdicRing S _ (Ideal.adicTopology J) J` from `[IsAdicComplete J S]` at every ideal, and Mathlib
supplies the `IsAdicComplete` here (`Mathlib/RingTheory/AdicCompletion/Completeness.lean` carries
an anonymous `instance : IsAdicComplete (.span {X}) (PowerSeries R)`; it is reached by
`inferInstance`, not by name). So `FormalSpectrum.isStalkLimit_powerSeriesX_iff` below is the
criterion instantiated at `(X) ⊆ R⟦X⟧` — and since neither instance occurs in the conclusion,
**the resulting `Iff` carries no topology and no `IsAdicRing` at all.**

**The space is `Spec R`, and the basic opens are those of `Spec R`.**
`FormalSpectrum.powerSeriesXHomeo` is `Spf (R⟦X⟧, (X)) ≃ₜ Spec R`, and
`FormalSpectrum.basicOpen_powerSeriesX_eq_constantCoeff` says `D(f)` depends on `f` only through
its constant term. This is where the case differs from `⊥` and from every nilpotent ideal of
definition: there the underlying space is the whole of `Spec R`, here it is a proper closed
subspace of `Spec R⟦X⟧`.

**A value, at every point of `Spf (k⟦X⟧, (X))` for `k` a field.** That is
`FormalSpectrum.isStalkLimit_powerSeriesX_field`, and it is the first value of
`FormalSpectrum.IsStalkLimit` at an ideal of definition that is not nilpotent. It is a corollary of
a criterion that has nothing to do with power series:
`FormalSpectrum.isStalkLimit_of_isUnit_notMem_pointPrime` holds `IsStalkLimit I x` whenever every
element outside `FormalSpectrum.pointPrime I x` is a unit of `R` — that is, at the closed point of
a local ring (`FormalSpectrum.isStalkLimit_of_pointPrime_eq_maximalIdeal`).

**And a value at the closed point of `Spf (R⟦X⟧, (X))` for every local `R`.** That criterion is
stated at an arbitrary finitely generated ideal of definition and it now has a consumer at `(X)`:
`FormalSpectrum.isStalkLimit_powerSeriesXClosedPoint`, with no domain, factorisation, countability
or Noetherian hypothesis. All of the work is `FormalSpectrum.pointPrime_powerSeriesX`, which
computes the prime of `R⟦X⟧` under *any* point of this space as a `PowerSeries.constantCoeff`
preimage, and `FormalSpectrum.maximalIdeal_powerSeries`, which reads that preimage at the closed
point back as the maximal ideal of `R⟦X⟧`.

**It is the first point at which the predicate is decided in a space with more than one point.**
The field value is at every point of a one-point space, and the generic-point cluster downstream
is at a point that is not closed and answers differently for different `R`. As soon as `R` is a
local **domain** that is not a field, `Spf (R⟦X⟧, (X))` carries
`FormalSpectrum.powerSeriesXClosedPoint` and a separate generic point, settled by different
arguments under different hypotheses. **That is not a claim that the predicate ever disagrees at
the two**, and nothing below makes one; see
`FormalSpectrum.isStalkLimit_powerSeriesXClosedPoint` for what a ring at which they disagree has to
be, and for the leaf downstream that exhibits one.

## Which difficulty this value faces, and which it does not

**The filtration does not reach `⊥`, and that is new.** At `⊥` the stalk tower is constant from
level `0`; at `J ^ k = ⊥` it is constant from level `k - 1`, and
`FormalSchemes.StructureSheafStalkNilpotent`'s whole argument is read off that. Here
`FormalSpectrum.pow_powerSeriesXIdeal_ne_bot` says `(X) ^ n ≠ ⊥` for every `n` as soon as `R` is
nontrivial, so that argument has no analogue: `FormalSpectrum.awayCompletion` and the completion of
the local ring are not identified with the rings they complete by any power of the ideal vanishing.
That the levels of the stalk tower are moreover pairwise distinct is not proved below.

**What collapses instead is the colimit, and this file's proof is entirely about that.** The
obstruction `FormalSchemes.StructureSheafStalkComparison` records is that the witness `g` produced
at level `n` may depend on `n`, while the injectivity half needs one `g` serving every level. The
proof below never produces a witness at all: at the closed point of a local ring every `f` with
`x ∈ D(f)` is a unit, so `Localization.Away f` and `Localization.AtPrime (pointPrime I x)` are both
`R` (`IsLocalization.atUnits`), `FormalSpectrum.awayToAtPrime` is a bijection between them, and the
completion of a bijection is a bijection (`AdicCompletion.bijective_mapCompletion`). The injectivity
half is then discharged with `D(f)` itself as the smaller basic open, so no uniformity over levels
is ever asked for.

**So the obstruction is avoided, not surmounted**, exactly as at `⊥` and at a nilpotent ideal —
only by a different mechanism, and at a ring where the levels are infinite in number. Nothing below
is evidence about a point that is not closed.

## What is *not* proved here

**`FormalSpectrum.IsStalkLimit` at `(X) ⊆ R⟦X⟧` for a general commutative ring `R` is undecided,
in both directions, and nothing below decides it.** `FormalSpectrum.isStalkLimit_powerSeriesX_iff`
is a reformulation and not an answer; it is worth landing because it is the first time the
sheaf-free criterion has been available with its instance hypotheses discharged, not because it
settles anything.

**Neither half is attempted at a point of `Spf (R⟦X⟧, (X))` that is not closed.** The value below
covers `k` a field, where `Spf (k⟦X⟧, (X))` has a single point and it is closed. For a general `R`
the space is `Spec R` and a point that is not closed has a genuinely filtered system of basic opens
around it, which is the situation the recorded obstruction is about; this file says nothing about
it. A reader must not read "the first value at a non-nilpotent ideal of definition" as "the general
question is decided", and must not restate the general question as open only in the Noetherian case
— `k⟦X⟧` is Noetherian, and so is `R⟦X⟧` for `R` Noetherian.

**The direction the general case fails in is stated here as an expectation and is not proved
below.** The surjectivity half at `R = ℤ` and the generic point of `Spec ℤ` asks for every element
of the target to come from a single basic open; the sections over the basic open `D(m)` are an
`(X)`-adic completion of a localization of `ℤ⟦X⟧`, so an element of the target with a denominator
growing with the degree has no single `m` serving all degrees. **That computation is not carried
out below and no declaration below asserts it**; it is carried out in
`FormalSchemes.StructureSheafStalkPowerSeriesCounterexample`, where
`FormalSpectrum.not_isStalkLimit_powerSeriesXIntGenericPoint` confirms the expectation and refutes
`FormalSpectrum.IsStalkLimit` at that point. It is a statement about a *non-closed* point, so it is
consistent with everything this file proves — in particular neither
`FormalSpectrum.isStalkLimit_powerSeriesX_field` nor
`FormalSpectrum.isStalkLimit_powerSeriesXClosedPoint` is touched by it, and `ℤ` is not local, so
the latter says nothing at that ring at all.

**Nothing under a Noetherian hypothesis.** `Ideal.FG` of the ideal of definition is the only
finiteness assumption, and it is inherited from the criteria being applied; `Ideal.span {X}` is
generated by one element.

**No comparison with `Spec`.** `FormalSchemes.SpfDiscrete` is not imported — measured at **+42**
modules on top of this leaf's closure, and nothing here needs it — and no statement below is made
through `FormalSpectrum.specIsoSpfBot`.

## Placement

A new leaf over `FormalSchemes.StructureSheafStalkAlgebraic` and
`FormalSchemes.StructureSheafStalkNilpotent`: forward closure **49** project modules besides itself
(50 counted with itself), reverse closure **6**, the consumers being
`FormalSchemes.StructureSheafStalkPowerSeriesGeneric`,
`FormalSchemes.StructureSheafStalkPowerSeriesCounterexample` and the four leaves above them. The
Mathlib import `Mathlib/RingTheory/PowerSeries/Inverse.lean` is new to this leaf's closure but not
to the library's: it is already reached by the full `FormalSchemes` build, so it adds no build job.

`AdicCompletion.bijective_mapCompletion` mentions no formal geometry and would sit naturally in
`FormalSchemes.Completion` beside `AdicCompletion.mapCompletion_id` and
`AdicCompletion.mapCompletion_comp`, from which it is proved. It is **not** put there:
`FormalSchemes.Completion`'s reverse closure is **446** of the project's 558 modules, and it has
one consumer, here. This is the disposition `FormalSchemes.StructureSheafStalkNilpotent` recorded
for `isAdicRing_adicTopology` at `FormalSchemes.AdicRing`; if a second consumer appears the move is
worth re-costing.

## Main results

* `AdicCompletion.bijective_mapCompletion`: the completion of a bijection carrying one ideal of
  definition **onto** the other is a bijection.
* `FormalSpectrum.isStalkLimit_of_isUnit_notMem_pointPrime`,
  `FormalSpectrum.isStalkLimit_of_pointPrime_eq_maximalIdeal`: `IsStalkLimit` at the closed point
  of a local ring, at every finitely generated ideal of definition.
* `FormalSpectrum.powerSeriesXHomeo`, `FormalSpectrum.basicOpen_powerSeriesX_eq_constantCoeff`,
  `FormalSpectrum.mem_basicOpen_powerSeriesX_iff`: the space of `Spf (R⟦X⟧, (X))` is `Spec R`, and
  its basic opens — the ones both halves of the criterion quantify over — are those of `Spec R`.
* `FormalSpectrum.not_isNilpotent_powerSeriesXIdeal`: the target is outside the regime of the two
  existing values.
* `FormalSpectrum.pointPrime_powerSeriesX`: **the prime of `R⟦X⟧` under any point of
  `Spf (R⟦X⟧, (X))` is the `PowerSeries.constantCoeff` preimage of the prime it lies over**, at an
  arbitrary commutative ring. The general form of two computations that predate it.
* `FormalSpectrum.isStalkLimit_powerSeriesX_iff`: **the criterion at `(X) ⊆ R⟦X⟧`, with both
  instance hypotheses discharged.**
* `FormalSpectrum.maximalIdeal_powerSeries`, `FormalSpectrum.powerSeriesXClosedPoint`,
  `FormalSpectrum.isStalkLimit_powerSeriesXClosedPoint`: **the value at the closed point**, for
  every local `R`, and the maximal ideal of `R⟦X⟧` it is read through.
* `FormalSpectrum.isStalkLimit_powerSeriesX_field`: **the value**, at every point of
  `Spf (k⟦X⟧, (X))` for `k` a field — the case of the previous bullet in which the space has a
  single point.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX).
-/

noncomputable section

universe u

open PowerSeries

/-! ### Completion of a bijection -/

namespace AdicCompletion

variable {R S : Type u} [CommRing R] [CommRing S] {I : Ideal R} {J : Ideal S}

/-- A ring isomorphism carrying `I` onto `J` carries `J` back onto `I`. Stated separately because
`AdicCompletion.bijective_mapCompletion` needs it to name the map it composes with. -/
theorem map_symm_eq_of_map_eq (e : R ≃+* S) (hIJ : I.map (e : R →+* S) = J) :
    J.map (e.symm : S →+* R) = I := by
  subst hIJ
  rw [Ideal.map_map, show ((e.symm : S →+* R).comp (e : R →+* S)) = RingHom.id R from
    RingHom.ext fun x => e.symm_apply_apply x, Ideal.map_id]

/-- **The completion of a bijection is a bijection**, provided the bijection carries `I` *onto* `J`
rather than merely into it. There is nothing to compute: `AdicCompletion.mapCompletion_comp` and
`AdicCompletion.mapCompletion_id` say completion is a functor, and a functor sends an isomorphism
to an isomorphism.

The `Ideal.map` hypothesis is an equality because the inverse needs a continuity bound of its own,
and `I.map φ ≤ J` gives none: `J.map φ⁻¹ ≤ I` is exactly `J ≤ I.map φ`, the other containment. Both
`Ideal.FG` hypotheses are `AdicCompletion.mapCompletion`'s, one for each direction. -/
theorem bijective_mapCompletion (φ : R →+* S) (hbij : Function.Bijective φ)
    (hIJ : I.map φ = J) (hI : I.FG) (hJ : J.FG) :
    Function.Bijective (mapCompletion φ hIJ.le hJ) := by
  set e : R ≃+* S := RingEquiv.ofBijective φ hbij with he
  have hφe : (e : R →+* S) = φ := rfl
  have hψ : J.map (e.symm : S →+* R) = I := map_symm_eq_of_map_eq e (hφe ▸ hIJ)
  have key : ∀ {T : Type u} [CommRing T] (K : Ideal T) (hK : K.FG) (g : T →+* T)
      (hg : K.map g ≤ K), g = RingHom.id T → mapCompletion g hg hK = RingHom.id _ := by
    rintro T _ K hK g hg rfl
    exact mapCompletion_id hK
  have h1 : (mapCompletion (e.symm : S →+* R) hψ.le hI).comp (mapCompletion φ hIJ.le hJ) =
      RingHom.id _ := by
    rw [mapCompletion_comp φ (e.symm : S →+* R) hIJ.le hψ.le hJ hI hI]
    exact key I hI _ _ (RingHom.ext fun x => e.symm_apply_apply x)
  have h2 : (mapCompletion φ hIJ.le hJ).comp (mapCompletion (e.symm : S →+* R) hψ.le hI) =
      RingHom.id _ := by
    rw [mapCompletion_comp (e.symm : S →+* R) φ hψ.le hIJ.le hI hJ hJ]
    exact key J hJ _ _ (RingHom.ext fun x => e.apply_symm_apply x)
  have hli : Function.LeftInverse (mapCompletion (e.symm : S →+* R) hψ.le hI)
      (mapCompletion φ hIJ.le hJ) := fun a => DFunLike.congr_fun h1 a
  have hri : Function.RightInverse (mapCompletion (e.symm : S →+* R) hψ.le hI)
      (mapCompletion φ hIJ.le hJ) := fun b => DFunLike.congr_fun h2 b
  exact ⟨hli.injective, hri.surjective⟩

end AdicCompletion

/-- **A localization at a submonoid of units is the ring itself**, in the form the two localizations
below are used in: `algebraMap R S` is bijective. This is `IsLocalization.atUnits` read as a
statement about the structural map rather than as an `AlgEquiv`; the two differ by
`AlgEquiv.commutes` at `algebraMap R R = id`. -/
theorem bijective_algebraMap_of_le_isUnit {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (h : M ≤ IsUnit.submonoid R) :
    Function.Bijective (algebraMap R S) := by
  have hfun : ⇑(algebraMap R S) = ⇑(IsLocalization.atUnits R M h) := by
    funext r
    simp [((IsLocalization.atUnits R M h).commutes r).symm]
  rw [hfun]
  exact (IsLocalization.atUnits R M h).bijective

namespace FormalSpectrum

/-! ### `IsStalkLimit` at the closed point of a local ring -/

section Local

variable {R : Type u} [CommRing R] (I : Ideal R) (x : FormalSpectrum I)

/-- Membership in a basic open of `Spf R` is non-membership in the prime under the point. Both
directions are already on the tree — `FormalSpectrum.notMem_pointPrime_of_mem_basicOpen` and
`FormalSpectrum.mem_basicOpen_of_notMem_pointPrime`, both from
`FormalSchemes.StructureSheafStalkComparison` — and this is the `Iff` they make. -/
theorem mem_basicOpen_iff_notMem_pointPrime {f : R} :
    x ∈ basicOpen I f ↔ f ∉ pointPrime I x :=
  ⟨notMem_pointPrime_of_mem_basicOpen I x, mem_basicOpen_of_notMem_pointPrime I x⟩

/-- **The comparison map at a basic open is a bijection as soon as the localization map under it
is.** `FormalSpectrum.awayToAtPrimeCompletion` is `AdicCompletion.mapCompletion` of
`FormalSpectrum.awayToAtPrime`, and `FormalSpectrum.map_awayToAtPrime` supplies the `Ideal.map`
equality — not merely the containment — that `AdicCompletion.bijective_mapCompletion` asks for. -/
theorem bijective_awayToAtPrimeCompletion (hI : I.FG) {f : R} (hf : x ∈ basicOpen I f)
    (hbij : Function.Bijective (awayToAtPrime I x hf)) :
    Function.Bijective (awayToAtPrimeCompletion I x hI hf) :=
  AdicCompletion.bijective_mapCompletion _ hbij (map_awayToAtPrime I x hf) (hI.map _) (hI.map _)

/-- **At a point whose prime has only units outside it, every basic open through it computes the
local ring.** `x ∈ D(f)` gives `f ∉ pointPrime I x`, so `f` is a unit and `Localization.Away f` is
`R`; the whole of `(pointPrime I x).primeCompl` is units, so `Localization.AtPrime (pointPrime I x)`
is `R` too; and `FormalSpectrum.awayToAtPrime` is a map under `R`, so it is the composite of one
bijection with the inverse of the other. -/
theorem bijective_awayToAtPrime_of_isUnit (hu : ∀ g : R, g ∉ pointPrime I x → IsUnit g)
    {f : R} (hf : x ∈ basicOpen I f) : Function.Bijective (awayToAtPrime I x hf) := by
  have hAway : Function.Bijective (algebraMap R (Localization.Away f)) := by
    refine bijective_algebraMap_of_le_isUnit (Submonoid.powers f) ?_
    rintro s ⟨n, rfl⟩
    exact (hu f ((mem_basicOpen_iff_notMem_pointPrime I x).mp hf)).pow n
  have hAt : Function.Bijective (algebraMap R (Localization.AtPrime (pointPrime I x))) :=
    bijective_algebraMap_of_le_isUnit (pointPrime I x).primeCompl fun s hs => hu s hs
  constructor
  · intro a b hab
    obtain ⟨r, rfl⟩ := hAway.surjective a
    obtain ⟨r', rfl⟩ := hAway.surjective b
    rw [awayToAtPrime_algebraMap, awayToAtPrime_algebraMap] at hab
    rw [hAt.injective hab]
  · intro c
    obtain ⟨r, rfl⟩ := hAt.surjective c
    exact ⟨algebraMap R (Localization.Away f) r, awayToAtPrime_algebraMap I x hf r⟩

/-- **`FormalSpectrum.IsStalkLimit` holds at a point outside whose prime everything is a unit**, at
every finitely generated ideal of definition of every commutative ring.

Both halves of `FormalSpectrum.isStalkLimit_iff_awayCompletion` become bijectivity of a single map.
The injectivity half needs no smaller basic open at all: the element is already `0` on `D(f)`, so
`D(f)` itself serves and the smaller open is `f`. The surjectivity half is read at `f = 1`, where
`D(1) = ⊤` contains `x` unconditionally.

**The hypothesis is a statement about `x`, not about `R`.** It says the prime under `x` is the set
of non-units, so `R` is local and `x` is its closed point; see
`FormalSpectrum.isStalkLimit_of_pointPrime_eq_maximalIdeal`. -/
theorem isStalkLimit_of_isUnit_notMem_pointPrime (hI : I.FG)
    (hu : ∀ g : R, g ∉ pointPrime I x → IsUnit g) : IsStalkLimit I x := by
  have hone : x ∈ basicOpen I (1 : R) := by rw [basicOpen_one]; trivial
  rw [isStalkLimit_iff_awayCompletion I x hI]
  refine ⟨fun f hf a ha => ⟨f, hf, le_rfl, ?_⟩, fun b => ?_⟩
  · have hzero : a = 0 :=
      (bijective_awayToAtPrimeCompletion I x hI hf
        (bijective_awayToAtPrime_of_isUnit I x hu hf)).injective (by rw [ha, map_zero])
    rw [hzero, map_zero]
  · obtain ⟨a, ha⟩ := (bijective_awayToAtPrimeCompletion I x hI hone
      (bijective_awayToAtPrime_of_isUnit I x hu hone)).surjective b
    exact ⟨1, hone, a, ha⟩

/-- **`FormalSpectrum.IsStalkLimit` at the closed point of a local ring.** The hypothesis is that
`x` is the closed point, spelled as an equality of `FormalSpectrum.pointPrime I x` with the maximal
ideal; `IsLocalRing.notMem_maximalIdeal` turns it into the unit hypothesis of
`FormalSpectrum.isStalkLimit_of_isUnit_notMem_pointPrime`.

The ideal of definition is arbitrary (finitely generated) — in particular this is *not* a statement
about `I = IsLocalRing.maximalIdeal R`, though that is the case in which the hypothesis on `x` is
automatic, `Spf (R, m)` being a single point. -/
theorem isStalkLimit_of_pointPrime_eq_maximalIdeal [IsLocalRing R] (hI : I.FG)
    (h : pointPrime I x = IsLocalRing.maximalIdeal R) : IsStalkLimit I x :=
  isStalkLimit_of_isUnit_notMem_pointPrime I x hI fun _ hg =>
    IsLocalRing.notMem_maximalIdeal.mp (h ▸ hg)

end Local

/-! ### The ideal of definition `(X) ⊆ R⟦X⟧` -/

section PowerSeriesX

variable (R : Type u) [CommRing R]

/-- The ideal of definition of this file: `(X) ⊆ R⟦X⟧`. An `abbrev` rather than a `def` so that
Mathlib's anonymous `IsAdicComplete (.span {X}) (PowerSeries R)` instance is still found through
it. -/
abbrev powerSeriesXIdeal : Ideal (PowerSeries R) := Ideal.span {(X : PowerSeries R)}

/-- `(X)` is generated by one element. Every criterion in this cluster takes `Ideal.FG` of the
ideal of definition; a library search over this statement turns nothing up, so it is named. -/
theorem fg_powerSeriesXIdeal : (powerSeriesXIdeal R).FG := ⟨{X}, by simp⟩

/-- `(X)` is the kernel of `PowerSeries.constantCoeff`: `X ∣ φ` says the constant term vanishes
(`PowerSeries.X_dvd_iff`), and membership in a principal ideal is divisibility. -/
theorem powerSeriesXIdeal_eq_ker : powerSeriesXIdeal R = RingHom.ker (constantCoeff (R := R)) := by
  ext φ
  rw [powerSeriesXIdeal, Ideal.mem_span_singleton, RingHom.mem_ker, X_dvd_iff]

/-- **`R⟦X⟧ ⧸ (X) ≃+* R`**, the identification that makes the underlying space of
`Spf (R⟦X⟧, (X))` the space of `Spec R`. -/
def powerSeriesXQuotientEquiv : (PowerSeries R ⧸ powerSeriesXIdeal R) ≃+* R :=
  (Ideal.quotEquivOfEq (powerSeriesXIdeal_eq_ker R)).trans
    (RingHom.quotientKerEquivOfSurjective constantCoeff_surj)

/-- **The space of `Spf (R⟦X⟧, (X))` is `Spec R`.** `FormalSpectrum I` is `Spec (R ⧸ I)` by
definition, so this is `FormalSpectrum.powerSeriesXQuotientEquiv` read on prime spectra.

This is where `(X)` leaves the regime of the two existing values of `FormalSpectrum.IsStalkLimit`:
at `⊥`, and at every nilpotent ideal of definition, the space is the whole of `Spec` of the ambient
ring, and here it is the proper closed subspace `V(X) ⊆ Spec R⟦X⟧`. -/
def powerSeriesXHomeo : FormalSpectrum (powerSeriesXIdeal R) ≃ₜ PrimeSpectrum R :=
  PrimeSpectrum.homeomorphOfRingEquiv (powerSeriesXQuotientEquiv R)

/-- **A basic open of `Spf (R⟦X⟧, (X))` depends on `f` only through its constant term**: `D(f)` is
`D(C (constantCoeff f))`, because `f - C (constantCoeff f)` is divisible by `X`
(`PowerSeries.sub_const_eq_shift_mul_X`) and `FormalSpectrum.basicOpen` reads `f` modulo the ideal
of definition. So the basic opens of `Spf (R⟦X⟧, (X))` are the basic opens of `Spec R` transported
along `FormalSpectrum.powerSeriesXHomeo`. -/
theorem basicOpen_powerSeriesX_eq_constantCoeff (f : PowerSeries R) :
    basicOpen (powerSeriesXIdeal R) f =
      basicOpen (powerSeriesXIdeal R) (PowerSeries.C (constantCoeff f)) := by
  have hmem : f - PowerSeries.C (constantCoeff f) ∈ powerSeriesXIdeal R :=
    Ideal.mem_span_singleton.mpr ⟨_, by rw [sub_const_eq_shift_mul_X, mul_comm]⟩
  rw [basicOpen, basicOpen,
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem f (PowerSeries.C (constantCoeff f))).mpr hmem]

/-- **Membership in a basic open of `Spf (R⟦X⟧, (X))`, written out.** `x ∈ D(f)` says that the
constant term of `f`, read back into `R⟦X⟧` as a constant power series, is outside the prime under
`x` — so the quantifier `∀ f, x ∈ D(f) → …` in both halves of
`FormalSpectrum.isStalkLimit_powerSeriesX_iff` ranges over the constant terms, i.e. over the basic
opens of `Spec R` through the corresponding prime, and over nothing else. -/
theorem mem_basicOpen_powerSeriesX_iff (x : FormalSpectrum (powerSeriesXIdeal R))
    (f : PowerSeries R) :
    x ∈ basicOpen (powerSeriesXIdeal R) f ↔
      PowerSeries.C (constantCoeff f) ∉ pointPrime (powerSeriesXIdeal R) x := by
  rw [basicOpen_powerSeriesX_eq_constantCoeff, mem_basicOpen_iff_notMem_pointPrime]

/-- **The prime of `R⟦X⟧` under a point of `Spf (R⟦X⟧, (X))` is the `PowerSeries.constantCoeff`
preimage of the prime of `R` the point lies over.** Together with
`FormalSpectrum.powerSeriesXHomeo`, which identifies the space with `Spec R`, this says that the
points of `Spf (R⟦X⟧, (X))` are exactly the primes of `R⟦X⟧` of the form `constantCoeff ⁻¹ p`.

`FormalSpectrum.pointPrime` is a contraction along `Ideal.Quotient.mk (X)` by definition and
`FormalSpectrum.powerSeriesXHomeo` is a contraction along the inverse of
`FormalSpectrum.powerSeriesXQuotientEquiv`, so both sides are contractions of the same ideal of
`R⟦X⟧ ⧸ (X)`; the two ring maps agree because the equivalence sends `Ideal.Quotient.mk (X) f` to
`PowerSeries.constantCoeff f`. They are equal and not *definitionally* equal — the composite
reduces to `Ideal.Quotient.mk (X)` only through `RingEquiv.symm_apply_apply` — which is why the
proof ends in `RingHom.ext` rather than `rfl`.

**This is the general form of two computations that predate it**, and it explains why they could
not share a proof: `FormalSpectrum.pointPrime_powerSeriesXIdeal` is this at the unique point of
`Spec k` for `k` a field, and `FormalSpectrum.pointPrime_powerSeriesXGenericPoint` is this at `⊥`,
where the contraction of `⊥` is `RingHom.ker constantCoeff`, which is `(X)`. Neither is restated
or reproved here. -/
theorem pointPrime_powerSeriesX (x : FormalSpectrum (powerSeriesXIdeal R)) :
    pointPrime (powerSeriesXIdeal R) x =
      Ideal.comap (constantCoeff (R := R)) (powerSeriesXHomeo R x).asIdeal := by
  have hdef : pointPrime (powerSeriesXIdeal R) x =
      (x.asIdeal).comap (Ideal.Quotient.mk (powerSeriesXIdeal R)) := rfl
  have hhomeo : (powerSeriesXHomeo R x).asIdeal =
      (x.asIdeal).comap (powerSeriesXQuotientEquiv R).symm.toRingHom := rfl
  rw [hdef, hhomeo, Ideal.comap_comap]
  congr 1
  exact RingHom.ext fun f =>
    ((powerSeriesXQuotientEquiv R).symm_apply_apply (Ideal.Quotient.mk _ f)).symm

/-- **No power of `(X)` is `⊥`**, as soon as `R` is nontrivial: the coefficient of `X ^ k` in
`X ^ k` is `1`. -/
theorem pow_powerSeriesXIdeal_ne_bot [Nontrivial R] (k : ℕ) : powerSeriesXIdeal R ^ k ≠ ⊥ := by
  intro h
  have hx : (X : PowerSeries R) ^ k ∈ powerSeriesXIdeal R ^ k := by
    rw [Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  rw [h, Ideal.mem_bot] at hx
  have hcoeff := congrArg (PowerSeries.coeff k) hx
  simp at hcoeff

/-- **`(X)` is not nilpotent**, so neither `FormalSpectrum.isStalkLimit_bot` nor
`FormalSpectrum.isStalkLimit_of_isNilpotent` says anything about it. This is the check that the
target of this file is outside the regime of the two existing values, rather than a remark that it
is. -/
theorem not_isNilpotent_powerSeriesXIdeal [Nontrivial R] :
    ¬ IsNilpotent (powerSeriesXIdeal R) := fun ⟨k, hk⟩ =>
  pow_powerSeriesXIdeal_ne_bot R k hk

/-- **The sheaf-free criterion at `(X) ⊆ R⟦X⟧`, with both instance hypotheses discharged.**
`FormalSpectrum.isStalkLimit_iff_awayCompletionRestrict` carries `[TopologicalSpace R]` and
`IsAdicRing I`, neither of which occurs in its conclusion; here they are supplied inside the proof
by `Ideal.adicTopology` together with `isAdicRing_adicTopology`
(`FormalSchemes.StructureSheafStalkNilpotent`) and Mathlib's `IsAdicComplete` instance for
`(X) ⊆ R⟦X⟧`, so the statement below has neither.

**This is the first application of that criterion anywhere on the tree**, checked by searching the
tree for every occurrence of the two names rather than assumed: before this file
`FormalSpectrum.isStalkLimit_iff_awayCompletionRestrict` had no consumer at all — every other
occurrence of the name is prose — and the sheaf-carrying
`FormalSpectrum.isStalkLimit_iff_awayCompletion` was applied exactly twice, at `⊥`
(`FormalSchemes.StructureSheafStalkBot`) and at a nilpotent ideal of definition
(`FormalSchemes.StructureSheafStalkNilpotent`). So no application at a non-nilpotent ideal of
definition existed.

**Read the instantiation, not the display.** Neither side mentions a topology, and that is the
content: it is *not* being claimed for the ambient topology of `R⟦X⟧`, because there is no ambient
topology in the statement. The topology used in the proof is `Ideal.adicTopology (X)` and it is
gone from the conclusion because `FormalSpectrum.awayCompletion`,
`FormalSpectrum.awayToAtPrimeCompletion`, `FormalSpectrum.awayCompletionRestrict`,
`FormalSpectrum.basicOpen`, `FormalSpectrum.pointIdeal` and `FormalSpectrum.pointPrime` take none.

**Both sides are undecided for a general `R`.** See the module docstring. -/
theorem isStalkLimit_powerSeriesX_iff (x : FormalSpectrum (powerSeriesXIdeal R)) :
    IsStalkLimit (powerSeriesXIdeal R) x ↔
      (∀ (f : PowerSeries R) (hf : x ∈ basicOpen (powerSeriesXIdeal R) f)
          (a : awayCompletion (powerSeriesXIdeal R) f),
          awayToAtPrimeCompletion (powerSeriesXIdeal R) x (fg_powerSeriesXIdeal R) hf a = 0 →
            ∃ e, ∃ (_ : x ∈ basicOpen (powerSeriesXIdeal R) e)
              (hle : basicOpen (powerSeriesXIdeal R) e ≤ basicOpen (powerSeriesXIdeal R) f),
              awayCompletionRestrict (powerSeriesXIdeal R) f e (fg_powerSeriesXIdeal R) hle a = 0) ∧
        ∀ b : AdicCompletion (pointIdeal (powerSeriesXIdeal R) x)
            (Localization.AtPrime (pointPrime (powerSeriesXIdeal R) x)),
          ∃ f, ∃ (hf : x ∈ basicOpen (powerSeriesXIdeal R) f),
            ∃ a, awayToAtPrimeCompletion (powerSeriesXIdeal R) x (fg_powerSeriesXIdeal R) hf a =
              b := by
  letI : TopologicalSpace (PowerSeries R) := (powerSeriesXIdeal R).adicTopology
  haveI : IsAdicRing (powerSeriesXIdeal R) := isAdicRing_adicTopology (powerSeriesXIdeal R)
  exact isStalkLimit_iff_awayCompletionRestrict (powerSeriesXIdeal R) x (fg_powerSeriesXIdeal R)

end PowerSeriesX

/-! ### The value at the closed point, at `(X) ⊆ R⟦X⟧` for `R` local

`FormalSpectrum.isStalkLimit_of_pointPrime_eq_maximalIdeal` above is a criterion at the closed
point of a local ring at an arbitrary finitely generated ideal of definition, and until now it had
no consumer at `(X)`. Supplying one costs exactly the computation of
`FormalSpectrum.pointPrime` at the point, which is `FormalSpectrum.pointPrime_powerSeriesX`
followed by the description of the maximal ideal of `R⟦X⟧`.

The section is placed before the field section rather than after it because the file runs in
decreasing generality — arbitrary `R`, then local `R`, then a field — and the field value is the
special case of this one in which the space has a single point.
-/

section LocalRing

variable (R : Type u) [CommRing R]

/-- **The maximal ideal of `R⟦X⟧` for `R` local is the `PowerSeries.constantCoeff` preimage of the
maximal ideal of `R`.** Both sides are the non-units, and a power series is a unit exactly when its
constant term is (`PowerSeries.isUnit_iff_constantCoeff`).

Mathlib has `PowerSeries.maximalIdeal_eq_span_X`, but only over a **field**, where the right-hand
side collapses to `(X)`; the statement at a general local ring is absent there and absent from this
tree. It specialises correctly: over a field the maximal ideal of `R` is `⊥`, its preimage is
`RingHom.ker constantCoeff`, and that is `(X)` by
`FormalSpectrum.powerSeriesXIdeal_eq_ker`. -/
theorem maximalIdeal_powerSeries [IsLocalRing R] :
    IsLocalRing.maximalIdeal (PowerSeries R) =
      Ideal.comap (constantCoeff (R := R)) (IsLocalRing.maximalIdeal R) := by
  ext f
  rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, mem_nonunits_iff, isUnit_iff_constantCoeff]

/-- **The closed point of `Spf (R⟦X⟧, (X))` for `R` local**, as the point of the formal spectrum
lying over the closed point of `Spec R` under `FormalSpectrum.powerSeriesXHomeo`.

Named for the same reason `FormalSpectrum.powerSeriesXGenericPoint` is, and in the same shape: the
two are the points of this space at which `FormalSpectrum.IsStalkLimit` is decided, and they are
different points as soon as `R` is a local **domain** that is not a field — the generic point is
defined only at a domain, since it is the point over `⊥`. -/
def powerSeriesXClosedPoint [IsLocalRing R] : FormalSpectrum (powerSeriesXIdeal R) :=
  (powerSeriesXHomeo R).symm (IsLocalRing.closedPoint R)

/-- **The prime of `R⟦X⟧` under the closed point is the maximal ideal of `R⟦X⟧`**, which is the
hypothesis `FormalSpectrum.isStalkLimit_of_pointPrime_eq_maximalIdeal` asks for.

`FormalSpectrum.pointPrime_powerSeriesX` at this point gives the `PowerSeries.constantCoeff`
preimage of `(IsLocalRing.closedPoint R).asIdeal`, which is the maximal ideal of `R` by definition
of `IsLocalRing.closedPoint`; `FormalSpectrum.maximalIdeal_powerSeries` reads that preimage back as
the maximal ideal of `R⟦X⟧`. -/
theorem pointPrime_powerSeriesXClosedPoint [IsLocalRing R] :
    pointPrime (powerSeriesXIdeal R) (powerSeriesXClosedPoint R) =
      IsLocalRing.maximalIdeal (PowerSeries R) := by
  rw [powerSeriesXClosedPoint, pointPrime_powerSeriesX, Homeomorph.apply_symm_apply,
    maximalIdeal_powerSeries]
  rfl

/-- **`FormalSpectrum.IsStalkLimit` holds at the closed point of `Spf (R⟦X⟧, (X))`, for every local
ring `R`** — no domain, factorisation, countability or Noetherian hypothesis.

It is `FormalSpectrum.isStalkLimit_of_pointPrime_eq_maximalIdeal` at
`FormalSpectrum.pointPrime_powerSeriesXClosedPoint`, and nothing else: the criterion was written
for exactly this and the whole of the work is the computation of the prime under the point.

**This is the first value of the predicate at one point of a formal spectrum whose other points it
does not settle.** `FormalSpectrum.isStalkLimit_powerSeriesX_field` is a value at every point of a
space with one point; the generic-point cluster in
`FormalSchemes.StructureSheafStalkPowerSeriesGeneric` and
`FormalSchemes.StructureSheafStalkPowerSeriesCounterexample` is at a point that is *not* closed and
its answer depends on `R`. Here the hypothesis is on `R` alone and the answer is unconditionally
yes, so as soon as `R` is a local **domain** that is not a field — the generic point needs a
domain, being the point over `⊥`, and it is distinct from the closed point exactly when the maximal
ideal is not `⊥` — this space carries a decided closed point and a separate generic point.

**No claim that the predicate varies across this space is made here.** That would need a local ring
at whose generic point the predicate *fails*, i.e. a local domain failing the denominator condition
of `FormalSchemes.StructureSheafStalkPowerSeriesCounterexample`, and no ring named in this file is
one — a discrete valuation ring is not, since it satisfies that condition and the predicate holds at
both of its points. What is shown here is that the two points are settled by *different* arguments
under *different* hypotheses, not that they ever disagree.

**A ring at which they do disagree is exhibited downstream**, on the leaf
`FormalSchemes.StructureSheafStalkPowerSeriesLocal`: `ℤ[X]` localized at `(2, X)` is a local domain
failing the denominator condition, so this theorem and
`FormalSpectrum.isStalkLimit_powerSeriesXGenericPoint_iff_hasBoundedDenominators` settle the two
points of one space oppositely (`FormalSpectrum.exists_isStalkLimit_and_not_isStalkLimit`). That
leaf consumes this theorem exactly as it stands and adds no hypothesis to it.

**Nothing here bears on EGA I 10.8's stalk half.** The counterexample is at a non-closed point and
stands; which hypothesis repairs the general statement is still not determined anywhere. -/
theorem isStalkLimit_powerSeriesXClosedPoint [IsLocalRing R] :
    IsStalkLimit (powerSeriesXIdeal R) (powerSeriesXClosedPoint R) :=
  isStalkLimit_of_pointPrime_eq_maximalIdeal (powerSeriesXIdeal R) _
    (fg_powerSeriesXIdeal R) (pointPrime_powerSeriesXClosedPoint R)

/-- The value at a local ring that is **not** a field, so that it is not the field case of
`FormalSpectrum.isStalkLimit_powerSeriesX_field` in disguise: `k⟦X⟧` is local for `k` a field and
its space `Spec k⟦X⟧` has two points. An `example`, since it proves nothing the theorem above does
not. -/
example (k : Type u) [Field k] :
    IsStalkLimit (powerSeriesXIdeal (PowerSeries k))
      (powerSeriesXClosedPoint (PowerSeries k)) :=
  isStalkLimit_powerSeriesXClosedPoint _

end LocalRing

/-! ### The value, at `(X) ⊆ k⟦X⟧` for a field `k` -/

section Field

variable (k : Type u) [Field k]

/-- `(X) ⊆ k⟦X⟧` is a maximal ideal: it is the kernel of `PowerSeries.constantCoeff`, which is a
surjection onto a field. -/
theorem isMaximal_powerSeriesXIdeal : (powerSeriesXIdeal k).IsMaximal :=
  (powerSeriesXIdeal_eq_ker k) ▸ RingHom.ker_isMaximal_of_surjective _ constantCoeff_surj

/-- **`Spf (k⟦X⟧, (X))` has one point and its prime is `(X)`.** The prime under any point contains
the ideal of definition (`FormalSpectrum.le_pointPrime`) and is proper, and `(X)` is maximal. -/
theorem pointPrime_powerSeriesXIdeal (x : FormalSpectrum (powerSeriesXIdeal k)) :
    pointPrime (powerSeriesXIdeal k) x = powerSeriesXIdeal k := by
  have hprime : (pointPrime (powerSeriesXIdeal k) x).IsPrime := inferInstance
  exact ((isMaximal_powerSeriesXIdeal k).eq_of_le hprime.ne_top
    (le_pointPrime (powerSeriesXIdeal k) x)).symm

/-- Outside `(X)` everything is a unit of `k⟦X⟧`: a power series with nonzero constant term over a
field is invertible (`PowerSeries.isUnit_iff_constantCoeff`). -/
theorem isUnit_of_notMem_powerSeriesXIdeal {g : PowerSeries k} (hg : g ∉ powerSeriesXIdeal k) :
    IsUnit g := by
  rw [powerSeriesXIdeal_eq_ker, RingHom.mem_ker] at hg
  exact isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hg)

/-- **`FormalSpectrum.IsStalkLimit` holds at every point of `Spf (k⟦X⟧, (X))` for `k` a field** —
the first value of the predicate at an ideal of definition that is **not** nilpotent
(`FormalSpectrum.not_isNilpotent_powerSeriesXIdeal`), and so the first outside the regime of
`FormalSpectrum.isStalkLimit_bot` and `FormalSpectrum.isStalkLimit_of_isNilpotent`.

It is `FormalSpectrum.isStalkLimit_of_isUnit_notMem_pointPrime` at the unique point, whose prime is
`(X)` by `FormalSpectrum.pointPrime_powerSeriesXIdeal`.

**It is a value at a *closed* point and says nothing about a point that is not closed.** For `k` a
field there is no other kind of point. For a general `R` the space is `Spec R` and this argument
does not run at every point — but it does run at the **closed** point whenever `R` is local, which
is `FormalSpectrum.isStalkLimit_powerSeriesXClosedPoint` above, and this theorem is that statement
in the case where the space has a single point. See the module docstring for which difficulty is
faced here and which is not. -/
theorem isStalkLimit_powerSeriesX_field (x : FormalSpectrum (powerSeriesXIdeal k)) :
    IsStalkLimit (powerSeriesXIdeal k) x :=
  isStalkLimit_of_isUnit_notMem_pointPrime (powerSeriesXIdeal k) x (fg_powerSeriesXIdeal k)
    fun _ hg => isUnit_of_notMem_powerSeriesXIdeal k (by
      rwa [pointPrime_powerSeriesXIdeal k x] at hg)

/-- **The value is attained**: `Spf (k⟦X⟧, (X))` is nonempty, so
`FormalSpectrum.isStalkLimit_powerSeriesX_field` is not vacuous. Its space is `Spec k`, a single
point. -/
theorem exists_isStalkLimit_powerSeriesX_field :
    ∃ x : FormalSpectrum (powerSeriesXIdeal k), IsStalkLimit (powerSeriesXIdeal k) x :=
  ⟨(powerSeriesXHomeo k).symm ⟨⊥, inferInstance⟩, isStalkLimit_powerSeriesX_field k _⟩

end Field

end FormalSpectrum
