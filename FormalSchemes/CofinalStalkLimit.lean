import FormalSchemes.StructureSheafStalkAlgebraic
import FormalSchemes.StructureSheafStalkCofinalTarget
import FormalSchemes.CofinalAwayToAtPrimeSquare
import FormalSchemes.CofinalAwayCompletionRestrict

set_option linter.style.header false

/-!
# `FormalSpectrum.IsStalkLimit` does not depend on the ideal of definition

`FormalSpectrum.IsStalkLimit I x` (`FormalSchemes.StructureSheafStalks`) asks whether the stalk of
`O_{Spf_I R}` at `x` is the limit of its tower of thickenings, i.e. whether the stalk half of
EGA I 10.8 holds at `x`. It is stated at a *chosen* ideal of definition `I`, while `Spf` itself does
not depend on that choice (`FormalSpectrum.generalCofinalSpfIso`,
`FormalSchemes.CofinalSheafComparisonGeneral`, EGA I §10.3).

**This file removes the choice.** For two ideals of definition `I`, `J` of one adic ring and a point
`x` of `Spf_I R`, the predicate holds at `x` exactly when it holds at the partner point
`FormalSpectrum.cofinalPoint I J x` of `Spf_J R`. So every answer to the stalk-limit question
obtained at one ideal of definition is an answer at every other one, for the same points.

## How it is proved, and why no sheaf theory appears

The route is the sheaf-free one. `FormalSpectrum.isStalkLimit_iff_awayCompletionRestrict`
(`FormalSchemes.StructureSheafStalkAlgebraic`) restates the predicate as a conjunction of two
first-order conditions on completed localizations, mentioning no stalk, germ, colimit or category:
an injectivity clause about `FormalSpectrum.awayToAtPrimeCompletion` and
`FormalSpectrum.awayCompletionRestrict`, and a surjectivity clause about the first of those. Each of
the four objects those clauses name is transported from `I` to `J`, and the two maps are carried
along by the two squares this cluster was built to supply:

* `FormalSpectrum.cofinalHom_comp_awayToAtPrimeCompletion`
  (`FormalSchemes.CofinalAwayToAtPrimeSquare`) for the comparison at a basic open;
* `FormalSpectrum.cofinalHom_comp_awayCompletionRestrict_of_isAdic`
  (`FormalSchemes.CofinalAwayCompletionRestrict`) for restriction between basic opens.

Nothing about either square is reproved here. What this file adds is the bookkeeping the two squares
deliberately left out, and it is two things.

## The one pair of exponents

`AdicCompletion.cofinalHom` (`FormalSchemes.CofinalCompletion`) is indexed by a containment
`I ^ b ≤ J`, and its level-`n` component is a formula in `b`; nothing on this tree says that two
containments at two exponents induce the same map. Both squares above are stated at
`Ideal.pow_map_le_map hb φ` (`FormalSchemes.CofinalIdeal`) for the consumer's own `hb`, so the
assembly takes **one** pair `I ^ b ≤ J`, `J ^ a ≤ I` out of `IsAdic.isCofinal`
(`FormalSchemes.CofinalIdeal`) at the top and builds every comparison map from it. Then the two
squares apply verbatim and there is nothing about exponents to reconcile.

That is why `FormalSpectrum.atPrimeCofinalRingEquiv` and
`FormalSpectrum.stalkTargetCofinalRingEquiv` (`FormalSchemes.StructureSheafStalkCofinalTarget`) do
**not** appear below: both choose their own exponents, by taking `Exists.choose_spec` of
`Ideal.IsCofinal.exists_pow_le`, so the squares are not stated at the maps they are built from.
What this file consumes out of that module is the point data —
`FormalSpectrum.cofinalPoint`, `FormalSpectrum.pointPrime_cofinalPoint`,
`FormalSpectrum.cofinalPoint_cofinalPoint` — and `FormalSpectrum.mapAtPrimeCongr`.

The invertibility the argument needs of the comparison maps is therefore not a witness-independence
statement but the plain fact that a comparison at a pair of containments is bijective:
`AdicCompletion.bijective_cofinalHom_map` below, which is `AdicCompletion.cofinalRingEquiv` read
through `AdicCompletion.cofinalRingEquiv_apply`.

## The transport along the equality of primes

`FormalSpectrum.cofinalHom_comp_awayToAtPrimeCompletion` is stated at one point and one prime, and
its own module docstring says why the two-point spelling does not typecheck and that recovering it
*"is needed exactly once, and it belongs where the two points are actually compared rather than
here."* This is that place, and `FormalSpectrum.mapAtPrimeCongr_awayToAtPrimeCompletion` is that
recovery: the comparison at `J` read at the partner point is the comparison at the second ideal read
at the original point, transported along `FormalSpectrum.pointPrime_cofinalPoint`.

It goes through `FormalSpectrum.mapAtPrimeCongr_mapCompletion_awayLift`, which has **both primes as
variables** so that `subst` fires — the point-indexed statement cannot `subst` in place, because
there neither side is a variable, which is what `FormalSpectrum.mapAtPrimeCongr`'s own docstring
records. After the substitution the two localization maps differ only in an `IsUnit` proof and the
two `AdicCompletion.mapCompletion`s only in proofs, so the identification is definitional.

## Main results

* `FormalSpectrum.mem_basicOpen_cofinalPoint`: the partner of a point lies in `D(f)` exactly when
  the point does, as the `FormalSpectrum.cofinalPoint` spelling of
  `FormalSpectrum.mem_basicOpen_homeomorphFormalSpectrum`.
* `FormalSpectrum.mapAtPrimeCongr_mapCompletion_awayLift` and
  `FormalSpectrum.mapAtPrimeCongr_awayToAtPrimeCompletion`: the transport of the comparison at a
  basic open along an equality of primes.
* `FormalSpectrum.mapAtPrimeCongr_awayToAtPrimeCompletion_cofinalHom`: the square of
  `FormalSchemes.CofinalAwayToAtPrimeSquare` in the two-point form the assembly consumes.
* `FormalSpectrum.isStalkLimit_cofinalPoint` and `FormalSpectrum.isStalkLimit_congr`: **the
  stalk-limit condition transports between any two ideals of definition**, one direction and the
  `Iff`. The `Iff` is the one direction twice, by `FormalSpectrum.cofinalPoint_cofinalPoint`.

## What is *not* proved here

Nothing is decided. `FormalSpectrum.IsStalkLimit` is undecided on this tree in both directions, and
this file moves the question between presentations rather than answering it: both sides of
`FormalSpectrum.isStalkLimit_congr` are open for a general adic ring, exactly as
`FormalSpectrum.isStalkLimit_iff_awayCompletionRestrict` is.

Nothing here is stated at `R⟦X⟧`, and the results of the `StructureSheafStalkPowerSeries*` cluster
are not transported off `FormalSpectrum.powerSeriesXIdeal` here; that corollary needs that cluster's
imports and a prose repair in `FormalSchemes.StructureSheafStalkPowerSeriesPoint`, and it is a
separate file.

Nothing here relates the two *stalks*, or the two limits of the two towers of thickenings, or the
two comparison maps `FormalSpectrum.stalkToLimit`. The transport goes through the algebraic
criterion, not through `FormalSpectrum.cofinalSpfIso`; the geometric route would need the two towers
identified and a square over a homeomorphism base, and it is not taken.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.3 and §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

universe u

namespace AdicCompletion

variable {R : Type u} [CommRing R] {S : Type u} [CommRing S] {I J : Ideal R} {a b : ℕ}

/-- **A cofinal comparison map between two extended ideals is bijective.** For containments
`I ^ b ≤ J` and `J ^ a ≤ I` in `R` and any `φ : R →+* S`, the comparison
`AdicCompletion (I · S) S →+* AdicCompletion (J · S) S` at the extended containment
`Ideal.pow_map_le_map hb φ` (`FormalSchemes.CofinalIdeal`) is bijective: it is the forward map of
`AdicCompletion.cofinalRingEquiv`, whose inverse is the comparison at
`Ideal.pow_map_le_map ha φ`.

Stated at the containments upstairs in `R` rather than at their extensions because that is the form
the squares of this cluster are indexed by, and it is what makes the *same* map both a square's edge
and an invertible one. It is not a witness-independence statement: it says nothing about two
containments at different exponents, and nothing below needs that. -/
theorem bijective_cofinalHom_map (hb : I ^ b ≤ J) (ha : J ^ a ≤ I) (φ : R →+* S) :
    Function.Bijective (cofinalHom (S := S) (Ideal.pow_map_le_map hb φ)) :=
  (cofinalRingEquiv (Ideal.pow_map_le_map hb φ) (Ideal.pow_map_le_map ha φ)).bijective

end AdicCompletion

namespace FormalSpectrum

section Transport

variable {R : Type u} [CommRing R]

/-- **Transport of `AdicCompletion.mapCompletion` along an equality of primes**, for the
localization map out of `Localization.Away f` supplied by `IsLocalization.Away.lift`. For `p = q`
the two localizations `Localization.AtPrime p` and `Localization.AtPrime q` are different terms of
the same type family, so the two completed maps out of `AdicCompletion (K · R_f) R_f` land in
different terms and have to be compared through `FormalSpectrum.mapAtPrimeCongr`.

Both primes are variables, which is the whole point: `subst` fires, after which the two `IsUnit`
witnesses are proofs of one proposition, the two `IsLocalization.Away.lift`s are definitionally
equal, and so are the two `AdicCompletion.mapCompletion`s, whose remaining arguments are proofs as
well. The statement at a pair of *points* cannot do this — see
`FormalSpectrum.mapAtPrimeCongr_awayToAtPrimeCompletion`, which is this lemma instantiated there. -/
theorem mapAtPrimeCongr_mapCompletion_awayLift {p q : Ideal R} [p.IsPrime] [q.IsPrime]
    (h : p = q) (K : Ideal R) (hK : K.FG) {f : R}
    (hp : IsUnit (algebraMap R (Localization.AtPrime p) f))
    (hq : IsUnit (algebraMap R (Localization.AtPrime q) f))
    (hmp : (K.map (algebraMap R (Localization.Away f))).map
        (IsLocalization.Away.lift (S := Localization.Away f) f hp) ≤
      K.map (algebraMap R (Localization.AtPrime p)))
    (hmq : (K.map (algebraMap R (Localization.Away f))).map
        (IsLocalization.Away.lift (S := Localization.Away f) f hq) ≤
      K.map (algebraMap R (Localization.AtPrime q)))
    (α : AdicCompletion (K.map (algebraMap R (Localization.Away f))) (Localization.Away f)) :
    mapAtPrimeCongr h K
        (AdicCompletion.mapCompletion (IsLocalization.Away.lift f hp) hmp (hK.map _) α) =
      AdicCompletion.mapCompletion (IsLocalization.Away.lift f hq) hmq (hK.map _) α := by
  subst h
  rfl

end Transport

section

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I J : Ideal R)
  [IsAdicRing I] [IsAdicRing J]

/-- **The partner of a point lies in `D(f)` exactly when the point does.** This is
`FormalSpectrum.mem_basicOpen_homeomorphFormalSpectrum`
(`FormalSchemes.CofinalFormalSpectrumPoint`) in the `FormalSpectrum.cofinalPoint` spelling, which is
the one every statement below is written in; `FormalSpectrum.cofinalPoint` is by definition that
homeomorphism applied to the point. Note that `f` is the same element of `R` on both sides. -/
theorem mem_basicOpen_cofinalPoint (x : FormalSpectrum I) (f : R) :
    cofinalPoint I J x ∈ basicOpen J f ↔ x ∈ basicOpen I f :=
  mem_basicOpen_homeomorphFormalSpectrum (IsAdicRing.isAdic (I := I))
    (IsAdicRing.isAdic (I := J)) x f

/-- **The comparison at a basic open, read at the partner point, is the comparison at the second
ideal read at the original point.** `FormalSpectrum.awayToAtPrimeCompletion J (cofinalPoint I J x)`
lands in the completion of `Localization.AtPrime (pointPrime J (cofinalPoint I J x))` and
`FormalSpectrum.awayToAtPrimeCompletionOfIdeal I x J` in the completion of
`Localization.AtPrime (pointPrime I x)`; the two primes are equal
(`FormalSpectrum.pointPrime_cofinalPoint`) and `FormalSpectrum.mapAtPrimeCongr` carries one to the
other.

This is the two-point spelling that `FormalSchemes.CofinalAwayToAtPrimeSquare` declines to state and
defers to the file where the two points are compared. It is
`FormalSpectrum.mapAtPrimeCongr_mapCompletion_awayLift` at `p := pointPrime J (cofinalPoint I J x)`
and `q := pointPrime I x`: both comparisons are `AdicCompletion.mapCompletion` of an
`IsLocalization.Away.lift`, which is what `FormalSpectrum.awayToAtPrime` is defined to be, and
neither depends on the ideal of definition except through that prime. -/
theorem mapAtPrimeCongr_awayToAtPrimeCompletion (hJ : J.FG) (x : FormalSpectrum I) {f : R}
    (hf : x ∈ basicOpen I f) (hf' : cofinalPoint I J x ∈ basicOpen J f) (α : awayCompletion J f) :
    mapAtPrimeCongr (pointPrime_cofinalPoint I J x) J
        (awayToAtPrimeCompletion J (cofinalPoint I J x) hJ hf' α) =
      awayToAtPrimeCompletionOfIdeal I x J hJ hf α :=
  mapAtPrimeCongr_mapCompletion_awayLift _ J hJ _ _ _ _ α

/-- **The stalk comparison at a basic open commutes with a change of ideal of definition, at two
points.** `FormalSpectrum.cofinalHom_comp_awayToAtPrimeCompletion`
(`FormalSchemes.CofinalAwayToAtPrimeSquare`) with its lower-right corner transported to the partner
point by `FormalSpectrum.mapAtPrimeCongr_awayToAtPrimeCompletion`.

This is the form the two clauses of `FormalSpectrum.isStalkLimit_iff_awayCompletionRestrict`
consume: on the left the comparison at `J` at the partner point, which is what the criterion at `J`
names, and on the right the comparison at `I` at `x`, which is what the criterion at `I` names, with
one containment `I ^ b ≤ J` in `R` serving both comparison maps. -/
theorem mapAtPrimeCongr_awayToAtPrimeCompletion_cofinalHom (hI : I.FG) (hJ : J.FG) {b : ℕ}
    (hb : I ^ b ≤ J) (x : FormalSpectrum I) {f : R} (hf : x ∈ basicOpen I f)
    (hf' : cofinalPoint I J x ∈ basicOpen J f) (α : awayCompletion I f) :
    mapAtPrimeCongr (pointPrime_cofinalPoint I J x) J
        (awayToAtPrimeCompletion J (cofinalPoint I J x) hJ hf'
          (AdicCompletion.cofinalHom
            (Ideal.pow_map_le_map hb (algebraMap R (Localization.Away f))) α)) =
      AdicCompletion.cofinalHom
          (Ideal.pow_map_le_map hb (algebraMap R (Localization.AtPrime (pointPrime I x))))
        (awayToAtPrimeCompletion I x hI hf α) := by
  rw [mapAtPrimeCongr_awayToAtPrimeCompletion I J hJ x hf hf']
  exact RingHom.congr_fun (cofinalHom_comp_awayToAtPrimeCompletion I x hI hJ hb hf) α

/-- **The stalk-limit condition passes to another ideal of definition.** If the stalk of
`O_{Spf_I R}` at `x` is the limit of its tower of thickenings, then so is the stalk of
`O_{Spf_J R}` at the partner point `FormalSpectrum.cofinalPoint I J x`.

Both sides are read through `FormalSpectrum.isStalkLimit_iff_awayCompletionRestrict`, so no sheaf
theory is involved. One pair of exponents is taken from `IsAdic.isCofinal` at the top and every
comparison map below is built from it; the two squares of this cluster then apply verbatim, and
`AdicCompletion.bijective_cofinalHom_map` supplies the element of `R{1/f}` at `I` behind a given one
at `J` in the injectivity clause, and the element of the completion at the prime behind a given one
in the surjectivity clause.

The `Iff` is `FormalSpectrum.isStalkLimit_congr`; it does not need a second proof. -/
theorem isStalkLimit_cofinalPoint (hI : I.FG) (hJ : J.FG) (x : FormalSpectrum I)
    (h : IsStalkLimit I x) : IsStalkLimit J (cofinalPoint I J x) := by
  obtain ⟨hinj, hsurj⟩ := (isStalkLimit_iff_awayCompletionRestrict I x hI).1 h
  have hIa : IsAdic I := IsAdicRing.isAdic
  have hJa : IsAdic J := IsAdicRing.isAdic
  obtain ⟨b, hb⟩ := (hIa.isCofinal hJa).exists_pow_le
  obtain ⟨a, ha⟩ := (hIa.isCofinal hJa).exists_pow_le'
  refine (isStalkLimit_iff_awayCompletionRestrict J (cofinalPoint I J x) hJ).2 ⟨?_, ?_⟩
  · intro f hf' α' hα'
    have hf : x ∈ basicOpen I f := (mem_basicOpen_cofinalPoint I J x f).1 hf'
    obtain ⟨α, hα⟩ :=
      (AdicCompletion.bijective_cofinalHom_map hb ha (algebraMap R (Localization.Away f))).2 α'
    have hsq := mapAtPrimeCongr_awayToAtPrimeCompletion_cofinalHom I J hI hJ hb x hf hf' α
    rw [hα] at hsq
    have hz : awayToAtPrimeCompletion I x hI hf α = 0 :=
      (AdicCompletion.bijective_cofinalHom_map hb ha
          (algebraMap R (Localization.AtPrime (pointPrime I x)))).1
        ((hsq.symm.trans ((mapAtPrimeCongr (pointPrime_cofinalPoint I J x) J).map_eq_zero_iff.2
          hα')).trans (map_zero _).symm)
    obtain ⟨e, hxe, hle, hres⟩ := hinj f hf α hz
    refine ⟨e, (mem_basicOpen_cofinalPoint I J x e).2 hxe,
      (basicOpen_le_congr_of_isAdic hIa hJa f e).1 hle, ?_⟩
    have hsq2 := RingHom.congr_fun
      (cofinalHom_comp_awayCompletionRestrict_of_isAdic (f := f) (g := e) hIa hJa hI hJ hb hle) α
    simp only [RingHom.comp_apply] at hsq2
    rwa [hα, hres, map_zero] at hsq2
  · intro β'
    obtain ⟨β, hβ⟩ :=
      (AdicCompletion.bijective_cofinalHom_map hb ha
          (algebraMap R (Localization.AtPrime (pointPrime I x)))).2
        (mapAtPrimeCongr (pointPrime_cofinalPoint I J x) J β')
    obtain ⟨f, hf, α, hα⟩ := hsurj β
    refine ⟨f, (mem_basicOpen_cofinalPoint I J x f).2 hf,
      AdicCompletion.cofinalHom
        (Ideal.pow_map_le_map hb (algebraMap R (Localization.Away f))) α, ?_⟩
    refine (mapAtPrimeCongr (pointPrime_cofinalPoint I J x) J).injective ?_
    rw [mapAtPrimeCongr_awayToAtPrimeCompletion_cofinalHom I J hI hJ hb x hf _ α, hα]
    exact hβ

/-- **`FormalSpectrum.IsStalkLimit` does not depend on the ideal of definition.** The stalk half of
EGA I 10.8 holds at a point of `Spf_I R` exactly when it holds at the corresponding point of
`Spf_J R`, for any two ideals of definition `I`, `J` of one adic ring.

The two directions are `FormalSpectrum.isStalkLimit_cofinalPoint` with the ideals exchanged:
`FormalSpectrum.cofinalPoint_cofinalPoint` says the partner of the partner is the point again, so
the second direction needs no separate proof. -/
theorem isStalkLimit_congr (hI : I.FG) (hJ : J.FG) (x : FormalSpectrum I) :
    IsStalkLimit I x ↔ IsStalkLimit J (cofinalPoint I J x) :=
  ⟨isStalkLimit_cofinalPoint I J hI hJ x, fun h => by
    have hx := isStalkLimit_cofinalPoint J I hJ hI (cofinalPoint I J x) h
    rwa [cofinalPoint_cofinalPoint] at hx⟩

end

end FormalSpectrum

end
