import FormalSchemes.StructureSheafStalkLevels
import FormalSchemes.IdealsOfDefinition
import FormalSchemes.CofinalIdeal

set_option linter.style.header false

/-!
# The point data of `Spf R` does not depend on the ideal of definition

`IsAdic.homeomorphFormalSpectrum` (`FormalSchemes.IdealsOfDefinition`) identifies the underlying
spaces of `Spf_I R` and `Spf_J R` for two ideals of definition of one topological ring, and
`FormalSpectrum.cofinalSpfIso` (`FormalSchemes.CofinalSheafComparisonIso`) upgrades that to an
isomorphism of locally ringed spaces. Neither of them says anything about the *data attached to a
point* that the stalk cluster is written in terms of. This file supplies that, in three statements
and no more:

* the prime of `R` under a point is **equal** at the two ideals, not merely corresponding;
* membership in a basic open transports along the homeomorphism;
* the two ideals of definition stay cofinal after any base change, in particular at the two
  localizations the stalk cluster localises at.

Nothing here mentions a completion, a stalk or a sheaf. It is the point-level bookkeeping that the
cofinal-invariance of `FormalSpectrum.IsStalkLimit` rests on, separated out because it is the half
with no analysis in it.

## Why the cofinality statements are at an arbitrary ring map

The two objects the stalk cluster actually compares are `FormalSpectrum.pointIdeal I x` and
`FormalSpectrum.pointIdeal J x'`, where `x'` is the transported point. Those are ideals of
`Localization.AtPrime (pointPrime I x)` and of `Localization.AtPrime (pointPrime J x')`, and
`pointPrime_homeomorphFormalSpectrum` below says the two primes are equal — but an equality of
ideals is a proposition, and it does not make the two localizations the same type. Stating the
cofinality at `pointIdeal` would therefore force a transport across a type equality into the
cheapest file in the chain.

So the cofinality is stated at an **arbitrary** ring homomorphism (`IsAdic.isCofinal_map`) and, for
the two cases the stalk cluster wants, at an **arbitrary** element and an **arbitrary** prime
(`IsAdic.isCofinal_map_away`, `IsAdic.isCofinal_map_atPrime`). At a fixed prime `p` both ideals live
in `Localization.AtPrime p` and there is nothing to transport; a consumer that needs the statement
at `pointIdeal` generalises its prime, rewrites with `pointPrime_homeomorphFormalSpectrum`, and
specialises. That is one transport at one site, rather than one here and one at each consumer.

## Main results

* `FormalSpectrum.pointPrime_homeomorphFormalSpectrum`: the prime of `R` under a point is unchanged
  by `IsAdic.homeomorphFormalSpectrum`.
* `FormalSpectrum.mem_basicOpen_iff_notMem_pointPrime`: membership in a basic open is
  non-membership in the prime under the point. Definitional, and stated because the two halves of
  it already on the tree live in two different modules.
* `FormalSpectrum.mem_basicOpen_homeomorphFormalSpectrum`: basic-open membership transports.
* `IsAdic.isCofinal_map`, `IsAdic.isCofinal_map_away`, `IsAdic.isCofinal_map_atPrime`: two ideals of
  definition of one topological ring stay cofinal after any base change.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1, §10.3.
* [The Stacks Project, Tag 0AHZ](https://stacks.math.columbia.edu/tag/0AHZ).
-/

universe u v

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] {I J : Ideal R}

/-- **The prime of `R` under a point does not depend on the ideal of definition.** The
homeomorphism `IsAdic.homeomorphFormalSpectrum` is defined so that it sends a point to the point
lying over the same prime of `R` (`IsAdic.toPrimeSpectrum_homeomorphFormalSpectrum`), and
`FormalSpectrum.pointPrime` is that prime's underlying ideal, so this is that compatibility read
through `PrimeSpectrum.asIdeal`.

It is an *equality* of ideals of `R`, not a correspondence, which is what makes the rest of this
file — and the cofinal-invariance of the stalk-limit question above it — bookkeeping rather than
transport. -/
theorem pointPrime_homeomorphFormalSpectrum (hI : IsAdic I) (hJ : IsAdic J) (x : FormalSpectrum I) :
    pointPrime J (hI.homeomorphFormalSpectrum hJ x) = pointPrime I x :=
  congrArg PrimeSpectrum.asIdeal (hI.toPrimeSpectrum_homeomorphFormalSpectrum hJ x)

omit [TopologicalSpace R] in
/-- **A point lies in `D(f)` exactly when `f` avoids the prime under it.** Both sides unfold to
`f ∉ (FormalSpectrum.toPrimeSpectrum I x).asIdeal`, so this is `Iff.rfl`.

The two directions are already on the tree, but in two different modules —
`FormalSpectrum.notMem_pointPrime_of_mem_basicOpen` in
`FormalSchemes.StructureSheafStalkComparison` and
`FormalSpectrum.mem_basicOpen_of_notMem_pointPrime` in `FormalSchemes.StructureSheafStalkBot`,
neither of which is in the other's import closure. Stating the `Iff` here costs nothing and lets
this file import neither. -/
theorem mem_basicOpen_iff_notMem_pointPrime (I : Ideal R) (x : FormalSpectrum I) (f : R) :
    x ∈ basicOpen I f ↔ f ∉ pointPrime I x :=
  Iff.rfl

/-- **Basic-open membership transports along the change of ideal of definition.** Both sides are
non-membership of `f` in the prime under the point, and
`FormalSpectrum.pointPrime_homeomorphFormalSpectrum` says that prime does not move.

Note that `f` is the *same* element of `R` on both sides: `FormalSpectrum.basicOpen` is indexed by
elements of `R` rather than by residues, so there is no comparison of residue rings here. -/
theorem mem_basicOpen_homeomorphFormalSpectrum (hI : IsAdic I) (hJ : IsAdic J)
    (x : FormalSpectrum I) (f : R) :
    hI.homeomorphFormalSpectrum hJ x ∈ basicOpen J f ↔ x ∈ basicOpen I f := by
  rw [mem_basicOpen_iff_notMem_pointPrime, mem_basicOpen_iff_notMem_pointPrime,
    pointPrime_homeomorphFormalSpectrum hI hJ x]

end FormalSpectrum

namespace IsAdic

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [TopologicalSpace R] {I J : Ideal R}

/-- **Two ideals of definition of one topological ring stay cofinal after any base change.**
`IsAdic.isCofinal` (`FormalSchemes.CofinalIdeal`) says they are cofinal in `R`, with no finite
generation anywhere, and `Ideal.IsCofinal.map` carries a cofinality along a ring homomorphism. -/
theorem isCofinal_map (hI : IsAdic I) (hJ : IsAdic J) (φ : R →+* S) :
    Ideal.IsCofinal (I.map φ) (J.map φ) :=
  (hI.isCofinal hJ).map φ

/-- **The cofinality of the two ideals of definition on a basic open**, i.e. on the localization
`Localization.Away f`, whose adic completion is `FormalSpectrum.awayCompletion I f`. This is
`IsAdic.isCofinal_map` at that localization's structural map, named because it is the instance the
sections of `O_{Spf R}` over a basic open are compared at. -/
theorem isCofinal_map_away (hI : IsAdic I) (hJ : IsAdic J) (f : R) :
    Ideal.IsCofinal (I.map (algebraMap R (Localization.Away f)))
      (J.map (algebraMap R (Localization.Away f))) :=
  hI.isCofinal_map hJ _

/-- **The cofinality of the two ideals of definition at a prime**, i.e. on the localization
`Localization.AtPrime p`, whose adic completion is the limit of the stalk tower. This is
`IsAdic.isCofinal_map` at that localization's structural map, and at
`p := FormalSpectrum.pointPrime I x` its two ideals are `FormalSpectrum.pointIdeal I x` and the
corresponding ideal for `J` — see the module docstring for why the statement is at an arbitrary
prime rather than at a point. -/
theorem isCofinal_map_atPrime (hI : IsAdic I) (hJ : IsAdic J) (p : Ideal R) [p.IsPrime] :
    Ideal.IsCofinal (I.map (algebraMap R (Localization.AtPrime p)))
      (J.map (algebraMap R (Localization.AtPrime p))) :=
  hI.isCofinal_map hJ _

end IsAdic
