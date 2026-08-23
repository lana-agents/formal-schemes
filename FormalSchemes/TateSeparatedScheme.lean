import FormalSchemes.GeneralSeparatedScheme
import FormalSchemes.TateSeparatedTopFiniteType
import FormalSchemes.TateSeparatedValue

set_option linter.style.header false

/-!
# `𝔈_q` is a separated formal scheme over `Spf R` — with no chart data in the statement

`FormalSchemes.GeneralSeparatedScheme` (issue 842) introduced
`FormalScheme.IsSeparatedOverSpf X s`, separatedness as a property of a formal scheme and its
structural morphism rather than of a presentation, and deliberately contained **no value**: as it
landed, the predicate had no inhabitants at all. This file supplies the first one about a *named
geometric object*.

> **The Tate curve formal model `𝔈_q` is separated over `Spf R`**, unconditionally, and the
> statement mentions no chart, no datum and no cocycle.

## Why this is cheap, and what it is not blocked on

The affine value `Spf A` — the one a reader would expect first — is blocked on a structural
compatibility for the one-chart gluing isomorphism `oneChartXGluedIso`
(`FormalSchemes.AffineSeparatedIso`) that does not exist on master; `GeneralSeparatedScheme`'s
module docstring names it, and it is tracked separately.

The Tate analogue of exactly that missing lemma **does** exist:
`tateXGluedHom_comp_tateCurveModelStructMap` (`FormalSchemes.TateSeparatedTopFiniteType`, issue
813) says 704's comparison isomorphism between the datum's glued object and `𝔈_q` is a morphism
over `Spf R`. So the Tate value, which reads like the harder one, is the one that is available,
and it is packaging over three facts already on master:

* `tate_isSeparated` (`FormalSchemes.TateSeparatedValue`, issues 706/798) — the presentation-level
  value, unconditional;
* `FormalScheme.isSeparatedOverSpf_of_isSeparated` — a presentation-level value enters the
  scheme-level vocabulary at its own glued object;
* `FormalScheme.isSeparatedOverSpf_of_iso` together with 813's compatibility — transport across
  704's isomorphism, from that glued object to `𝔈_q` itself.

## The choice of `B`

`AffineChartedFibreDatumX R I hI B` carries the `Y`-side algebra `B` of the fibre-product datum it
extends, and `tateCurveExposeXDatum` is defined for every `B`; nothing in the Tate charts, their
overlaps or their cocycle mentions it. `IsSeparatedOverSpf` quantifies existentially over the whole
presentation, so `tateCurveModel_isSeparatedOverSpf` is `B`-free and the proof merely has to *pick*
one. It picks `B := R`. That is a choice of witness, not a restriction: the same statement follows
from the datum at any `B`, and `tateCurveExposeX_isSeparatedOverSpf` below is stated at an arbitrary
one.

## Both EGA properties of `𝔈_q`, now about `𝔈_q`

`FormalSchemes.TateSeparatedTopFiniteType` paired separatedness with finite type by transporting
the finite-type half *down* to the datum's glued object, because the separatedness half was only
available there. With this file the pairing can be stated the other way round, at the model itself:
`tateCurveModel_isRelativelyTopFiniteType` (`FormalSchemes.TateTopFiniteType`, issue 806) and
`tateCurveModel_isSeparatedOverSpf` are two properties of the single term
`tateCurveModel R I q hq hI`, and neither statement mentions a chart. Following the convention of
`TateTopFiniteType` and `TateSeparatedTopFiniteType`, the finite-type half is cited by name rather
than imported, so that this module stays a leaf.

## Main results

* `AlgebraicGeometry.tateCurveExposeX_isSeparatedOverSpf`: the Tate datum's glued object is
  separated over `Spf R`, along the datum's own structural morphism.
* `AlgebraicGeometry.tateCurveModel_isSeparatedOverSpf`: **`𝔈_q` is separated over `Spf R`**, along
  `tateCurveModelStructMap`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
-/

noncomputable section

open CategoryTheory FormalSpectrum

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R]

/-- **The glued object of the Tate `X`-expose datum is separated over `Spf R`** (EGA I §10.15), in
the scheme-level vocabulary of `FormalSchemes.GeneralSeparatedScheme`.

This is `tate_isSeparated` entering that vocabulary through
`FormalScheme.isSeparatedOverSpf_of_isSeparated`, which witnesses the existential with the datum
itself and the identity isomorphism. It is the direct counterpart of
`tateCurveExposeX_isRelativelyTopFiniteType`, and holds for every `B`. -/
theorem tateCurveExposeX_isSeparatedOverSpf (B : Type u) [CommRing B] [Algebra R B]
    (hq : q ∈ I) (hI : I.FG) :
    FormalScheme.IsSeparatedOverSpf hI (tateCurveExposeXDatum R I q B hq hI).xGlued
      (tateCurveExposeXDatum R I q B hq hI).xStructMap :=
  FormalScheme.isSeparatedOverSpf_of_isSeparated hI _ _ _ _ (tate_isSeparated R I q B hq hI)

/-- **The Tate curve formal model `𝔈_q` is a separated formal scheme over `Spf R`**
(EGA I §10.15), with no hypotheses beyond `hq : q ∈ I`, `hI : I.FG` and the ambient instances —
and, unlike `tate_isSeparated`, with no chart, datum or cocycle anywhere in the statement.

The proof transports `tateCurveExposeX_isSeparatedOverSpf` across 704's comparison isomorphism
`tateXGluedIsoLRS` using `FormalScheme.isSeparatedOverSpf_of_iso`, whose compatibility over the
base is 813's `tateXGluedHom_comp_tateCurveModelStructMap`. The witnessing presentation is the Tate
datum at `B := R`; see the module docstring on why that choice is free.

Together with `tateCurveModel_isRelativelyTopFiniteType` (`FormalSchemes.TateTopFiniteType`), this
says: **`𝔈_q` is a separated formal scheme, topologically of finite type over `Spf R`** — both
properties of one term, both stated without charts. -/
theorem tateCurveModel_isSeparatedOverSpf (hq : q ∈ I) (hI : I.FG) :
    FormalScheme.IsSeparatedOverSpf hI (tateCurveModel R I q hq hI)
      (tateCurveModelStructMap R I q hq hI) :=
  FormalScheme.isSeparatedOverSpf_of_iso hI (tateXGluedIsoLRS R I q R hq hI)
    (tateXGluedHom_comp_tateCurveModelStructMap R I q R hq hI)
    (tateCurveExposeX_isSeparatedOverSpf R I q R hq hI)

end AlgebraicGeometry

end
