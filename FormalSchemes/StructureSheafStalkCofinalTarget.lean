import FormalSchemes.CofinalFormalSpectrumPoint
import FormalSchemes.CofinalCompletion

set_option linter.style.header false

/-!
# The target of the stalk comparison does not depend on the ideal of definition

`FormalSpectrum.stalkToAdicCompletion I x` (`FormalSchemes.StructureSheafStalkLevels`) compares the
stalk of `O_{Spf_I R}` at `x` with `AdicCompletion (I · R_p) R_p`, for `p` the prime of `R` under
`x`, and `FormalSpectrum.IsStalkLimit` (`FormalSchemes.StructureSheafStalks`) asks whether it is an
isomorphism. Both the question and the answer are stated at a *chosen* ideal of definition, while
`Spf` itself is known not to depend on that choice — `FormalSpectrum.generalCofinalSpfIso`
(`FormalSchemes.CofinalSheafComparisonGeneral`), EGA I §10.3.

**This file settles the target side of that discrepancy.** For two ideals of definition `I`, `J` of
one adic ring and a point `x` of `Spf_I R`, the two completions the two comparisons land in are
canonically isomorphic, and the isomorphism fixes the image of `R`. Nothing here is about the stalk,
and nothing here decides `FormalSpectrum.IsStalkLimit`; what it says is that the *object* the
predicate compares the stalk against is independent of the presentation.

## Route

Two ideals of definition of one topological ring are cofinal (`IsAdic.isCofinal`,
`FormalSchemes.CofinalIdeal`), cofinality survives extension along a ring homomorphism
(`Ideal.IsCofinal.map`), and cofinal ideals have isomorphic adic completions
(`AdicCompletion.cofinalRingEquiv`, `FormalSchemes.CofinalCompletion`). The first two steps are
already composed at a localization by `IsAdic.isCofinal_map_atPrime`
(`FormalSchemes.CofinalFormalSpectrumPoint`), so this file takes only the third. The same three
steps are taken at `Localization.Away g` in
`FormalSpectrum.isIso_mapSheafHomId_app_basicOpen` (`FormalSchemes.CofinalSheafComparisonIso`),
which is the sheaf-level analogue of this file.

The one piece of bookkeeping is that the two points are different terms: `x` lives in
`FormalSpectrum I` and its partner `FormalSpectrum.cofinalPoint I J x` in `FormalSpectrum J`, so
their `FormalSpectrum.pointPrime`s are equal but not syntactically so, and the two localizations are
therefore different terms of the same type family. `FormalSpectrum.mapAtPrimeCongr` transports along
that equality; it is stated with both primes as variables because `subst` is what proves it.

## Main definitions and results

* `FormalSpectrum.cofinalPoint`: the point of `Spf_J R` over the same prime of `R` as a given point
  of `Spf_I R`, with `FormalSpectrum.pointPrime_cofinalPoint` and
  `FormalSpectrum.cofinalPoint_cofinalPoint`.
* `FormalSpectrum.atPrimeCofinalRingEquiv`: the two adic completions of `Localization.AtPrime p`
  are isomorphic, for every prime `p` of `R`, and `FormalSpectrum.atPrimeCofinalRingEquiv_of`: the
  isomorphism fixes the image of that local ring.
* `FormalSpectrum.stalkTargetCofinalRingEquiv`: **the two targets of the stalk comparison at a point
  and at its partner are isomorphic**, and `FormalSpectrum.stalkTargetCofinalRingEquiv_of`: the
  isomorphism fixes the image of `R`.

## What is *not* proved here

Nothing about `FormalSpectrum.stalkToLimit`, `FormalSpectrum.stalkToAdicCompletion` or
`FormalSpectrum.IsStalkLimit`. That the comparison maps *intertwine*
`FormalSpectrum.stalkTargetCofinalRingEquiv` with the isomorphism of the two stalks — and hence that
`FormalSpectrum.IsStalkLimit` is invariant under passing to another ideal of definition — is a
separate question, and the isomorphism of the two stalks is not constructed here either. This file
supplies one edge of that square and makes no claim about the other three.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.3 and §10.8.
-/

noncomputable section

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I J : Ideal R)
  [IsAdicRing I] [IsAdicRing J]

/-! ### The partner of a point -/

/-- **The point of `Spf_J R` over the same prime of `R`** as `x ∈ Spf_I R`. The underlying space of
`Spf R` does not depend on the ideal of definition, and `IsAdic.homeomorphFormalSpectrum`
(`FormalSchemes.IdealsOfDefinition`) is the identification; this is that homeomorphism, named so
that the statements below read as statements about a point rather than about a homeomorphism. -/
def cofinalPoint (x : FormalSpectrum I) : FormalSpectrum J :=
  (IsAdicRing.isAdic (I := I)).homeomorphFormalSpectrum (IsAdicRing.isAdic (I := J)) x

/-- **The partner of a point lies over the same prime of `R`.** This is what puts the two stalk
comparisons over one local ring, and it is the only reason the completions below are comparable at
all. It is `FormalSpectrum.pointPrime_homeomorphFormalSpectrum`
(`FormalSchemes.CofinalFormalSpectrumPoint`) read at the homeomorphism
`FormalSpectrum.cofinalPoint` is defined from. -/
theorem pointPrime_cofinalPoint (x : FormalSpectrum I) :
    pointPrime J (cofinalPoint I J x) = pointPrime I x :=
  FormalSpectrum.pointPrime_homeomorphFormalSpectrum
    (IsAdicRing.isAdic (I := I)) (IsAdicRing.isAdic (I := J)) x

/-- Taking the partner twice returns the point: both round trips read the same prime of `R`, and a
point of `Spf_I R` is determined by it (`FormalSpectrum.isClosedEmbedding_toPrimeSpectrum`). -/
theorem cofinalPoint_cofinalPoint (x : FormalSpectrum I) :
    cofinalPoint J I (cofinalPoint I J x) = x := by
  apply (isClosedEmbedding_toPrimeSpectrum I).injective
  rw [cofinalPoint, cofinalPoint, IsAdic.toPrimeSpectrum_homeomorphFormalSpectrum,
    IsAdic.toPrimeSpectrum_homeomorphFormalSpectrum]

/-! ### The two completions of one local ring -/

/-- **The two adic completions of `Localization.AtPrime p` agree.**
`AdicCompletion.cofinalRingEquiv` (`FormalSchemes.CofinalCompletion`) applied to
`IsAdic.isCofinal_map_atPrime` (`FormalSchemes.CofinalFormalSpectrumPoint`).

The two exponents are *chosen* from the cofinality rather than passed in:
`AdicCompletion.cofinalRingEquiv` takes them explicitly, and `Ideal.IsCofinal` only asserts that
they exist. Nothing below depends on which witnesses are chosen, because
`FormalSpectrum.atPrimeCofinalRingEquiv_of` pins the map on the image of
`Localization.AtPrime p`, and `AdicCompletion.cofinalHom` is determined there.

The cofinality itself is `IsAdic.isCofinal_map_atPrime`
(`FormalSchemes.CofinalFormalSpectrumPoint`), taken once in each direction. It is stated there at
`IsAdic` rather than at `IsAdicRing`, so it is applied to `IsAdicRing.isAdic` and not by dot
notation: `IsAdic` unfolds to an equation between topologies, and a projection off
`IsAdicRing.isAdic` would be sought on `Eq`. -/
def atPrimeCofinalRingEquiv (p : Ideal R) [p.IsPrime] :
    AdicCompletion (I.map (algebraMap R (Localization.AtPrime p))) (Localization.AtPrime p) ≃+*
      AdicCompletion (J.map (algebraMap R (Localization.AtPrime p))) (Localization.AtPrime p) :=
  AdicCompletion.cofinalRingEquiv
    (IsAdic.isCofinal_map_atPrime (IsAdicRing.isAdic (I := I)) (IsAdicRing.isAdic (I := J))
      p).exists_pow_le.choose_spec
    (IsAdic.isCofinal_map_atPrime (IsAdicRing.isAdic (I := J)) (IsAdicRing.isAdic (I := I))
      p).exists_pow_le.choose_spec

/-- **The comparison of the two completions fixes the image of the local ring**: it is
`AdicCompletion.of` on both sides. This is `AdicCompletion.cofinalHom_of` read through
`AdicCompletion.cofinalRingEquiv_apply`. -/
theorem atPrimeCofinalRingEquiv_of (p : Ideal R) [p.IsPrime] (a : Localization.AtPrime p) :
    atPrimeCofinalRingEquiv I J p (AdicCompletion.of _ _ a) = AdicCompletion.of _ _ a := by
  rw [atPrimeCofinalRingEquiv, AdicCompletion.cofinalRingEquiv_apply, AdicCompletion.cofinalHom_of]

/-! ### Transport along an equality of primes -/

section Congr

omit [TopologicalSpace R] [IsAdicRing I] [IsAdicRing J]

/-- **Transport of the adic completion of a localization along an equality of primes.** For `p = q`
the two localizations are different terms of the same type family, so an extension `K · R_p` and the
extension `K · R_q` of the same ideal of `R` are not syntactically the same ideal; this carries the
completion from one to the other.

Both primes are variables, which is what lets `subst` prove it — the point-indexed application in
`FormalSpectrum.stalkTargetCofinalRingEquiv` cannot `subst` in place, because there neither side is
a variable. -/
def mapAtPrimeCongr {p q : Ideal R} [p.IsPrime] [q.IsPrime] (h : p = q) (K : Ideal R) :
    AdicCompletion (K.map (algebraMap R (Localization.AtPrime p))) (Localization.AtPrime p) ≃+*
      AdicCompletion (K.map (algebraMap R (Localization.AtPrime q))) (Localization.AtPrime q) := by
  subst h; exact RingEquiv.refl _

/-- `FormalSpectrum.mapAtPrimeCongr` fixes the image of `R`. -/
theorem mapAtPrimeCongr_of {p q : Ideal R} [p.IsPrime] [q.IsPrime] (h : p = q) (K : Ideal R)
    (r : R) :
    mapAtPrimeCongr h K (AdicCompletion.of _ _ (algebraMap R (Localization.AtPrime p) r)) =
      AdicCompletion.of _ _ (algebraMap R (Localization.AtPrime q) r) := by
  subst h; rfl

end Congr

/-! ### The two targets of the stalk comparison -/

/-- **The target of the stalk comparison does not depend on the ideal of definition.** For a point
`x` of `Spf_I R` and its partner `FormalSpectrum.cofinalPoint I J x` in `Spf_J R`, the completion
`FormalSpectrum.stalkToAdicCompletion I x` lands in is canonically isomorphic to the one
`stalkToAdicCompletion J (cofinalPoint I J x)` lands in.

Both are completions of the *same* local ring `Localization.AtPrime (pointPrime I x)` — that is
`FormalSpectrum.pointPrime_cofinalPoint` — at the two extensions `I · R_p` and `J · R_p`, which are
cofinal. This says nothing about the two comparison maps; see the module docstring. -/
def stalkTargetCofinalRingEquiv (x : FormalSpectrum I) :
    AdicCompletion (pointIdeal I x) (Localization.AtPrime (pointPrime I x)) ≃+*
      AdicCompletion (pointIdeal J (cofinalPoint I J x))
        (Localization.AtPrime (pointPrime J (cofinalPoint I J x))) :=
  (atPrimeCofinalRingEquiv I J (pointPrime I x)).trans
    (mapAtPrimeCongr (pointPrime_cofinalPoint I J x).symm J)

/-- **The comparison of the two targets fixes the image of `R`.** This is what makes
`FormalSpectrum.stalkTargetCofinalRingEquiv` usable: the two completions are identified compatibly
with the structure maps out of `R`, not merely abstractly isomorphic.

The `change` is not decoration. `FormalSpectrum.pointIdeal I x` is *by definition*
`I.map (algebraMap R (Localization.AtPrime (pointPrime I x)))`, and while `RingEquiv.trans` accepts
the composite above, `RingEquiv.trans_apply` will not rewrite through the two spellings: the
unifier does not identify them at `instances` transparency. Spelling the application in the
`Ideal.map` form first is what lets the two `_of` lemmas fire. -/
theorem stalkTargetCofinalRingEquiv_of (x : FormalSpectrum I) (r : R) :
    stalkTargetCofinalRingEquiv I J x
        (AdicCompletion.of _ _ (algebraMap R (Localization.AtPrime (pointPrime I x)) r)) =
      AdicCompletion.of _ _
        (algebraMap R (Localization.AtPrime (pointPrime J (cofinalPoint I J x))) r) := by
  change mapAtPrimeCongr (pointPrime_cofinalPoint I J x).symm J
      (atPrimeCofinalRingEquiv I J (pointPrime I x)
        (AdicCompletion.of (I.map (algebraMap R (Localization.AtPrime (pointPrime I x))))
          (Localization.AtPrime (pointPrime I x))
          (algebraMap R (Localization.AtPrime (pointPrime I x)) r))) = _
  rw [atPrimeCofinalRingEquiv_of, mapAtPrimeCongr_of]
  rfl

end FormalSpectrum

end
