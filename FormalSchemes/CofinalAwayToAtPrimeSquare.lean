import FormalSchemes.StructureSheafStalkComparison
import FormalSchemes.CofinalCompletionFunctorial
import FormalSchemes.CofinalIdeal

set_option linter.style.header false

/-!
# The stalk comparison at a basic open commutes with a change of ideal of definition

`FormalSpectrum.awayToAtPrimeCompletion` (`FormalSchemes.StructureSheafStalkComparison`) is the
comparison the stalk cluster is built on: for a point `x` of `Spf_I R` lying in a basic open
`D(f)`, it carries the completed localization `FormalSpectrum.awayCompletion I f` into the adic
completion of `Localization.AtPrime (FormalSpectrum.pointPrime I x)` at
`FormalSpectrum.pointIdeal I x`. It is stated at a *chosen* ideal of definition `I`, while `Spf`
itself is known not to depend on that choice (`FormalSpectrum.generalCofinalSpfIso`,
`FormalSchemes.CofinalSheafComparisonGeneral`, EGA I §10.3).

**This file proves the square that begins to close that gap**: the comparison commutes with the
cofinal comparison maps `AdicCompletion.cofinalHom` (`FormalSchemes.CofinalCompletion`) that pass
from `I` to another ideal `J` with `I ^ b ≤ J`.

```
AdicCompletion (I · R_f) R_f  --cofinalHom-->  AdicCompletion (J · R_f) R_f
            |                                              |
   mapCompletion φ                                mapCompletion φ
            v                                              v
AdicCompletion (I · R_p) R_p  --cofinalHom-->  AdicCompletion (J · R_p) R_p
```

with `φ = FormalSpectrum.awayToAtPrime I x hf` the localization map. In the diagram the top row
is read in `Localization.Away f` and the bottom row in
`Localization.AtPrime (FormalSpectrum.pointPrime I x)`, `I · R_f` abbreviates
`I.map (algebraMap R (Localization.Away f))`, and `I · R_p` is `FormalSpectrum.pointIdeal I x`.
The left edge is
`FormalSpectrum.awayToAtPrimeCompletion` itself; the right edge is the same map read at `J`, which
is what `FormalSpectrum.awayToAtPrimeCompletionOfIdeal` below is for.

## Why the square is stated at one prime rather than at two points

The shape a reader expects is the one relating `awayToAtPrimeCompletion I x` to
`awayToAtPrimeCompletion J x'`, where `x'` is the partner of `x` in `Spf_J R` under
`IsAdic.homeomorphFormalSpectrum` (`FormalSchemes.IdealsOfDefinition`). **That statement does not
typecheck.** `AdicCompletion.cofinalHom` compares two ideals of *one* ring, and the two comparisons
land in `Localization.AtPrime (FormalSpectrum.pointPrime I x)` and in
`Localization.AtPrime (FormalSpectrum.pointPrime J x')`. Those primes are equal — that is
`FormalSpectrum.pointPrime_homeomorphFormalSpectrum` (`FormalSchemes.CofinalFormalSpectrumPoint`) —
but an equality of ideals is a proposition and does not make the two localizations one type.

So the square is stated with **one point and one prime**, and with the two ideals of definition
appearing only as ideals of `R`. Nothing is lost: the map `φ` above does not depend on the ideal of
definition at all, only on `x` and on `f`, and the whole content of the square is that completing
along `φ` commutes with changing the ideal. Recovering the two-point spelling is a transport along
the equality of primes, it is needed exactly once, and it belongs where the two points are actually
compared rather than here.

## Why the hypothesis is `I ^ b ≤ J` and not `Ideal.IsCofinal I J`

`AdicCompletion.mapCompletion_comp_cofinalHom` (`FormalSchemes.CofinalCompletionFunctorial`) needs
**one** exponent `b` serving both rows of the square: `(I · R_f) ^ b ≤ J · R_f` *and*
`(I · R_p) ^ b ≤ J · R_p`. A containment `I ^ b ≤ J` in `R` maps forward to both, with the same `b`
(`Ideal.pow_map_le_map`, `FormalSchemes.CofinalIdeal`), so there is nothing to reconcile.

A packaged `Ideal.IsCofinal (I · R_f) (J · R_f)` would *lose* that. `Ideal.IsCofinal`
(`FormalSchemes.CofinalIdeal`) only asserts that an exponent exists, so the two rows would be
built from two independently chosen witnesses and would have to be reconciled by
`Ideal.pow_le_pow_right` at their maximum. Taking the containment upstairs in `R` avoids the
question rather than answering it, which is why the hypothesis is where it is. For two ideals of
definition of one topological ring the containment is supplied by `IsAdic.isCofinal`
(`FormalSchemes.CofinalIdeal`), whose `Ideal.IsCofinal.exists_pow_le` gives the `b`.

## Main definitions and results

* `FormalSpectrum.map_map_awayToAtPrime`: the localization map at a point of a basic open carries
  the extension of **any** ideal of `R` onto its extension at the prime, generalising
  `FormalSpectrum.map_awayToAtPrime` from the ideal of definition to an arbitrary ideal.
* `FormalSpectrum.awayToAtPrimeCompletionOfIdeal`: `FormalSpectrum.awayToAtPrimeCompletion` at an
  arbitrary ideal of `R` in place of the ideal of definition, with
  `FormalSpectrum.awayToAtPrimeCompletionOfIdeal_self` identifying the two.
* `FormalSpectrum.cofinalHom_comp_awayToAtPrimeCompletion`: **the square.**

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.3 and §10.8.
-/

noncomputable section

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R) (x : FormalSpectrum I)

/-- **`FormalSpectrum.awayToAtPrime` carries the extension of any ideal onto its extension.** Both
sides are the extension of `K` along a map under `R`, so `Ideal.map_map` and
`FormalSpectrum.awayToAtPrime_algebraMap` identify them outright.

This is `FormalSpectrum.map_awayToAtPrime` with the ideal of definition replaced by an arbitrary
ideal `K` — at `K = I` the right-hand side is `FormalSpectrum.pointIdeal I x` by definition, so
that lemma is this one's diagonal. The general form is what the square needs, because the square's
lower edge is the same localization map read at a second ideal. -/
theorem map_map_awayToAtPrime (K : Ideal R) {f : R} (hf : x ∈ basicOpen I f) :
    (K.map (algebraMap R (Localization.Away f))).map (awayToAtPrime I x hf) =
      K.map (algebraMap R (Localization.AtPrime (pointPrime I x))) := by
  rw [Ideal.map_map]
  congr 1
  exact RingHom.ext (awayToAtPrime_algebraMap I x hf)

/-- **`FormalSpectrum.awayToAtPrimeCompletion` at an arbitrary ideal of `R`.** The underlying ring
map is the same localization map `FormalSpectrum.awayToAtPrime I x hf`; only the ideal both
completions are taken at has changed, from the ideal of definition `I` to `K`.

The point `x` and the basic open still come from `I`: this is not the comparison for a formal
spectrum presented by `K`, and no hypothesis makes `K` an ideal of definition of anything. It is
the second ideal in a cofinal pair, and it exists so that the square below has a lower edge to be
stated at. -/
def awayToAtPrimeCompletionOfIdeal (K : Ideal R) (hK : K.FG) {f : R} (hf : x ∈ basicOpen I f) :
    awayCompletion K f →+*
      AdicCompletion (K.map (algebraMap R (Localization.AtPrime (pointPrime I x))))
        (Localization.AtPrime (pointPrime I x)) :=
  AdicCompletion.mapCompletion (awayToAtPrime I x hf)
    (le_of_eq (map_map_awayToAtPrime I x K hf)) (hK.map _)

/-- At the ideal of definition itself, `FormalSpectrum.awayToAtPrimeCompletionOfIdeal` is
`FormalSpectrum.awayToAtPrimeCompletion`. Both sides are the same `AdicCompletion.mapCompletion`,
and `FormalSpectrum.pointIdeal` is by definition the extension of `I`, so this is `rfl`; it is
stated so that the square below can be read as a statement about the existing comparison. -/
theorem awayToAtPrimeCompletionOfIdeal_self (hI : I.FG) {f : R} (hf : x ∈ basicOpen I f) :
    awayToAtPrimeCompletionOfIdeal I x I hI hf = awayToAtPrimeCompletion I x hI hf :=
  rfl

/-- **The stalk comparison at a basic open commutes with a change of ideal of definition.** For a
containment `I ^ b ≤ J` of ideals of `R`, the two cofinal comparison maps
`AdicCompletion.cofinalHom` — one on the completed localization away from `f`, one on the
completion at the prime under `x` — intertwine `FormalSpectrum.awayToAtPrimeCompletion` at `I` with
its counterpart at `J`.

This is `AdicCompletion.mapCompletion_comp_cofinalHom`
(`FormalSchemes.CofinalCompletionFunctorial`) at a single instantiation: the ring map is
`FormalSpectrum.awayToAtPrime I x hf`, the two source ideals are the extensions of `I` and `J` to
`Localization.Away f`, the two target ideals their extensions to
`Localization.AtPrime (FormalSpectrum.pointPrime I x)`, the four compatibilities are
`FormalSpectrum.map_map_awayToAtPrime` at `I` and at `J`, and the four finite-generation
hypotheses are `Ideal.FG.map`. Nothing is reproved here.

Note what is *not* assumed: neither `I` nor `J` need be an ideal of definition, `J` need not
contain `I`, and there is no second point. See the module docstring for why the two-point spelling
is not the statement. -/
theorem cofinalHom_comp_awayToAtPrimeCompletion {J : Ideal R} (hI : I.FG) (hJ : J.FG)
    {b : ℕ} (hb : I ^ b ≤ J) {f : R} (hf : x ∈ basicOpen I f) :
    (awayToAtPrimeCompletionOfIdeal I x J hJ hf).comp
        (AdicCompletion.cofinalHom
            (Ideal.pow_map_le_map hb (algebraMap R (Localization.Away f)))) =
      (AdicCompletion.cofinalHom
          (Ideal.pow_map_le_map hb
            (algebraMap R (Localization.AtPrime (pointPrime I x))))).comp
        (awayToAtPrimeCompletion I x hI hf) :=
  AdicCompletion.mapCompletion_comp_cofinalHom (awayToAtPrime I x hf) _ _
    (le_of_eq (map_map_awayToAtPrime I x I hf)) (le_of_eq (map_map_awayToAtPrime I x J hf))
    (hI.map _) (hI.map _) (hJ.map _) (hJ.map _)

end FormalSpectrum

end
