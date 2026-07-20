import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.Algebra.MvPolynomial.CommRing

set_option linter.style.header false

/-!
# Restricted power series over an adic ring

For a commutative ring `R`, an ideal `I ⊆ R` and a natural number `n`, the ring of *restricted
power series* `R{X₁, …, Xₙ}` (also written `R⟨X₁, …, Xₙ⟩`) is the completion of the polynomial ring
`R[X₁, …, Xₙ]` for the `I`-adic topology. Concretely, when `R` is `I`-adically complete and
separated it is the subring of the formal power series ring consisting of series
`Σ_ν a_ν X^ν` whose coefficients `a_ν` tend to `0` `I`-adically, i.e. for every `k` all but finitely
many coefficients lie in `I ^ k`. It is the ring of functions on the *formal polydisc* over
`Spf R` and is the basic building block for constructions of formal schemes by adic completion.

This file gives the concrete `AdicCompletion` model of `R{X}`. We define it as the `I`-adic
completion of `MvPolynomial (Fin n) R`, where "`I`-adic" means the topology of the *extended ideal*
`I · R[X] = I.map (algebraMap R (MvPolynomial (Fin n) R))`. Because `RestrictedPowerSeries I n` is
*by definition* this completion, the identification with
`AdicCompletion (I.map (algebraMap R (MvPolynomial (Fin n) R))) (MvPolynomial (Fin n) R)` is
definitional and the corresponding `RingEquiv` is `RingEquiv.refl`.

The *ideal of definition* of `R{X}` is the extension of `I · R[X]` to `R{X}`, namely
`RestrictedPowerSeries.idealOfDefinition I n`. When `I` is finitely generated, `R{X}` is
complete and separated for this ideal, so it is an adic ring in the sense of
`FormalSchemes.AdicRing`.

## Main definitions

* `RestrictedPowerSeries I n`: the ring `R{X₁, …, Xₙ}` of restricted power series, defined as the
  `I·R[X]`-adic completion of `MvPolynomial (Fin n) R`.
* `RestrictedPowerSeries.idealOfDefinition I n`: the ideal of definition of `R{X}`, the extension of
  the extended ideal `I · R[X]` to `R{X}`.

## Main results

* `RestrictedPowerSeries.adicCompletionEquiv`: the (definitional) ring isomorphism identifying
  `R{X}` with the adic completion of `R[X]` for the extended ideal.
* `RestrictedPowerSeries.isAdicComplete`: for `I` finitely generated, `R{X}` is adically complete
  for its ideal of definition.

## TODO

* The universal property of the formal polydisc: for a complete adic `R`-algebra `S` and a tuple
  `x : Fin n → S`, the `R`-algebra homomorphism `R{X} → S` extending `MvPolynomial.aeval x`
  (evaluation at `x`). This is deferred to future work.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*][bosch2014], LNM 2105, §7.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1.
* [The Stacks Project, Tag 0AKA](https://stacks.math.columbia.edu/tag/0AKA)
-/

variable {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ)

/-- The ring of **restricted power series** `R{X₁, …, Xₙ}` over `R` for the ideal `I`, defined as
the completion of the polynomial ring `MvPolynomial (Fin n) R` for the `I`-adic topology, i.e. the
adic completion for the extended ideal `I · R[X] = I.map (algebraMap R (MvPolynomial (Fin n) R))`.

This is an `abbrev`, so all ring, module and algebra instances of `AdicCompletion` are inherited
automatically. In particular `R{X}` is a commutative ring and an algebra over
`MvPolynomial (Fin n) R` (and over `R`). -/
abbrev RestrictedPowerSeries : Type _ :=
  AdicCompletion (I.map (algebraMap R (MvPolynomial (Fin n) R))) (MvPolynomial (Fin n) R)

namespace RestrictedPowerSeries

/-- The ring `R{X}` of restricted power series is *by definition* the adic completion of the
polynomial ring `R[X]` for the extended ideal `I · R[X]`. This records that identification as an
explicit ring isomorphism; it is definitionally the identity. -/
noncomputable def adicCompletionEquiv :
    RestrictedPowerSeries I n ≃+*
      AdicCompletion (I.map (algebraMap R (MvPolynomial (Fin n) R))) (MvPolynomial (Fin n) R) :=
  RingEquiv.refl _

/-- The **ideal of definition** of `R{X}`: the extension to `R{X}` of the extended ideal
`I · R[X] = I.map (algebraMap R (MvPolynomial (Fin n) R))` along the structure map
`R[X] → R{X}`. When `I` is finitely generated this ideal makes `R{X}` an adic ring. -/
noncomputable abbrev idealOfDefinition : Ideal (RestrictedPowerSeries I n) :=
  (I.map (algebraMap R (MvPolynomial (Fin n) R))).map
    (algebraMap (MvPolynomial (Fin n) R) (RestrictedPowerSeries I n))

/-- For a finitely generated ideal `I`, the ring of restricted power series `R{X}` is adically
complete for its ideal of definition. Together with the fact that this ideal defines the topology,
this exhibits `R{X}` as an adic ring. This is the completion analogue of
`AdicCompletion.isAdicComplete_self`, applied to the base ring `R[X]` and the extended ideal. -/
theorem isAdicComplete (hI : I.FG) :
    IsAdicComplete (idealOfDefinition I n) (RestrictedPowerSeries I n) :=
  AdicCompletion.isAdicComplete_self (I.map (algebraMap R (MvPolynomial (Fin n) R))) (hI.map _)

end RestrictedPowerSeries
