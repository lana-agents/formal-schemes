import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import FormalSchemes.FormalScheme

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
* `RestrictedPowerSeries.formalPolydisc I n hI`: for `I` finitely generated, the **formal polydisc**
  `Spf R{X}` packaged as an affine `FormalScheme` via `AlgebraicGeometry.FormalScheme.Spf`.
* `RestrictedPowerSeries.eval I n x`: the **evaluation homomorphism** `R{X} → S`, `Xᵢ ↦ xᵢ`, into a
  complete adic `R`-algebra `S`, realizing the universal property of the formal polydisc.

## Main results

* `RestrictedPowerSeries.adicCompletionEquiv`: the (definitional) ring isomorphism identifying
  `R{X}` with the adic completion of `R[X]` for the extended ideal.
* `RestrictedPowerSeries.isAdicComplete`: for `I` finitely generated, `R{X}` is adically complete
  for its ideal of definition.
* `RestrictedPowerSeries.map_pow_map_aeval`: evaluation `aeval x` is continuous for the adic
  topologies — it carries `(I · R[X])^k` onto `(I · S)^k` — which is what lets it extend to `R{X}`.

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

open AlgebraicGeometry in
set_option linter.style.setOption false in
set_option maxHeartbeats 800000 in
-- Building `FormalScheme.Spf` unfolds the structure sheaf (a limit of pushforward sheaves)
-- against the restriction machinery, which is slow; the same bump is used at `FormalScheme.Spf`.
/-- The **formal polydisc** `Spf R{X₁, …, Xₙ}` as an affine formal scheme over an adic ring `R`
with finitely generated ideal of definition `I`. We equip `R{X}` with its ideal-of-definition-adic
topology; `RestrictedPowerSeries.isAdicComplete` then makes it an `IsAdicRing`, so `R{X}` is an
adic ring and `FormalScheme.Spf` (issue 22) produces the affine formal scheme. -/
noncomputable def formalPolydisc (hI : I.FG) : FormalScheme :=
  letI : TopologicalSpace (RestrictedPowerSeries I n) := (idealOfDefinition I n).adicTopology
  haveI : IsAdicRing (idealOfDefinition I n) :=
    { toIsAdicComplete := isAdicComplete I n hI
      isAdic := rfl }
  FormalScheme.Spf (idealOfDefinition I n)

section UniversalProperty

variable {S : Type*} [CommRing S] [Algebra R S]

/-- Evaluation `MvPolynomial.aeval x : R[X] → S` carries the extended ideal `I · R[X]` onto
`I · S`, because it restricts to the structure map `R → S` on constants. -/
theorem map_map_aeval (x : Fin n → S) :
    Ideal.map (MvPolynomial.aeval (R := R) x : MvPolynomial (Fin n) R →+* S)
        (I.map (algebraMap R (MvPolynomial (Fin n) R))) = I.map (algebraMap R S) := by
  simp only [Ideal.map_map, AlgHom.comp_algebraMap]

/-- The power version of `map_map_aeval`: evaluation carries `(I · R[X])^k` onto `(I · S)^k`. -/
theorem map_pow_map_aeval (x : Fin n → S) (k : ℕ) :
    Ideal.map (MvPolynomial.aeval (R := R) x : MvPolynomial (Fin n) R →+* S)
        ((I.map (algebraMap R (MvPolynomial (Fin n) R))) ^ k) = (I.map (algebraMap R S)) ^ k := by
  rw [Ideal.map_pow, map_map_aeval]

variable [IsAdicComplete (I.map (algebraMap R S)) S]

/-- The **evaluation homomorphism** `R{X₁, …, Xₙ} → S`, `Xᵢ ↦ xᵢ`, into a complete adic
`R`-algebra `S` (one that is `I · S`-adically complete). This is the universal property of the
formal polydisc: `aeval x : R[X] → S` is continuous for the adic topologies (`map_pow_map_aeval`),
so it extends uniquely along the completion `R[X] → R{X}` to the complete target `S`. The extension
is built level by level through the finite quotients `S ⧸ (I · S)^k` and assembled with
`IsAdicComplete.liftAlgHom`. -/
noncomputable def eval (x : Fin n → S) : RestrictedPowerSeries I n →ₐ[R] S :=
  IsAdicComplete.liftAlgHom (I.map (algebraMap R S))
    (fun k =>
      (Ideal.quotientMapₐ ((I.map (algebraMap R S)) ^ k) (MvPolynomial.aeval x)
          (by exact Ideal.map_le_iff_le_comap.mp (le_of_eq (map_pow_map_aeval I n x k)))).comp
        ((AdicCompletion.evalₐ
            (I.map (algebraMap R (MvPolynomial (Fin n) R))) k).restrictScalars R))
    (by
      intro a b hab
      apply AlgHom.ext
      intro z
      obtain ⟨c, rfl⟩ :=
        AdicCompletion.mk_surjective (I.map (algebraMap R (MvPolynomial (Fin n) R)))
          (MvPolynomial (Fin n) R) z
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, AdicCompletion.evalₐ_mk,
        Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.factorₐ_apply_mk]
      rw [Ideal.Quotient.eq, ← map_sub]
      have hmem : c.val b - c.val a ∈ (I.map (algebraMap R (MvPolynomial (Fin n) R))) ^ a := by
        rw [← Ideal.Quotient.eq]
        exact AdicCompletion.Ideal.mk_eq_mk _ hab c
      have hmap := Ideal.mem_map_of_mem
        (MvPolynomial.aeval (R := R) x : MvPolynomial (Fin n) R →+* S) hmem
      rwa [map_pow_map_aeval I n x a] at hmap)

end UniversalProperty

end RestrictedPowerSeries
