import FormalSchemes.RestrictedPowerSeries

set_option linter.style.header false

/-!
# The formal completion of an affine scheme along a closed subscheme

For a commutative ring `R` and a finitely generated ideal `I`, the **formal completion of
`Spec R` along the closed subscheme `V(I)`** is the formal spectrum of the `I`-adic completion
`R^ = AdicCompletion I R` (EGA I, 10.8; Stacks, Tag 0AIX). This file constructs it and
identifies its underlying space.

The key algebraic input is that completion does not change the infinitesimal thickenings:
`R^ ⧸ (I·R^) ^ n ≅ R ⧸ I ^ n` (`AdicCompletion.quotientEquivPow`), because the kernel of
`evalₐ I n : R^ → R ⧸ I ^ n` is exactly `(I·R^) ^ n` when `I` is finitely generated. Level `1`
of this identification says that the underlying space of the completion is `Spec (R ⧸ I)`,
i.e. the closed subset `V(I) ⊆ Spec R` — the formal completion is supported on the closed
subscheme one completes along, as it must be.

## Main definitions and results

* `AdicCompletion.idealOfDefinition I`: the ideal of definition `I·R^` of the completion.
* `AdicCompletion.ker_evalₐ`: `ker (evalₐ I n) = (I·R^) ^ n` for finitely generated `I`.
* `AdicCompletion.quotientEquivPow`: `R^ ⧸ (I·R^) ^ n ≃+* R ⧸ I ^ n`.
* `formalCompletion R I hI : FormalScheme`: the formal completion of `Spec R` along `V(I)`.
* `formalCompletionHomeo`: its underlying space is homeomorphic to `Spec (R ⧸ I)`.
* `range_toPrimeSpectrum_formalCompletion`: which sits inside `Spec R` as the closed subset
  `V(I)`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open Ideal AlgebraicGeometry

universe u

namespace AdicCompletion

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The ideal of definition `I·R^` of the `I`-adic completion of `R`. -/
abbrev idealOfDefinition : Ideal (AdicCompletion I R) :=
  I.map (algebraMap R (AdicCompletion I R))

/-- The powers of the ideal of definition of the completion are exactly the kernels of the
evaluation maps to the thickenings, for `I` finitely generated. -/
theorem ker_evalₐ (hI : I.FG) (n : ℕ) :
    RingHom.ker (evalₐ I n).toRingHom = (idealOfDefinition I) ^ n := by
  have heq : ((I ^ n • ⊤ : Ideal R)) = I ^ n := by ext y; simp
  have hsmul : ((idealOfDefinition I) ^ n • ⊤ : Submodule (AdicCompletion I R)
      (AdicCompletion I R)) = ((idealOfDefinition I) ^ n : Ideal (AdicCompletion I R)) := by
    ext y
    simp
  -- `evalₐ` is `eval` followed by an isomorphism of the two quotient presentations
  have hcompute : ∀ x : AdicCompletion I R,
      evalₐ I n x = Ideal.quotientEquivAlgOfEq R heq (eval I R n x) := fun _ => rfl
  ext x
  rw [RingHom.mem_ker]
  change evalₐ I n x = 0 ↔ _
  rw [hcompute x, map_eq_zero_iff _ (Ideal.quotientEquivAlgOfEq R heq).injective]
  rw [show ((0 : R ⧸ (I ^ n • ⊤ : Ideal R)) = 0) from rfl]
  constructor
  · intro hx
    have hmem : x ∈ (I ^ n • ⊤ : Submodule R (AdicCompletion I R)) := by
      rw [AdicCompletion.pow_smul_top_eq_ker_eval hI]
      exact hx
    rw [← Ideal.mem_map_pow_iff_mem_smul_top I n x, hsmul] at hmem
    exact hmem
  · intro hx
    rw [← hsmul, Ideal.mem_map_pow_iff_mem_smul_top I n x,
      AdicCompletion.pow_smul_top_eq_ker_eval hI] at hx
    exact hx

/-- **Completion does not change the infinitesimal thickenings**: the `n`-th thickening of the
completion `R^` is the `n`-th thickening `R ⧸ I ^ n` of `R` itself. -/
def quotientEquivPow (hI : I.FG) (n : ℕ) :
    AdicCompletion I R ⧸ (idealOfDefinition I) ^ n ≃+* R ⧸ I ^ n :=
  (Ideal.quotEquivOfEq (ker_evalₐ I hI n).symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := (evalₐ I n).toRingHom) (surjective_evalₐ I n))

theorem quotientEquivPow_mk (hI : I.FG) (n : ℕ) (x : AdicCompletion I R) :
    quotientEquivPow I hI n (Ideal.Quotient.mk _ x) = evalₐ I n x :=
  rfl

/-- Level `1`: the residue ring of the completion is the residue ring of `R`. -/
def quotientEquiv (hI : I.FG) :
    AdicCompletion I R ⧸ (idealOfDefinition I) ≃+* R ⧸ I :=
  (Ideal.quotEquivOfEq (pow_one (idealOfDefinition I)).symm).trans
    ((quotientEquivPow I hI 1).trans (Ideal.quotEquivOfEq (pow_one I)))

end AdicCompletion

/-- The **formal completion of `Spec R` along `V(I)`** (EGA I, 10.8): the formal spectrum of the
`I`-adic completion of `R`, for a finitely generated ideal `I`. -/
def formalCompletion (R : Type u) [CommRing R] (I : Ideal R) (hI : I.FG) : FormalScheme :=
  haveI := AdicCompletion.isAdicRing_map I hI
  FormalScheme.Spf (AdicCompletion.idealOfDefinition I)

namespace formalCompletion

variable {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)

/-- The underlying space of the formal completion of `Spec R` along `V(I)` is `Spec (R ⧸ I)`:
the completion is supported on the closed subscheme one completes along. -/
def homeo :
    FormalSpectrum (AdicCompletion.idealOfDefinition I) ≃ₜ PrimeSpectrum (R ⧸ I) :=
  PrimeSpectrum.homeomorphOfRingEquiv (AdicCompletion.quotientEquiv I hI)

/-- The formal completion sits inside `Spec R` as the closed subset `V(I)`: composing the
identification of its space with `Spec (R ⧸ I)` and the closed embedding of the latter, the
range is the zero locus of `I`. -/
theorem range_comap_mk :
    Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I) ∘ (homeo I hI)) =
      PrimeSpectrum.zeroLocus (I : Set R) := by
  rw [Set.range_comp, (homeo I hI).surjective.range_eq, Set.image_univ]
  have h := range_comap_of_surjective _ (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  rwa [Ideal.mk_ker] at h

end formalCompletion
