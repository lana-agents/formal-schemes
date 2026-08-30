import FormalSchemes.CofinalIdeal
import Mathlib.RingTheory.AdicCompletion.Basic

set_option linter.style.header false

/-!
# Adic completeness only depends on the ideal up to cofinality

`Ideal.IsCofinal.isAdic` (`FormalSchemes.CofinalIdeal`) says cofinal ideals induce the same adic
*topology*. This file says the same for the three completeness conditions Mathlib states against a
fixed ideal — `IsHausdorff`, `IsPrecomplete` and `IsAdicComplete` — for an arbitrary module, not
only for the ring itself.

## Why the tree needs it

`AlgebraicGeometry.IsTopologicallyFiniteType.of_span_awayCompletion`
(`FormalSchemes.TopFiniteTypeAffineLocal`) carries `[IsAdicComplete L A]` together with the
on-the-nose identity `I · A = L`. A consumer coming from geometry does not have the on-the-nose
identity: an affine open of `Spf I` is presented by a ring `B` with an ideal of definition pinned
only up to `Ideal.IsCofinal`, because an isomorphism of formal spectra sees an ideal only through
its radical (`FormalSpectrum.isCofinal_map_spfIsoRingEquiv`, `FormalSchemes.SpfIsoIdealRecovery`).
So such a consumer must first replace the given ideal by `I · B` and re-derive the completeness
instance along the way. That step is this file.

## The proof, and the one place it is not formal

Both directions reindex the filtration. Cofinality gives `J ^ (n + 1) ≤ I` and `I ^ (m + 1) ≤ J`,
hence `J ^ ((n + 1) * k) ≤ I ^ k` and `I ^ ((m + 1) * p) ≤ J ^ p` by `pow_mul`, and `SModEq.mono`
transports a congruence along either.

For `IsHausdorff` that is the whole proof. For `IsPrecomplete` it is not: a `J`-Cauchy sequence
`f` has to be *thinned* to the `I`-Cauchy sequence `k ↦ f ((n + 1) * k)` before Mathlib's
hypothesis applies, and the limit `L` it produces then has to be shown to work for `f` itself at
every index — not only along the subsequence. That last step is where `I ^ (m + 1) ≤ J` is spent,
and it is the reason **both** containments are needed even though only one is needed for
`IsHausdorff`.

The `+ 1` matters: `Ideal.IsCofinal` is stated with bare existentials, and `J ^ 0 = ⊤ ≤ I` holds
only when `I = ⊤`, so a raw exponent could be `0` and the reindexing `p ≤ (n + 1) * ((m + 1) * p)`
would fail. `Ideal.IsCofinal.exists_pow_succ_le` is what rules that out.

## Main results

* `Ideal.IsCofinal.isHausdorff`, `Ideal.IsCofinal.isPrecomplete`,
  `Ideal.IsCofinal.isAdicComplete`: the three transfers.
* `IsAdicComplete.pow`: the transfer applied to a positive power of the ideal — the same
  application `IsTopologicallyFiniteType.pow` (`FormalSchemes.CofinalTopFiniteType`) makes of
  `Ideal.IsCofinal.pow`, and the standard witness that the relation is not equality.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. 0, §7.2.
* [The Stacks Project, Tag 0317](https://stacks.math.columbia.edu/tag/0317).
-/

universe u v

variable {R : Type u} [CommRing R] {I J : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace Ideal.IsCofinal

/-- **Hausdorffness only depends on the ideal up to cofinality.** Only the containment
`J ^ (n + 1) ≤ I` is used: a `J`-adically small element is `I`-adically small after reindexing
`k ↦ (n + 1) * k`, and `IsHausdorff I M` then kills it. -/
theorem isHausdorff (h : IsCofinal I J) [IsHausdorff I M] : IsHausdorff J M := by
  obtain ⟨n, hn⟩ := h.symm.exists_pow_succ_le
  refine ⟨fun x hx => IsHausdorff.haus ‹IsHausdorff I M› x fun k => ?_⟩
  refine SModEq.mono (Submodule.smul_mono ?_ le_rfl) (hx ((n + 1) * k))
  rw [pow_mul]
  exact Ideal.pow_right_mono hn k

/-- **Precompleteness only depends on the ideal up to cofinality.** Unlike
`Ideal.IsCofinal.isHausdorff` this needs both containments. A `J`-Cauchy sequence `f` is thinned
to `k ↦ f ((n + 1) * k)`, which is `I`-Cauchy because `J ^ ((n + 1) * k) ≤ I ^ k`; the limit `L`
that `IsPrecomplete I M` returns is then a limit of `f` itself, because
`I ^ ((m + 1) * p) ≤ J ^ p` compares `L` to a far-out term of the subsequence and the Cauchy
hypothesis on `f` compares that term to `f p`. -/
theorem isPrecomplete (h : IsCofinal I J) [IsPrecomplete I M] : IsPrecomplete J M := by
  obtain ⟨m, hm⟩ := h.exists_pow_succ_le
  obtain ⟨n, hn⟩ := h.symm.exists_pow_succ_le
  have hJI : ∀ k : ℕ, (J ^ ((n + 1) * k) • ⊤ : Submodule R M) ≤ I ^ k • ⊤ := by
    intro k
    refine Submodule.smul_mono ?_ le_rfl
    rw [pow_mul]
    exact Ideal.pow_right_mono hn k
  have hIJ : ∀ p : ℕ, (I ^ ((m + 1) * p) • ⊤ : Submodule R M) ≤ J ^ p • ⊤ := by
    intro p
    refine Submodule.smul_mono ?_ le_rfl
    rw [pow_mul]
    exact Ideal.pow_right_mono hm p
  refine ⟨fun f hf => ?_⟩
  obtain ⟨L, hL⟩ := IsPrecomplete.prec ‹IsPrecomplete I M›
    (f := fun k => f ((n + 1) * k)) (fun {k l} hkl =>
      SModEq.mono (hJI k) (hf (Nat.mul_le_mul_left (n + 1) hkl)))
  refine ⟨L, fun p => ?_⟩
  have hstep : f p ≡ f ((n + 1) * ((m + 1) * p)) [SMOD (J ^ p • ⊤ : Submodule R M)] := by
    refine hf ?_
    exact (Nat.le_mul_of_pos_left p (Nat.succ_pos m)).trans
      (Nat.le_mul_of_pos_left _ (Nat.succ_pos n))
  exact hstep.trans (SModEq.mono (hIJ p) (hL ((m + 1) * p)))

/-- **Adic completeness only depends on the ideal up to cofinality**, the conjunction of
`Ideal.IsCofinal.isHausdorff` and `Ideal.IsCofinal.isPrecomplete`.

This is the form a consumer wants: it lets a completeness instance obtained for one ideal of
definition of an adic ring be used against any other, which is what makes
`AlgebraicGeometry.IsTopologicallyFiniteType.of_span_awayCompletion`
(`FormalSchemes.TopFiniteTypeAffineLocal`) applicable to a ring presented by geometry, where the
ideal is pinned only up to cofinality. -/
theorem isAdicComplete (h : IsCofinal I J) [IsAdicComplete I M] : IsAdicComplete J M :=
  haveI := h.isHausdorff (M := M)
  haveI := h.isPrecomplete (M := M)
  ⟨⟩

end Ideal.IsCofinal

/-- **A module complete for `I` is complete for every positive power of `I`.** An application of
`Ideal.IsCofinal.isAdicComplete` to `Ideal.IsCofinal.pow` (`FormalSchemes.CofinalIdeal`), and the
standard witness that the transfer is not vacuous: `I` and `I ^ 2` are different ideals with the
same completions, the same example that refutes the on-the-nose form of
`FormalSpectrum.isCofinal_map_spfIsoRingEquiv` (`FormalSchemes.SpfIsoIdealRecovery`).

Compare `IsTopologicallyFiniteType.pow` (`FormalSchemes.CofinalTopFiniteType`), which is the same
application of the same instance of `Ideal.IsCofinal` one layer up. -/
theorem IsAdicComplete.pow [IsAdicComplete I M] {k : ℕ} (hk : k ≠ 0) :
    IsAdicComplete (I ^ k) M :=
  (Ideal.IsCofinal.pow I hk).isAdicComplete
