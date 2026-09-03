import FormalSchemes.CofinalIdeal

set_option linter.style.header false

/-!
# Being an adic ring only depends on the ideal of definition up to cofinality

`Ideal.IsCofinal` (`FormalSchemes.CofinalIdeal`) records that some power of each of two ideals
lies in the other, and `Ideal.IsCofinal.isAdic` already says that cofinality transports `IsAdic`.
`IsAdicRing` asks for more than `IsAdic`: it also asks for `IsAdicComplete`, which is a statement
about the ideal and not about the topology it induces. This file supplies the missing half, so
that `IsAdicRing` transports too and `FormalScheme.Spf` can be formed at either ideal.

## Why the hypothesis is a cofinality and not a containment

`IsHausdorff.of_le` transfers `IsHausdorff` only *downwards*: it takes `K ≤ I` as a hypothesis and
concludes for the smaller ideal. That was enough for `IsAdicRing.mul` below while that lemma built
its completeness by hand, and is no longer used by it: the product ideal is cofinal with `I`, so the
transport covers it in one step. It is not enough for a transport, where the
two ideals arrive from independent witnesses with no containment between them — for instance the
ideal of definition of a chart of `Y` coming from `f` and the one coming from `g`, in EGA I
10.13's composition law.

Nothing is lost by asking for the stronger hypothesis, because a containment `K ≤ I` carrying a
power `I ^ c ≤ K` *is* a cofinality (`Ideal.IsCofinal.of_le_of_pow_le`): the downward form of
`IsPrecomplete.of_isCofinal` is that lemma at that witness, and is not stated separately anywhere
on the tree.

The cofinal proofs are reindexings of the downward ones. A `K`-Cauchy sequence is no longer
`I`-Cauchy on the nose, so it is first thinned to the subsequence `n ↦ f ((a + 1) * n)`, where
`K ^ (a + 1) ≤ I`; its `I`-adic limit is then also the `K`-adic limit of the original, by the
other containment `I ^ (c + 1) ≤ K`.

## Main results

* `IsHausdorff.of_isCofinal`, `IsPrecomplete.of_isCofinal`, `IsAdicComplete.of_isCofinal`: the
  three completeness conditions transfer between cofinal ideals, with no containment hypothesis.
* `IsHausdorff.of_le`: the downward form of the first, which needs only `K ≤ I`. Kept because a
  containment is not a cofinality, so `IsHausdorff.of_isCofinal` does not subsume it — and kept
  although nothing on the tree calls it; its docstring says why.
* `IsAdicRing.of_isCofinal`: **the transport** — an ideal cofinal with an ideal of definition is
  itself an ideal of definition.
* `IsAdicRing.mul`: the product of two ideals of definition is an ideal of definition. This is the
  nested ideal that `FormalSpectrum.generalCofinalSpfIso` factors through.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.5.
* [The Stacks Project, Tag 0AHZ](https://stacks.math.columbia.edu/tag/0AHZ).
-/

universe u v

section CofinalCompleteness

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- **`IsHausdorff` is antitone in the ideal.** If `K ≤ I` and `M` is `I`-adically Hausdorff, then
`M` is `K`-adically Hausdorff: an element in every `K ^ n • ⊤` lies in every `I ^ n • ⊤`.

Not subsumed by `IsHausdorff.of_isCofinal` below, and not derivable from it: `K ≤ I` alone is not
a cofinality, and the two hypotheses are independent — neither implies the other. The conclusion
census read this pair and classified it in those words, as a *family* and not a subsumption.

**Nothing on the tree calls this**, since issue 1585 gave `IsAdicRing.mul` below its one-step
proof through `IsAdicRing.of_isCofinal`. Kept, on the test the tree applies rather than on the
consumer count: issue 1426 deleted four zero-consumer names because *"their content is one
`congrArg` off a morphism-level identity that keeps its own consumers, so deleting them loses no
fact"*, and issue 805 deleted an API whose hypothesis was unreachable. Neither test is met here —
no surviving statement yields this one in a step, which is exactly what the independence above
says. It is also Mathlib-shaped and absent from Mathlib, whose neighbours
(`IsHausdorff.of_map`, `IsHausdorff.of_isLocalRing`, `IsHausdorff.of_isDomain`,
`IsHausdorff.congr_ringEquiv`) are none of them antitone in the ideal; upstreaming it is a
separate row. -/
theorem IsHausdorff.of_le {K I : Ideal R} (hKI : K ≤ I) [h : IsHausdorff I M] :
    IsHausdorff K M where
  haus' x hx :=
    h.haus x fun n => (hx n).mono (Submodule.smul_mono_left (Ideal.pow_right_mono hKI n))

/-- **`IsHausdorff` transfers between cofinal ideals.** An element lying in every `K ^ n • ⊤` lies
in every `I ^ n • ⊤`, because `K ^ (a n) ≤ I ^ n` for the exponent `a` cofinality supplies. -/
theorem IsHausdorff.of_isCofinal {K I : Ideal R} (h : Ideal.IsCofinal K I)
    [hI : IsHausdorff I M] : IsHausdorff K M where
  haus' x hx := by
    obtain ⟨a, ha⟩ := h.exists_pow_le
    refine hI.haus x fun n => ?_
    refine (hx (a * n)).mono (Submodule.smul_mono_left ?_)
    rw [pow_mul]
    exact Ideal.pow_right_mono ha n

/-- **`IsPrecomplete` transfers between cofinal ideals**, with no containment hypothesis. The
downward form — `K ≤ I` together with a power `I ^ c ≤ K` — is this lemma applied to
`Ideal.IsCofinal.of_le_of_pow_le`, and is not stated separately anywhere on the tree. Its consumer
is `IsAdicComplete.of_isCofinal` below; `IsAdicRing.mul` used to apply it directly at the
containment `I * J ≤ I` and now reaches it through that lemma.

A `K`-Cauchy sequence `f` need not be `I`-Cauchy, so the thinned sequence `n ↦ f ((a + 1) * n)` is
used instead: `K ^ ((a + 1) * m) = (K ^ (a + 1)) ^ m ≤ I ^ m`. Its `I`-adic limit `L` is a `K`-adic
limit of `f`, by comparing `f n` with `f ((a + 1) * ((c + 1) * n))` in two steps, one from the
`K`-Cauchy hypothesis and one from `I ^ ((c + 1) * n) ≤ K ^ n`. -/
theorem IsPrecomplete.of_isCofinal {K I : Ideal R} (h : Ideal.IsCofinal K I)
    [hI : IsPrecomplete I M] : IsPrecomplete K M where
  prec' f hf := by
    obtain ⟨a, ha⟩ := h.exists_pow_succ_le
    obtain ⟨c, hc⟩ := (Ideal.IsCofinal.symm h).exists_pow_succ_le
    have hgI : ∀ {m n : ℕ}, m ≤ n →
        f ((a + 1) * m) ≡ f ((a + 1) * n) [SMOD (I ^ m • ⊤ : Submodule R M)] := by
      intro m n hmn
      refine (hf (Nat.mul_le_mul_left _ hmn)).mono (Submodule.smul_mono_left ?_)
      rw [pow_mul]
      exact Ideal.pow_right_mono ha m
    obtain ⟨L, hL⟩ := hI.prec' (fun n => f ((a + 1) * n)) hgI
    refine ⟨L, fun n => ?_⟩
    have hIK : (I ^ ((c + 1) * n) : Ideal R) ≤ K ^ n := by
      rw [pow_mul]
      exact Ideal.pow_right_mono hc n
    have h1 : f n ≡ f ((a + 1) * ((c + 1) * n)) [SMOD (K ^ n • ⊤ : Submodule R M)] := by
      refine hf ?_
      calc n ≤ (c + 1) * n := Nat.le_mul_of_pos_left n (Nat.succ_pos c)
        _ ≤ (a + 1) * ((c + 1) * n) := Nat.le_mul_of_pos_left _ (Nat.succ_pos a)
    have h2 : f ((a + 1) * ((c + 1) * n)) ≡ L [SMOD (K ^ n • ⊤ : Submodule R M)] :=
      (hL ((c + 1) * n)).mono (Submodule.smul_mono_left hIK)
    exact h1.trans h2

/-- **`IsAdicComplete` transfers between cofinal ideals**, the two halves above combined. -/
theorem IsAdicComplete.of_isCofinal {K I : Ideal R} (h : Ideal.IsCofinal K I)
    [IsAdicComplete I M] : IsAdicComplete K M where
  toIsHausdorff := IsHausdorff.of_isCofinal h
  toIsPrecomplete := IsPrecomplete.of_isCofinal h

end CofinalCompleteness

/-- **An ideal cofinal with an ideal of definition is an ideal of definition.** The topology is
unchanged (`Ideal.IsCofinal.isAdic`) and the completeness transfers
(`IsAdicComplete.of_isCofinal`), so `FormalScheme.Spf` may be formed at either ideal.

Not an instance: `J` does not appear in the hypotheses of the class, so instance search cannot
find it. Callers supply the cofinality and use `haveI`. -/
theorem IsAdicRing.of_isCofinal {R : Type u} [CommRing R] [TopologicalSpace R] {I J : Ideal R}
    [IsAdicRing I] (h : Ideal.IsCofinal I J) : IsAdicRing J where
  toIsAdicComplete := IsAdicComplete.of_isCofinal (Ideal.IsCofinal.symm h)
  isAdic := Ideal.IsCofinal.isAdic h IsAdicRing.isAdic

/-- **The product of two ideals of definition is an ideal of definition.** It is nested below `I`,
and some power of `I` lies in it because some power of `I` lies in `J` (`IsAdic.exists_pow_le`);
those two containments *are* a cofinality (`Ideal.IsCofinal.of_le_of_pow_le`), so this is
`IsAdicRing.of_isCofinal` above at that witness. One step gives both halves: the topology by
`Ideal.IsCofinal.isAdic` and the completeness by `IsAdicComplete.of_isCofinal`, where assembling
them by hand took `IsAdic.of_le_of_pow_le`, `IsHausdorff.of_le` and `IsPrecomplete.of_isCofinal`
separately. The transfer has to be algebraic either way: `IsAdic.isAdicComplete_iff`
would need a `UniformSpace R` instance, which the adic-ring setting does not carry.

`J`'s only role is to supply the power: the statement is symmetric in the two ideals, but the
proof descends into `I` and never into `J`.

This is the ideal `FormalSpectrum.generalCofinalSpfIso`
(`FormalSchemes.CofinalSheafComparisonGeneral`) factors through, stated here so that the
factorisation can be *stated* (`FormalSpectrum.generalCofinalSpfIso_eq`) and not only used inside
that construction.

Not an instance: `I * J` is not a pattern instance search can key on without looping. -/
theorem IsAdicRing.mul {R : Type u} [CommRing R] [TopologicalSpace R] (I J : Ideal R)
    [IsAdicRing I] [IsAdicRing J] : IsAdicRing (I * J) := by
  obtain ⟨m, hm⟩ := IsAdic.exists_pow_le (IsAdicRing.isAdic (I := J)) (IsAdicRing.isAdic (I := I))
  have hKI : (I * J : Ideal R) ≤ I := Ideal.mul_le_right
  refine IsAdicRing.of_isCofinal (Ideal.IsCofinal.of_le_of_pow_le hKI (n := m + 1) ?_).symm
  rw [pow_succ]
  calc I ^ m * I ≤ J * I := Ideal.mul_mono hm le_rfl
    _ = I * J := mul_comm J I
