import FormalSchemes.AdicSubringComplete

set_option linter.style.header false

/-!
# The filtration bridge at a principal ideal, and the ideal it contracts to

`FormalSchemes.AdicSubringComplete` reduces adic completeness of a subring `S ⊆ A` for the
contracted ideal `K.comap S.subtype` to two inputs: the topological half
`Subring.IsInducedPrecomplete`, which adic closedness gives for free, and the *filtration bridge*
`Subring.HasCofinalInducedFiltration`, which it proves under either of two hypotheses. One of
them, `Subring.hasCofinalInducedFiltration_span_singleton`, asks for `K` to be principal on a
`c ∈ S` for which `S` is saturated under multiplication by `c`.

This file supplies what a consumer of that criterion needs but `AdicSubringComplete` does not
state:

* the saturation hypothesis for an **intersection of two equalizer subrings** — the shape every
  chart ring on this tree has — from left-regularity of `c`'s image under one map of each pair;
* the **contracted ideal itself**, which under the same saturation hypothesis is principal on
  `⟨c, hc⟩`, hence finitely generated. Finite generation is a *separate* obligation from
  completeness, so this is not a corollary of the bridge; it is a second consequence of the same
  saturation hypothesis;
* the degenerate case `K = ⊥`, where the bridge holds with no hypothesis at all — which
  `hasCofinalInducedFiltration_span_singleton` does **not** cover, since its saturation hypothesis
  at `c = 0` says `S = ⊤`.

## Main results

* `Subring.hasCofinalInducedFiltration_bot` — the bridge at `K = ⊥`, unconditionally.
* `RingHom.mem_inf_eqLocus_of_mul_mem` — saturation of `f₁.eqLocus g₁ ⊓ f₂.eqLocus g₂` under
  multiplication by `c`, from `IsLeftRegular (f₁ c)` and `IsLeftRegular (f₂ c)`.
* `Subring.hasCofinalInducedFiltration_inf_eqLocus` — the bridge for such an intersection at
  `K = Ideal.span {c}`.
* `Subring.comap_span_singleton_subtype` — the contracted ideal is `Ideal.span {⟨c, hc⟩}`, and
  `Subring.fg_comap_span_singleton` its finite generation.
* `Subring.isAdicComplete_comap_span_singleton_inf_eqLocus` — the three inputs assembled: an
  intersection of two equalizers, adically closed and Hausdorff, is adically complete for the
  contracted ideal when the ambient ideal is principal on a `c` with left-regular images.

## What is *not* proved

* **Nothing here supplies left-regularity.** Both regularity hypotheses are carried as explicit
  arguments in every statement below, and no `(A, K, S)` at which the bridge fails is exhibited —
  so the bridge is not shown *necessary* either.
* Nothing here says the contracted ideal is Hausdorff or that `S` is closed; those are
  `AlgebraicGeometry.isHausdorff_comap_subtype` and
  `RingHom.isAdicallyClosed_inf_eqLocus` (`FormalSchemes.AdicSubringComplete`) respectively, and
  the assembly below takes both as hypotheses.

## References

* [Atiyah–Macdonald, *Introduction to Commutative Algebra*][atiyah-macdonald], Ch. 10.
-/

universe u

namespace Subring

variable {A : Type u} [CommRing A]

/-- **The filtration bridge is free at `K = ⊥`.** Both filtrations are `⊤` at `n = 0` and `⊥`
afterwards, because `⊥.comap S.subtype = ⊥` for the injective `S.subtype`.

This case is *not* covered by `Subring.hasCofinalInducedFiltration_span_singleton`: at `c = 0` its
saturation hypothesis reads `0 ∈ S → a ∈ S` for every `a`, i.e. `S = ⊤`. -/
theorem hasCofinalInducedFiltration_bot (S : Subring A) :
    S.HasCofinalInducedFiltration (⊥ : Ideal A) := by
  intro n
  refine ⟨n, fun x hx => ?_⟩
  rw [Ideal.comap_bot_of_injective S.subtype S.subtype_injective]
  cases n with
  | zero => simp
  | succ k =>
    have hx0 : x = 0 :=
      Subtype.ext (Ideal.mem_bot.1 (Ideal.pow_le_self (Nat.succ_ne_zero k) hx))
    rw [hx0]
    exact zero_mem _

end Subring

namespace RingHom

variable {A B₁ B₂ : Type u} [CommRing A] [CommRing B₁] [CommRing B₂]

/-- **An intersection of two equalizer subrings is saturated for multiplication by `c`** as soon
as `c` lies in it and its image under the *first* map of each pair is left-regular. This is
`RingHom.mem_eqLocus_of_mul_mem` applied to each factor; it is the hypothesis
`Subring.hasCofinalInducedFiltration_span_singleton` asks for, in the shape the chart rings on
this tree have (`AlgebraicGeometry.tateInvNodeChartAwaySubring_eq_inf_eqLocus`). -/
theorem mem_inf_eqLocus_of_mul_mem {f₁ g₁ : A →+* B₁} {f₂ g₂ : A →+* B₂} {c : A}
    (hc : c ∈ f₁.eqLocus g₁ ⊓ f₂.eqLocus g₂) (hreg₁ : IsLeftRegular (f₁ c))
    (hreg₂ : IsLeftRegular (f₂ c)) {a : A} (hca : c * a ∈ f₁.eqLocus g₁ ⊓ f₂.eqLocus g₂) :
    a ∈ f₁.eqLocus g₁ ⊓ f₂.eqLocus g₂ :=
  Subring.mem_inf.2
    ⟨mem_eqLocus_of_mul_mem (Subring.mem_inf.1 hc).1 hreg₁ (Subring.mem_inf.1 hca).1,
      mem_eqLocus_of_mul_mem (Subring.mem_inf.1 hc).2 hreg₂ (Subring.mem_inf.1 hca).2⟩

end RingHom

namespace Subring

variable {A B₁ B₂ : Type u} [CommRing A] [CommRing B₁] [CommRing B₂]

/-- **The filtration bridge for an intersection of two equalizers at a principal ideal.**
`Subring.hasCofinalInducedFiltration_span_singleton` at the saturation
`RingHom.mem_inf_eqLocus_of_mul_mem`. -/
theorem hasCofinalInducedFiltration_inf_eqLocus {f₁ g₁ : A →+* B₁} {f₂ g₂ : A →+* B₂} {c : A}
    (hc : c ∈ f₁.eqLocus g₁ ⊓ f₂.eqLocus g₂) (hreg₁ : IsLeftRegular (f₁ c))
    (hreg₂ : IsLeftRegular (f₂ c)) :
    (f₁.eqLocus g₁ ⊓ f₂.eqLocus g₂).HasCofinalInducedFiltration (Ideal.span {c}) :=
  hasCofinalInducedFiltration_span_singleton hc fun _ hca =>
    RingHom.mem_inf_eqLocus_of_mul_mem hc hreg₁ hreg₂ hca

variable {A : Type u} [CommRing A]

/-- **The contracted ideal of a principal ideal is principal**, under the same saturation
hypothesis that buys the filtration bridge: an element of `S` divisible by `c` in `A` is `c` times
an element of `S`. -/
theorem comap_span_singleton_subtype {S : Subring A} {c : A} (hc : c ∈ S)
    (hsat : ∀ a : A, c * a ∈ S → a ∈ S) :
    (Ideal.span {c}).comap S.subtype = Ideal.span {(⟨c, hc⟩ : S)} := by
  refine le_antisymm (fun x hx => ?_) (Ideal.span_le.2 ?_)
  · rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hx
    obtain ⟨a, ha⟩ := hx
    have haS : a ∈ S := hsat a (by rw [← ha]; exact x.2)
    rw [Ideal.mem_span_singleton]
    exact ⟨⟨a, haS⟩, Subtype.ext ha⟩
  · rintro y rfl
    exact Ideal.mem_comap.2 (Ideal.mem_span_singleton_self c)

/-- **The contracted ideal is finitely generated**, being principal by
`Subring.comap_span_singleton_subtype`. Finite generation is a separate obligation from
completeness and is not implied by it; this is the second consequence of the saturation
hypothesis. -/
theorem fg_comap_span_singleton {S : Subring A} {c : A} (hc : c ∈ S)
    (hsat : ∀ a : A, c * a ∈ S → a ∈ S) :
    ((Ideal.span {c}).comap S.subtype).FG := by
  rw [comap_span_singleton_subtype hc hsat]
  exact ⟨{(⟨c, hc⟩ : S)}, by simp⟩

end Subring

namespace Subring

variable {A B₁ B₂ : Type u} [CommRing A] [CommRing B₁] [CommRing B₂]

/-- **Adic completeness of an intersection of two equalizers at a principal ideal.** The three
inputs of `Subring.isAdicComplete_comap_subtype`, with the filtration bridge supplied by
`Subring.hasCofinalInducedFiltration_inf_eqLocus`: Hausdorffness of the contracted ideal, adic
closedness of the intersection, and left-regularity of the two images of the generator.

The closedness hypothesis is what `RingHom.isAdicallyClosed_inf_eqLocus` produces from continuity
of the four maps, and the Hausdorff hypothesis is what
`AlgebraicGeometry.isHausdorff_comap_subtype` produces from Hausdorffness of `A`. -/
theorem isAdicComplete_comap_span_singleton_inf_eqLocus {f₁ g₁ : A →+* B₁} {f₂ g₂ : A →+* B₂}
    {c : A} (hc : c ∈ f₁.eqLocus g₁ ⊓ f₂.eqLocus g₂) (hreg₁ : IsLeftRegular (f₁ c))
    (hreg₂ : IsLeftRegular (f₂ c))
    (hh : IsHausdorff ((Ideal.span {c}).comap (f₁.eqLocus g₁ ⊓ f₂.eqLocus g₂).subtype)
      ↥(f₁.eqLocus g₁ ⊓ f₂.eqLocus g₂))
    (hcl : (f₁.eqLocus g₁ ⊓ f₂.eqLocus g₂).IsAdicallyClosed (Ideal.span {c}))
    [IsPrecomplete (Ideal.span {c}) A] :
    IsAdicComplete ((Ideal.span {c}).comap (f₁.eqLocus g₁ ⊓ f₂.eqLocus g₂).subtype)
      ↥(f₁.eqLocus g₁ ⊓ f₂.eqLocus g₂) :=
  isAdicComplete_comap_subtype hh (isInducedPrecomplete_of_isAdicallyClosed hcl)
    (hasCofinalInducedFiltration_inf_eqLocus hc hreg₁ hreg₂)

end Subring
