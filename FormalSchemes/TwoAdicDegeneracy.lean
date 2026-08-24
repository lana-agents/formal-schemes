import FormalSchemes.TwoAdicWitness
import Mathlib.RingTheory.Ideal.Int

set_option linter.style.header false

/-!
# `|Spf ℤ^|` is a one-point space: the degeneracy of the `2`-adic witness, as a theorem

`FormalSchemes/TwoAdicWitness.lean` supplies the standing `2`-adic witness `ℤ^` with its ideal of
definition `(2)·ℤ^`, and it is exactly what the ind-scheme layer needs: the tower `ℤ ⧸ 2ⁿ` is
genuinely infinite, so `[IsAdicRing I]` is visibly not instantiated only at `I = ⊥`.

On the **conclusion** side of the umbrella-59 results, though, that same witness degenerates, and
the modules there say so in prose:

> `FormalSpectrum I` is *defined* as `PrimeSpectrum (R ⧸ I)`, and `ℤ^ ⧸ 2ℤ^ ≅ ℤ ⧸ (2) = 𝔽₂` is a
> field, so `|Spf ℤ^|` is a **one-point space**. Every open of it is `⊥` or `⊤`, so every open
> cover of it has a member equal to `⊤`, and any statement about covers instantiated there says
> nothing.

That claim is the *comparative* half of every non-degeneracy result on the umbrella: it is what
makes "non-degenerate" mean anything when `FormalLineWitness.lean` exhibits a cover of
`|Spf ℤ⟦X⟧| ≃ₜ Spec ℤ` with no member equal to `⊤`. It is asserted in five module docstrings —
`FormalLineWitness.lean`, `ThickeningCoverPullback.lean`, `ThickeningBasicOpenRefinement.lean`,
`ThickeningChartRestrict.lean`, `ThickeningNonDegenerateWitness.lean` — and until this module it
was proved nowhere, so nothing in the toolchain ever checked it.

This module proves it. It is a fact about the witness rather than about the umbrella, so it sits
beside `TwoAdicWitness.lean` in the import order rather than inside the `Thickening*` cluster, and
imports nothing from either.

## Main results

* `Int.span_two_isMaximal`: `(2) ⊆ ℤ` is maximal. A fact about `ℤ`; see the implementation notes.
* `TopologicalSpace.Opens.exists_eq_top_of_subsingleton`: a cover of a nonempty subsingleton space
  has a member equal to `⊤`. No formal-schemes content; see the implementation notes.
* `FormalSpectrum.subsingleton_twoAdic`, `FormalSpectrum.nonempty_twoAdic`: `|Spf ℤ^|` is a
  one-point space.
* `FormalSpectrum.twoAdic_exists_eq_top`: **the contrast, as a theorem.** Every open cover of
  `|Spf ℤ^|` has a member equal to `⊤`.

## Implementation notes

`exists_eq_top_of_subsingleton` is stated in the `TopologicalSpace.Opens` namespace and
`span_two_isMaximal` in `Int`, neither in `FormalSpectrum`: their statements mention no ring, no
ideal and no spectrum, and no formal spectrum respectively. `ThickeningChartRestrict.lean`'s
implementation notes record the rule and why the enclosing `namespace FormalSpectrum` of every
module in this project makes it easy to get wrong.

`Int.span_two_isMaximal` and `isAdicRing_twoAdicIdeal` are activated with
`attribute [local instance]`, so neither escapes this file — moving the first out of
`FormalSpectrum` does not change that, since it is a `theorem` and not an `instance`. A global
`IsMaximal (Ideal.span {2})` would sit in the way of unrelated instance searches, and
`TwoAdicWitness.lean`'s implementation notes give the same reason for the adic instance.

The `Field (ℤ ⧸ (2))` instance must be introduced with `letI`, **not** `haveI`. `Field` is a data
class, `haveI` makes the instance opaque, and the `Unique (PrimeSpectrum R)` instance for a field
then fails to fire with a `failed to synthesize Unique (PrimeSpectrum (ℤ ⧸ Ideal.span {2}))` that
points nowhere near the cause. `Ideal.Quotient.field` is a `def` rather than an `instance`, so it
has to be introduced by hand in the first place.

`Mathlib.RingTheory.Ideal.Int` is a new import for this project, and it is the whole price of the
module: in the current closure `(Ideal.span {(2:ℤ)}).IsMaximal` is not reachable by `exact?`,
`Prime (2 : ℤ)` is closed by neither `exact?` nor `norm_num`, and `Int.quotientSpanEquivZMod` and
`ZMod.instField` are unknown constants. Routes through `Prime (2 : ℤ)` and through `ZMod 2` were
both tried and both need an import of their own.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1, §10.6.
* [The Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

open TopologicalSpace

namespace TopologicalSpace.Opens

/-- **A cover of a nonempty subsingleton space has a member equal to `⊤`.** Purely topological:
the single point lies in some member, and that member therefore contains every point. -/
theorem exists_eq_top_of_subsingleton {α : Type*} [TopologicalSpace α] [Subsingleton α]
    [Nonempty α] {ι : Type*} (V : ι → Opens α) (hV : ⨆ i, V i = ⊤) : ∃ i, V i = ⊤ := by
  obtain ⟨x⟩ := ‹Nonempty α›
  have hx : x ∈ ⨆ i, V i := by rw [hV]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  refine ⟨i, eq_top_iff.mpr fun y _ => ?_⟩
  rwa [Subsingleton.elim y x]

end TopologicalSpace.Opens

namespace Int

/-- `(2) ⊆ ℤ` is a maximal ideal, so `ℤ ⧸ (2)` is a field. This is the one fact the module needs
from `Mathlib.RingTheory.Ideal.Int`; `norm_num` is what turns that file's
`Ideal.span {(2 : ℕ) : ℤ}` spelling into the `Ideal.span {(2 : ℤ)}` this project uses.

A fact about `ℤ` and nothing else, so it lives in `Int` rather than in `FormalSpectrum`. It is
deliberately **not** an instance — see the implementation notes. -/
theorem span_two_isMaximal : (Ideal.span {(2 : ℤ)}).IsMaximal := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := Int.ideal_span_isMaximal_of_prime 2
  norm_num at h
  exact h

end Int

namespace FormalSpectrum

attribute [local instance] isAdicRing_twoAdicIdeal
attribute [local instance] Int.span_two_isMaximal

/-- **`|Spf ℤ^|` has at most one point.** `FormalSpectrum twoAdicIdeal` is by definition
`PrimeSpectrum (ℤ^ ⧸ 2ℤ^)`, and `AdicCompletion.quotientEquiv` identifies that residue ring with
`ℤ ⧸ (2)`, a field; a field has a unique prime. -/
theorem subsingleton_twoAdic : Subsingleton (FormalSpectrum twoAdicIdeal) := by
  letI : Field (ℤ ⧸ Ideal.span {(2 : ℤ)}) := Ideal.Quotient.field _
  exact (PrimeSpectrum.comapEquiv
    (AdicCompletion.quotientEquiv (Ideal.span {(2 : ℤ)})
      (Submodule.fg_span (Set.finite_singleton _)))).toEquiv.subsingleton

/-- **`|Spf ℤ^|` has at least one point** — the zero ideal of the residue field. Together with
`subsingleton_twoAdic` this is the one-point statement; separately, it is what stops
`twoAdic_exists_eq_top` from being vacuous, since over the empty space the empty cover covers. -/
theorem nonempty_twoAdic : Nonempty (FormalSpectrum twoAdicIdeal) := by
  letI : Field (ℤ ⧸ Ideal.span {(2 : ℤ)}) := Ideal.Quotient.field _
  exact ⟨(PrimeSpectrum.comapEquiv
    (AdicCompletion.quotientEquiv (Ideal.span {(2 : ℤ)})
      (Submodule.fg_span (Set.finite_singleton _)))).symm default⟩

/-- **The contrast that five module docstrings on umbrella 59 assert in prose, as a theorem:
every open cover of `|Spf ℤ^|` has a member equal to `⊤`.**

This is what makes the non-degeneracy results of `ThickeningNonDegenerateWitness.lean` say
something. There the cover of `|Spf ℤ⟦X⟧|` provably has *no* member equal to `⊤`; here no cover
can avoid one. Any theorem about covers of `|Spf R|` whose only witness is the `2`-adic one is
therefore a theorem about `⊤`. -/
theorem twoAdic_exists_eq_top {ι : Type*}
    (V : ι → Opens (FormalSpectrum twoAdicIdeal)) (hV : ⨆ i, V i = ⊤) : ∃ i, V i = ⊤ := by
  haveI := subsingleton_twoAdic
  haveI := nonempty_twoAdic
  exact Opens.exists_eq_top_of_subsingleton V hV

end FormalSpectrum
