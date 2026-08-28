import FormalSchemes.Completion
import FormalSchemes.RestrictedPowerSeries

set_option linter.style.header false

/-!
# The standing `2`-adic witness: `ℤ^` with its ideal of definition

Every witness section in the ind-scheme layer — `IndSchemeThickening.lean`,
`IndSchemeLimitComponents.lean`, `IndSchemeExistence.lean`,
`IndSchemeExistenceGeometric.lean` — has to rule out the same degeneracy: that `[IsAdicRing I]`
is only ever instantiated at `I = ⊥`, where every infinitesimal thickening `Spec (R ⧸ Iⁿ⁺¹)` is
`Spec R` itself and the whole layer says nothing. The `2`-adic integers rule it out, and
`twoAdicIdeal_ne_bot` below is the proof — for weeks this file only asserted it, and the
assertion was inherited verbatim by the sections that cite the witness. This file holds the one
witness those sections share, so that they are visibly about the same ring.

Nothing here mentions the ind-scheme layer, and this module imports nothing from it, so it sits
below the whole cluster.

## Main definitions

* `FormalSpectrum.twoAdicIdeal`: the ideal of definition `(2)·ℤ^` of the `2`-adic integers.
* `FormalSpectrum.isAdicRing_twoAdicIdeal`: it makes `ℤ^` an adic ring. Deliberately **not** a
  global instance — see below.

## Implementation notes

`isAdicRing_twoAdicIdeal` is a plain theorem, to be activated per witness section with
`attribute [local instance] isAdicRing_twoAdicIdeal`. Making it global would put it in the way of
every unrelated instance search over `AdicCompletion`, which is a far larger change than sharing
a witness.
-/

noncomputable section

namespace FormalSpectrum

/-- The ideal of definition `(2)·ℤ^` of the `2`-adic integers.

An `abbrev`, matching `AdicCompletion.idealOfDefinition` itself and every other
`idealOfDefinition` in this project, and here it has to be one: two of the four witness sections
state their `example`s with the ideal spelled out, so instance search must see through this name
at `instances` transparency to reach `isAdicRing_twoAdicIdeal`. As a `def` it does not, and those
two sections fail with `failed to synthesize IsAdicRing (AdicCompletion.idealOfDefinition
(Ideal.span {2}))`. -/
abbrev twoAdicIdeal : Ideal (AdicCompletion (Ideal.span {(2 : ℤ)}) ℤ) :=
  AdicCompletion.idealOfDefinition (Ideal.span {(2 : ℤ)})

/-- **The `2`-adic integers, with their ideal of definition, form a complete adic ring.** -/
theorem isAdicRing_twoAdicIdeal : IsAdicRing twoAdicIdeal :=
  AdicCompletion.isAdicRing_map _ (Submodule.fg_span (Set.finite_singleton _))

/-- **The `2`-adic witness really does rule out `I = ⊥`:** `twoAdicIdeal ≠ ⊥`.

Note what the statement is *not*. `twoAdicIdeal` is `(2)·ℤ^`, an ideal of the ring `ℤ^`, so this
is not `Ideal.span {(2 : ℤ)} ≠ ⊥` — that one is `Ideal.span_singleton_eq_bot` and `two_ne_zero`,
and it says nothing about the ideal every witness section below actually quantifies over.

`AdicCompletion.idealOfDefinition_ne_bot` reduces it to `2 ∉ (2)² = (4)` in `ℤ`. -/
theorem twoAdicIdeal_ne_bot : twoAdicIdeal ≠ ⊥ :=
  AdicCompletion.idealOfDefinition_ne_bot _ (Ideal.mem_span_singleton_self (2 : ℤ))
    (n := 2) <| by
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      decide

end FormalSpectrum

end
