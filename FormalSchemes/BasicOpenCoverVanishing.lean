import FormalSchemes.BasicOpenChart
import Mathlib.RingTheory.Localization.Away.Basic

set_option linter.style.header false

/-!
# Structure-sheaf separatedness: vanishing on a basic-open cover

Let `S` be an adic ring with (finitely generated) ideal of definition `J`, and let `t : S`.
The residue `t̄ ∈ S ⧸ J` is a global section of the structure sheaf of `Spf S`, and the structure
sheaf is *separated*: if `t̄` vanishes on a family of basic opens `D(ḡ)` (`g ∈ T`) whose residues
generate the unit ideal of `S ⧸ J` — i.e. the `D(ḡ)` cover `Spf S` — then `t̄ = 0`, that is
`t ∈ J`.

Vanishing of `t̄` on `D(ḡ)` is expressed at the level of sections: the completed-localization image
`awayCompletionHom J g t` lies in the ideal of definition `awayCompletionIdeal J g` of the chart
`R{1/g}`. Passing to the level-`0` residue via `awayCompletionResidueEquiv` (which needs `J.FG`),
this is exactly the statement that `t̄` becomes zero in the localization `(S ⧸ J)_{ḡ}`, and the
conclusion is the injectivity of `S ⧸ J → ∏ (S ⧸ J)_{ḡ}` along a spanning family
(`Localization.algebraMap_injective_of_span_eq_top`).

This is the elementary, purely algebraic half of the adic-source-descent lemma
`le_comap_globalSectionsMap_of_cover` (issue 471); the topological reflection input and the
quasi-compact finite-subcover reduction are the companion issues 471a / 471c.

## Main result

* `FormalSpectrum.mem_of_forall_basicOpen`: a section vanishing on a spanning basic-open family
  lies in the ideal of definition.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1.
-/

noncomputable section

open TopologicalSpace Topology

universe u

namespace FormalSpectrum

variable {S : Type u} [CommRing S] (J : Ideal S)

/-- **Structure-sheaf separatedness along a basic-open cover.**
Let `J` be a finitely generated ideal of `S` and `t : S`. If the residues `ḡ` (`g ∈ T`) of a family
of elements generate the unit ideal of `S ⧸ J` (equivalently, the basic opens `D(ḡ)` cover `Spf S`)
and the section `t` vanishes on each chart `D(ḡ)`, i.e.
`awayCompletionHom J g t ∈ awayCompletionIdeal J g`, then `t ∈ J`. -/
theorem mem_of_forall_basicOpen (hJ : J.FG) (t : S) (T : Set S)
    (hspan : Ideal.span (Ideal.Quotient.mk J '' T) = ⊤)
    (hvan : ∀ g ∈ T, awayCompletionHom J g t ∈ awayCompletionIdeal J g) :
    t ∈ J := by
  -- Each vanishing condition becomes vanishing of the residue `t̄` in the localization `(S⧸J)_{ḡ}`.
  have hloc : ∀ g ∈ T, algebraMap (S ⧸ J) (Localization.Away (Ideal.Quotient.mk J g))
      (Ideal.Quotient.mk J t) = 0 := by
    intro g hg
    -- `awayCompletionHom J g t ∈ awayCompletionIdeal J g` says the residue map kills `t̄`.
    have hres : residueRingHom J (awayCompletionIdeal J g) (awayCompletionHom J g)
        (le_comap_awayCompletionHom J g) (Ideal.Quotient.mk J t) = 0 := by
      rw [residueRingHom, Ideal.quotientMap_mk]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hvan g hg)
    -- Transport along the residue equivalence: the chart's level-`0` ring is `(S⧸J)_{ḡ}`.
    have hcong := RingHom.congr_fun (awayCompletionResidueEquiv_comp_residueRingHom J g hJ)
      (Ideal.Quotient.mk J t)
    rw [RingHom.comp_apply, hres, map_zero] at hcong
    exact hcong.symm
  -- Injectivity of `S⧸J → ∏ (S⧸J)_{ḡ}` along the spanning family finishes it.
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  refine Localization.algebraMap_injective_of_span_eq_top _ hspan ?_
  rw [map_zero]
  funext b
  obtain ⟨g, hg, hgb⟩ := b.2
  change algebraMap (S ⧸ J) (Localization.Away b.1) (Ideal.Quotient.mk J t) = 0
  rw [← hgb]
  exact hloc g hg

end FormalSpectrum

end
