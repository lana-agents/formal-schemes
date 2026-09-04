import FormalSchemes.CompletionToSpecStalk
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Rat.Encodable

set_option linter.style.header false

/-!
# `X_{/Y} ⟶ X` is **not** a closed immersion: the question, decided

`FormalSchemes.CompletionToSpecStalk` poses `formalCompletion.IsClosedImmersionToSpec` — a closed
topological embedding of the base together with surjectivity of every stalk map — and records that
its topological half is already a theorem, so that all of its content is the stalk half. It leaves
the stalk half undecided. This file decides it: **it fails**, and it already fails for `ℚ[X]`
completed at `(X)`.

The refutation is a **cardinality** argument, and that is the whole of it. Surjectivity of the
stalk map at a point `x` makes the stalk of the completion a quotient of the stalk of `Spec R` at
the image point. When `R` is countable that source stalk is countable, because it is a localization
of `R` (`AlgebraicGeometry.StructureSheaf.stalkIso`). When the ideal is **maximal** the completion
has a one-point underlying space, so its global sections inject into the stalk at that point, and
its global sections are the completion itself (`FormalSpectrum.globalSectionsEquiv`). A completion
that is uncountable therefore cannot be a quotient of a countable ring. The witness family is
`MvPolynomial σ k` completed at `MvPolynomial.idealOfVars σ k`, whose completion Mathlib identifies
with `MvPowerSeries σ k` (`MvPowerSeries.toAdicCompletionAlgEquiv`): countably many polynomials,
uncountably many power series.

**This file does not use `formalCompletion.toStalk_comp_stalkMap_toSpec`**, the reduction that
`FormalSchemes.CompletionToSpecStalk` lands. That reduction computes the stalk map on the image of
`AlgebraicGeometry.StructureSheaf.toStalk`, and it is what a *positive* result or a characterisation
would be proved against; a cardinality argument never has to identify the map, only its source and
its target, so it is deliberately not used here. The two are complementary and neither supersedes
the other.

## Main results

* `formalCompletion.not_isClosedImmersionToSpec_of_countable_of_uncountable`: **the criterion.**
  For `I` maximal and finitely generated in a countable `R` whose `I`-adic completion is
  uncountable, `formalCompletion.IsClosedImmersionToSpec` fails.
* `formalCompletion.not_isClosedImmersionToSpec_mvPolynomial`: **the witness family.** It fails for
  `MvPolynomial σ k` at `MvPolynomial.idealOfVars σ k`, for every finite nonempty `σ` and every
  countable field `k`.
* `formalCompletion.not_isClosedImmersionToSpec_ratMvPolynomial`: the same at `σ = Fin 1`, `k = ℚ`
  — the one-variable statement `ℚ[X] ⟶ ℚ[[X]]`, with no hypotheses at all.
* `formalCompletion.not_forall_isClosedImmersionToSpec`: **the headline.** There is no theorem
  saying `formalCompletion.toSpec` is always a closed immersion.

Supporting statements that mention no formal scheme are stated in the namespace they belong to:
`AlgebraicGeometry.LocallyRingedSpace.injective_Γgerm_of_subsingleton`,
`Localization.countable_of_countable`, `MvPolynomial.ker_constantCoeff`,
`MvPolynomial.isMaximal_idealOfVars`, `MvPolynomial.countable_of_countable`,
`MvPowerSeries.uncountable_of_nonempty` and
`MvPolynomial.uncountable_adicCompletion_idealOfVars`.

## What is *not* proved here

**The characterisation.** The expected general statement is that the stalk maps are surjective
exactly when the relevant local rings of `R` are already adically complete, and that the closed
immersion is the degenerate case rather than the general one. Nothing here proves either direction
of that, and in particular **nothing here says the answer is always no**: the question is not
refuted for every `R` and `I`, only for the witnesses below, which is what
`formalCompletion.not_forall_isClosedImmersionToSpec` claims and all it claims. The degenerate cases
where it does hold — `I` nilpotent, `R` already complete — are untouched.

**Anything about `ℤ` at `(2)`**, the obvious arithmetic witness — `ℤ_(2) ⟶ ℤ₂` is the same
phenomenon and is not what is proved. The criterion below applies to it the
moment someone proves `AdicCompletion (Ideal.span {(2 : ℤ)}) ℤ` uncountable — `ℤ` is countable and
`Ideal.span {(2 : ℤ)}` is maximal and finitely generated — but that uncountability is not on this
tree, and Mathlib carries no equivalence between that completion and its own `p`-adic integers,
which is where the count would otherwise come from. The power-series
witnesses are used precisely because Mathlib does have the corresponding equivalence for them.

**The positive stalk half of EGA I 10.8** — that the stalk of the completion is the completion of
the stalk — and the universal property of the completion. A reader who learns here that
`formalCompletion.toSpec` is not a closed immersion should not conclude that 10.8 has no
stalk-level content; that theorem is untouched and is the larger piece of work.

**Anything at a glued index.** This is the affine morphism `formalCompletion.toSpec` only. The
two-patch and arbitrary-index closed-immersion questions are still not written down anywhere.

## Implementation notes

The countability and uncountability statements are `theorem`s and not `instance`s, and are
activated where they are used with `haveI`. `Countable` and `Uncountable` are searched by every
elaboration in the file's reverse closure, and none of these is a fact anything else here wants.
`FormalSchemes.TwoAdicDegeneracy` gives the same reason for keeping its `Int` maximality statement
out of the instance graph.

`MvPolynomial.ker_constantCoeff` and `MvPolynomial.isMaximal_idealOfVars` say nothing about formal
schemes and would sit happily in Mathlib beside `MvPolynomial.idealOfVars_fg`. They are here rather
than earlier in this tree's import order because they have exactly one consumer, which is the
witness below; a second consumer is the reason to rehome them.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

/-- **On a one-point space the global sections inject into the stalk.** The opens containing `x`
are then just `⊤`, so two global sections with the same germ at `x` agree on a neighbourhood of
every point of `⊤` and the sheaf condition (`TopCat.Presheaf.section_ext`) identifies them.

This is what turns a bound on the stalk into a bound on the ring of global sections, and it is the
only place the one-point hypothesis of
`formalCompletion.not_isClosedImmersionToSpec_of_countable_of_uncountable` is used. -/
theorem injective_Γgerm_of_subsingleton (X : LocallyRingedSpace.{u}) (hX : Subsingleton X)
    (x : X) : Function.Injective ⇑(X.presheaf.Γgerm x).hom := by
  intro s t h
  refine TopCat.Presheaf.section_ext X.toSheafedSpace.sheaf ⊤ s t ?_
  intro y hy
  have hyx : y = x := hX.elim y x
  subst hyx
  exact h

end AlgebraicGeometry.LocallyRingedSpace

namespace Localization

/-- **A localization of a countable ring is countable**: every element is `Localization.mk r s`,
so `R × M` surjects onto it. -/
theorem countable_of_countable {A : Type u} [CommRing A] [Countable A] (M : Submonoid A) :
    Countable (Localization M) := by
  refine Function.Surjective.countable (f := fun q : A × M => Localization.mk q.1 q.2) ?_
  intro z
  induction z using Localization.ind with
  | _ q => exact ⟨(q.1, q.2), rfl⟩

end Localization

namespace MvPolynomial

/-- **`MvPolynomial.idealOfVars` is the kernel of `MvPolynomial.constantCoeff`.** By
`MvPolynomial.mem_pow_idealOfVars_iff'` at `n = 1`, membership says every exponent of total degree
`< 1` has zero coefficient, and `Finsupp.degree_eq_zero_iff` says the only such exponent is `0`. -/
theorem ker_constantCoeff (σ : Type u) [Finite σ] (k : Type u) [CommRing k] :
    RingHom.ker (constantCoeff : MvPolynomial σ k →+* k) = idealOfVars σ k := by
  ext p
  rw [RingHom.mem_ker, show idealOfVars σ k = idealOfVars σ k ^ 1 by ring,
    MvPolynomial.mem_pow_idealOfVars_iff', constantCoeff_eq]
  constructor
  · intro h x hx
    rw [Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] at hx
    subst hx
    exact h
  · intro h
    exact h 0 (by simp [Finsupp.degree])

/-- **Over a field the ideal spanned by the variables is maximal.** It is the kernel of
`MvPolynomial.constantCoeff` by `MvPolynomial.ker_constantCoeff`, and that map is onto `k` because
`MvPolynomial.C` sections it. -/
theorem isMaximal_idealOfVars (σ : Type u) [Finite σ] (k : Type u) [Field k] :
    (idealOfVars σ k).IsMaximal := by
  rw [← ker_constantCoeff]
  exact RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, by simp⟩

/-- **A polynomial ring over a countable ring in countably many variables is countable.** A
polynomial is its `AddMonoidAlgebra.coeff`, a finitely supported function on the exponents. -/
theorem countable_of_countable (σ : Type u) [Countable σ] (k : Type u) [CommRing k] [Countable k] :
    Countable (MvPolynomial σ k) :=
  Function.Injective.countable (f := AddMonoidAlgebra.coeff)
    fun a b h => by cases a; cases b; simpa using h

end MvPolynomial

namespace MvPowerSeries

/-- **A power series ring in at least one variable over a nontrivial ring is uncountable.**
`MvPowerSeries σ k` is the type of functions from the exponents to `k`, the exponents `σ →₀ ℕ` are
infinite once `σ` is nonempty, and `Cardinal.cantor'` bounds `ℵ₀` below `#k ^ #(σ →₀ ℕ)`. -/
theorem uncountable_of_nonempty (σ : Type u) [Nonempty σ] (k : Type u) [CommRing k]
    [Nontrivial k] : Uncountable (MvPowerSeries σ k) := by
  have h : Uncountable ((σ →₀ ℕ) → k) := by
    rw [← Cardinal.aleph0_lt_mk_iff, Cardinal.mk_arrow]
    simp only [Cardinal.lift_id]
    exact lt_of_le_of_lt (Cardinal.aleph0_le_mk (σ →₀ ℕ))
      (Cardinal.cantor' _ (Cardinal.one_lt_iff_nontrivial.2 ‹Nontrivial k›))
  exact h

end MvPowerSeries

namespace MvPolynomial

/-- **The completion of a polynomial ring at the variables is uncountable**, in at least one
variable and over a nontrivial ring. `MvPowerSeries.toAdicCompletionAlgEquiv` identifies that
completion with the power series ring, which `MvPowerSeries.uncountable_of_nonempty` counts. -/
theorem uncountable_adicCompletion_idealOfVars (σ : Type u) [Finite σ] [Nonempty σ] (k : Type u)
    [CommRing k] [Nontrivial k] :
    Uncountable (AdicCompletion (idealOfVars σ k) (MvPolynomial σ k)) :=
  haveI := MvPowerSeries.uncountable_of_nonempty σ k
  Uncountable.of_equiv _ (MvPowerSeries.toAdicCompletionAlgEquiv σ k).toEquiv

end MvPolynomial

namespace formalCompletion

variable (R : Type u) [CommRing R] (I : Ideal R)

/-! ### The one-point index -/

/-- **At a maximal ideal the completion has at most one point.** `FormalSpectrum` of the ideal of
definition is by definition the prime spectrum of `R^ ⧸ AdicCompletion.idealOfDefinition I`,
`AdicCompletion.quotientEquiv` identifies that residue ring with `R ⧸ I`, and for `I` maximal that
is a field, which has a unique prime.

`FormalSpectrum.subsingleton_twoAdic` (`FormalSchemes.TwoAdicDegeneracy`) is this statement at
`R = ℤ`, `I = (2)`, proved by this route before the general form existed — checked by deriving it
from this lemma, not by reading it. It is **not** replaced here: this file is downstream of it, so
removing the duplicate would mean rehoming the general form to sit before
`FormalSchemes.TwoAdicWitness` in the import order, which is a dedup question and not this
file's. -/
theorem subsingleton_formalSpectrum_of_isMaximal (hI : I.FG) [I.IsMaximal] :
    Subsingleton (FormalSpectrum (AdicCompletion.idealOfDefinition I)) := by
  letI : Field (R ⧸ I) := Ideal.Quotient.field _
  exact (PrimeSpectrum.comapEquiv (AdicCompletion.quotientEquiv I hI)).toEquiv.subsingleton

/-! ### The criterion -/

/-- **The closed-immersion question fails whenever the completion is too big to be a quotient of
`R`.** Precisely: for `I` maximal and finitely generated in a **countable** `R` whose `I`-adic
completion is **uncountable**, `formalCompletion.IsClosedImmersionToSpec` is false.

The topological half is unaffected — it is a theorem
(`formalCompletion.isClosedEmbedding_toSpec_base`) — so what fails is the stalk half, which is all
of the content by `formalCompletion.isClosedImmersionToSpec_iff_surjective_stalkMap`.

The argument is a count at the one point of `Spf R^`, which exists by
`formalCompletion.nonempty_formalSpectrum_of_ne_top` and is unique by
`formalCompletion.subsingleton_formalSpectrum_of_isMaximal`:

* the stalk of `Spec R` at its image is a localization of `R`
  (`AlgebraicGeometry.StructureSheaf.stalkIso`), hence countable;
* a surjection carries that to the stalk of `Spf R^`, which would then be countable;
* but the global sections of `Spf R^` are `AdicCompletion I R`
  (`FormalSpectrum.globalSectionsEquiv`) and they inject into that stalk
  (`AlgebraicGeometry.LocallyRingedSpace.injective_Γgerm_of_subsingleton`), so it is uncountable.

Maximality is used only to make the space a point, and countability only to make the source stalk
small; neither is claimed to be necessary. -/
theorem not_isClosedImmersionToSpec_of_countable_of_uncountable [Countable R] (hI : I.FG)
    [hmax : I.IsMaximal] (hunc : Uncountable (AdicCompletion I R)) :
    ¬ IsClosedImmersionToSpec R I hI := by
  intro h
  haveI := AdicCompletion.isAdicRing_map I hI
  obtain ⟨x⟩ := nonempty_formalSpectrum_of_ne_top R I hI hmax.ne_top
  haveI : Countable ((Spec.locallyRingedSpaceObj (CommRingCat.of R)).presheaf.stalk
      ((toSpec R I hI).base x)) :=
    haveI := Localization.countable_of_countable ((toSpec R I hI).base x).asIdeal.primeCompl
    Countable.of_equiv _ (StructureSheaf.stalkIso R ((toSpec R I hI).base x)).toEquiv
  haveI hstalk : Countable ((formalCompletion R I hI).toLocallyRingedSpace.presheaf.stalk x) :=
    Function.Surjective.countable (h.2 x)
  haveI : Uncountable ((formalCompletion R I hI).toLocallyRingedSpace.presheaf.obj (op ⊤)) :=
    Uncountable.of_equiv _
      (FormalSpectrum.globalSectionsEquiv (AdicCompletion.idealOfDefinition I)).symm.toEquiv
  exact (Function.Injective.uncountable
    (LocallyRingedSpace.injective_Γgerm_of_subsingleton
      (formalCompletion R I hI).toLocallyRingedSpace
      (subsingleton_formalSpectrum_of_isMaximal R I hI) x)).not_countable hstalk

/-! ### The witnesses -/

/-- **`Spf k[[σ]] ⟶ Spec k[σ]` is not a closed immersion**, for any finite nonempty `σ` and any
countable field `k`. The ideal is `MvPolynomial.idealOfVars σ k`, maximal by
`MvPolynomial.isMaximal_idealOfVars` and finitely generated by `MvPolynomial.idealOfVars_fg`; the
ring is countable by `MvPolynomial.countable_of_countable` and its completion uncountable by
`MvPolynomial.uncountable_adicCompletion_idealOfVars`.

Read on elements: the stalk of `Spec k[σ]` at the variables is a localization of `k[σ]`, so it has
only countably many elements, while `k[[σ]]` has uncountably many. No map at all — ring map or
otherwise — is onto, so the completion adds power series that the fractions of polynomials
available at that point do not reach. Which power series those are is not identified here, and the
argument does not produce one. -/
theorem not_isClosedImmersionToSpec_mvPolynomial (σ : Type u) [Finite σ] [Nonempty σ] (k : Type u)
    [Field k] [Countable k] :
    ¬ IsClosedImmersionToSpec (MvPolynomial σ k) (MvPolynomial.idealOfVars σ k)
      (MvPolynomial.idealOfVars_fg σ k) :=
  haveI := MvPolynomial.countable_of_countable σ k
  haveI := MvPolynomial.isMaximal_idealOfVars σ k
  not_isClosedImmersionToSpec_of_countable_of_uncountable _ _ _
    (MvPolynomial.uncountable_adicCompletion_idealOfVars σ k)

/-- **The one-variable rational witness, with no hypotheses at all**: `ℚ[X]` completed at `(X)` is
`ℚ[[X]]`, and `Spf ℚ[[X]] ⟶ Spec ℚ[X]` is not a closed immersion. This is
`formalCompletion.not_isClosedImmersionToSpec_mvPolynomial` at `σ = Fin 1` and `k = ℚ`. -/
theorem not_isClosedImmersionToSpec_ratMvPolynomial :
    ¬ IsClosedImmersionToSpec (MvPolynomial (Fin 1) ℚ) (MvPolynomial.idealOfVars (Fin 1) ℚ)
      (MvPolynomial.idealOfVars_fg (Fin 1) ℚ) :=
  not_isClosedImmersionToSpec_mvPolynomial (Fin 1) ℚ

/-- **The answer to the question `FormalSchemes.CompletionToSpecStalk` poses: no.** There is no
theorem saying `formalCompletion.toSpec` is a closed immersion, because
`formalCompletion.not_isClosedImmersionToSpec_ratMvPolynomial` is a counterexample.

This is the *general* statement being refuted, not every instance of it: the question does hold in
degenerate cases, and this file decides none of them. It quantifies over `Type` rather than
`Type u` because that is where the witness lives; nothing here is universe-polymorphic in the
witness, and a `Type u` form would need a `ULift`. -/
theorem not_forall_isClosedImmersionToSpec :
    ¬ ∀ (S : Type) [CommRing S] (J : Ideal S) (hJ : J.FG), IsClosedImmersionToSpec S J hJ :=
  fun h => not_isClosedImmersionToSpec_ratMvPolynomial (h _ _ _)

end formalCompletion
