import FormalSchemes.StructureSheafStalkComparison
import FormalSchemes.BasicOpenRestrictionIdentification

set_option linter.style.header false

/-!
# `IsStalkLimit` with the structure sheaf gone from both halves

`FormalSchemes.StructureSheafStalkComparison` reduces `FormalSpectrum.IsStalkLimit I x` — the stalk
half of EGA I 10.8 at a point `x` of `Spf (R, I)` — to a conjunction of two statements, an
injectivity one and a surjectivity one (`FormalSpectrum.isStalkLimit_iff_awayCompletion`). The
surjectivity half is free of the structure sheaf outright: it names only completed localizations,
the map between them and the topology of `Spf R`. **The injectivity half is not.** It names
`FormalSpectrum.basicOpenRes`, which `FormalSchemes.BasicOpenRestriction` *defines* as the
restriction `Γ(D(f), O_{Spf R}) ⟶ Γ(D(e), O_{Spf R})` conjugated by
`FormalSpectrum.sectionsBasicOpenEquiv` on both sides, and inside that file's import closure nothing
pins it beyond the image of `R`.

This file removes it. `FormalSpectrum.basicOpenRes_eq_awayCompletionRestrict`
(`FormalSchemes.BasicOpenRestrictionIdentification`) says that for `I` finitely generated the
sheaf-theoretic restriction *is* the algebraically constructed
`FormalSpectrum.awayCompletionRestrict` (`FormalSchemes.AwayCompletionRestrict`), and `Ideal.FG` is
a hypothesis the criterion already carries. So the substitution is a rewrite, and after it **both
halves of the right-hand side** of `FormalSpectrum.isStalkLimit_iff_awayCompletionRestrict` mention
no sheaf, stalk, germ, colimit or category at all. The left-hand side is
`FormalSpectrum.IsStalkLimit` itself, which `FormalSchemes.StructureSheafStalks` defines as `IsIso`
of `FormalSpectrum.stalkToLimit`; that is the notion being reformulated rather than part of the
reformulation, and it stays sheaf-theoretic.

## What the rewrite costs

Two things, both of which are the reason it was not taken where the criterion was first stated.

**Ten modules.** `FormalSchemes.BasicOpenRestrictionIdentification` is not in the import closure of
`FormalSchemes.StructureSheafStalkComparison`, and adding it takes a closure of 35 to one of 45.

**Two instance hypotheses.** `FormalSpectrum.basicOpenRes_eq_awayCompletionRestrict` carries
`[TopologicalSpace R]` and `IsAdicRing I`, so the statements below carry them too — even though,
`FormalSpectrum.awayCompletionRestrict` being instance-free, nothing in what they say mentions
either. `FormalSchemes.StructureSheafStalkComparison` needs neither and says so; that is why the
substitution is made here, in a leaf, rather than there.

## The two instance hypotheses are *not* spurious

`FormalSchemes.BasicOpenRestrictionIdentification` contains no `omit`, so the natural suspicion is
that its `Sheaf` section carries the two instances only as section-variable residue. It does not,
and the reason is one declaration:

**`FormalSpectrum.globalSectionsEquiv` (`FormalSchemes.Sections`) genuinely takes
`[TopologicalSpace R]` and `IsAdicRing I`.** It is the identification `Γ(⊤, O_{Spf R}) ≃+* R`,
which is a statement about an adic ring and false without one. It occurs in the *statement* of
`FormalSpectrum.awayCompletionHom_eq_restrict` (`FormalSchemes.SpfGammaSheafComponentArbComp`), and
`FormalSpectrum.basicOpenRes_comp_awayCompletionHom` — whose own statement is instance-free — is
proved by rewriting with it twice. `FormalSpectrum.basicOpenRes_eq_awayCompletionRestrict` is that
square fed to `FormalSpectrum.eq_awayCompletionRestrict_of_comp_awayCompletionHom`, which is itself
instance-free.

This was settled by trying, not by reading: `omit [TopologicalSpace R] [IsAdicRing I] in` was placed
in front of each of the three declarations in turn and each attempt fails —
`awayCompletionHom_eq_restrict` with *cannot omit referenced section variable*, singly for either
instance as well as for both, and the other two with *failed to synthesize instance* at exactly the
rewrite that consumes the one below it. So the answer to "which declaration needs which instance" is
that `globalSectionsEquiv` needs both and the other three inherit them, and the signature weakening
that would make the results below hypothesis-free does not exist as a signature change. What is
*not* settled, and is a separate question with a separate answer, is whether
`basicOpenRes_comp_awayCompletionHom` — an instance-free statement — admits an instance-free
*proof* not routed through `Γ(⊤)`; nothing here attempts one, and its module has reverse closure 9.

## Placement, and the two options not taken

A new leaf, importing `FormalSchemes.StructureSheafStalkComparison` and
`FormalSchemes.BasicOpenRestrictionIdentification`: forward closure 46, reverse closure 0, so
nothing else on the tree rebuilds for it.

*Editing `FormalSchemes.StructureSheafStalkComparison` in place* was the obvious alternative and
costs the most: it would take that file's closure from 35 to 45 and put `[TopologicalSpace R]` and
`IsAdicRing I` into a module that today has neither and says so, for every consumer of the
sheaf-carrying criterion as well.

*Adding this to `FormalSchemes.StructureSheafStalkBasicOpenCompletion`* was the near miss. That file
already imports `FormalSchemes.BasicOpenRestrictionIdentification` and already makes the same trade
one level down, for the separation statement on sections
(`FormalSpectrum.exists_basicOpen_awayCompletionRestrict_eq`), recording the same two instance
hypotheses as a cost. Its reverse closure is 0 too, and importing
`FormalSchemes.StructureSheafStalkComparison` would take its closure from 42 to 46 — the same total
as this leaf. The two are equal on the numbers; the split is by subject, since that file is about
the *source* of the comparison map and these statements are about the map itself.

## Main results

* `FormalSpectrum.exists_basicOpenRes_eq_zero_iff_awayCompletionRestrict`: the vanishing condition
  the injectivity half asks for is the same condition with `FormalSpectrum.awayCompletionRestrict`
  in place of `FormalSpectrum.basicOpenRes`.
* `FormalSpectrum.injective_stalkToAdicCompletion_iff_awayCompletionRestrict`: **the injectivity
  half with no sheaf in it.**
* `FormalSpectrum.isStalkLimit_iff_awayCompletionRestrict`: `FormalSpectrum.IsStalkLimit` as two
  statements about completed localizations, neither of which mentions the structure sheaf.

## What is *not* proved here

**Whether `FormalSpectrum.IsStalkLimit` holds.** It is undecided on this tree in both directions,
and this file decides neither half of it. This is a *second* reformulation of the same undecided
question — the first being `FormalSpectrum.isStalkLimit_iff_awayCompletion` — and not progress on
the answer. Both sides of every `Iff` below are undecided, and no argument below is about either.

**The obstruction is untouched.** `FormalSchemes.StructureSheafStalkComparison` records it and it
stands exactly as recorded: `Localization.AtPrime (pointPrime I x)` is a filtered colimit over
`g ∉ p`, so an element killed by `FormalSpectrum.awayToAtPrimeCompletion` is killed at each level
`n` separately by a `g` that may depend on `n`, and the injectivity half asks for one `g` serving
every level. Replacing `FormalSpectrum.basicOpenRes` by `FormalSpectrum.awayCompletionRestrict`
changes nothing about that; it makes the statement algebraic, which is what an attempt on it needs,
and it makes it no easier.

**Nothing under a Noetherian hypothesis.** `Ideal.FG` of the ideal of definition is the only
finiteness assumption below, and it is inherited from the statements being rewritten.

**No new identification of the restriction.** Everything here is
`FormalSpectrum.basicOpenRes_eq_awayCompletionRestrict` applied; that identification is proved where
it is stated and is not reproved, weakened or generalised here.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable (x : FormalSpectrum I)

/-- **The vanishing condition of the injectivity half, with the sheaf removed.** For `I` finitely
generated, an element of `R{1/f}` is killed by the structure-sheaf restriction to some smaller basic
open through `x` exactly when it is killed by `FormalSpectrum.awayCompletionRestrict` to some such
open — indeed by the same one, since the two maps are equal
(`FormalSpectrum.basicOpenRes_eq_awayCompletionRestrict`).

Stated separately from the two `Iff`s below because it is the whole of their content: they are this
lemma transported along `FormalSpectrum.injective_stalkToAdicCompletion_iff` and
`FormalSpectrum.isStalkLimit_iff_awayCompletion`. -/
theorem exists_basicOpenRes_eq_zero_iff_awayCompletionRestrict (hI : I.FG) {f : R}
    (a : awayCompletion I f) :
    (∃ (e : R) (_ : x ∈ basicOpen I e) (hle : basicOpen I e ≤ basicOpen I f),
        basicOpenRes I hle a = 0) ↔
      ∃ (e : R) (_ : x ∈ basicOpen I e) (hle : basicOpen I e ≤ basicOpen I f),
        awayCompletionRestrict I f e hI hle a = 0 := by
  constructor
  · rintro ⟨e, hxe, hle, hres⟩
    exact ⟨e, hxe, hle, by rwa [← basicOpenRes_eq_awayCompletionRestrict I hI hle]⟩
  · rintro ⟨e, hxe, hle, hres⟩
    exact ⟨e, hxe, hle, by rwa [basicOpenRes_eq_awayCompletionRestrict I hI hle]⟩

/-- **The injectivity half of `FormalSpectrum.IsStalkLimit`, with no sheaf in it.** The comparison
map `FormalSpectrum.stalkToAdicCompletion` is injective exactly when an element of `R{1/f}` killed
by the completed localization map `FormalSpectrum.awayToAtPrimeCompletion` at `x` is already killed
by the canonical `R{1/f} →+* R{1/e}` of some smaller basic open through `x`.

This is `FormalSpectrum.injective_stalkToAdicCompletion_iff` with
`FormalSpectrum.exists_basicOpenRes_eq_zero_iff_awayCompletionRestrict` applied to its right-hand
side. Every name occurring in that right-hand side — `FormalSpectrum.awayCompletion`,
`FormalSpectrum.awayToAtPrimeCompletion`, `FormalSpectrum.awayCompletionRestrict` and
`FormalSpectrum.basicOpen` — is a localization, an adic completion, a map between such, or the
topology of `Spf R`.

Both sides are undecided. -/
theorem injective_stalkToAdicCompletion_iff_awayCompletionRestrict (hI : I.FG) :
    Function.Injective (stalkToAdicCompletion I x) ↔
      ∀ (f : R) (hf : x ∈ basicOpen I f) (a : awayCompletion I f),
        awayToAtPrimeCompletion I x hI hf a = 0 →
          ∃ (e : R) (_ : x ∈ basicOpen I e) (hle : basicOpen I e ≤ basicOpen I f),
            awayCompletionRestrict I f e hI hle a = 0 := by
  rw [injective_stalkToAdicCompletion_iff I x hI]
  exact forall_congr' fun f => forall_congr' fun _ => forall_congr' fun a =>
    imp_congr_right fun _ => exists_basicOpenRes_eq_zero_iff_awayCompletionRestrict I x hI a

/-- **`FormalSpectrum.IsStalkLimit` as two statements about completed localizations.** The stalk
half of EGA I 10.8 at `x` holds exactly when the injectivity condition of
`FormalSpectrum.injective_stalkToAdicCompletion_iff_awayCompletionRestrict` and the surjectivity
condition of `FormalSpectrum.surjective_stalkToAdicCompletion_iff` both hold. Neither mentions the
structure sheaf, a stalk, a germ, a colimit or a category: this is
`FormalSpectrum.isStalkLimit_iff_awayCompletion` with the last sheaf-theoretic name removed from it.

**It is a reformulation and not an answer.** Both sides are undecided on this tree, in both
directions, and the module docstring records the obstruction — the smaller basic open produced at
each level need not be independent of the level — which this restatement does not address. -/
theorem isStalkLimit_iff_awayCompletionRestrict (hI : I.FG) :
    IsStalkLimit I x ↔
      (∀ (f : R) (hf : x ∈ basicOpen I f) (a : awayCompletion I f),
          awayToAtPrimeCompletion I x hI hf a = 0 →
            ∃ (e : R) (_ : x ∈ basicOpen I e) (hle : basicOpen I e ≤ basicOpen I f),
              awayCompletionRestrict I f e hI hle a = 0) ∧
        ∀ b : AdicCompletion (pointIdeal I x) (Localization.AtPrime (pointPrime I x)),
          ∃ (f : R) (hf : x ∈ basicOpen I f) (a : awayCompletion I f),
            awayToAtPrimeCompletion I x hI hf a = b := by
  rw [isStalkLimit_iff_bijective_stalkToAdicCompletion, Function.Bijective,
    injective_stalkToAdicCompletion_iff_awayCompletionRestrict I x hI,
    surjective_stalkToAdicCompletion_iff I x hI]

end FormalSpectrum
