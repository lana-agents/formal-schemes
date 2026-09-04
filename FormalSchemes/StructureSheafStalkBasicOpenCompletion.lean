import FormalSchemes.StructureSheafStalkBasicOpen
import FormalSchemes.BasicOpenRestrictionIdentification

set_option linter.style.header false

/-!
# The separation half of the stalk description, as an equation in a completed localization

`FormalSchemes.StructureSheafStalkBasicOpen` states the two facts a colimit description of the
stalk of `O_{Spf R}` at `x` exists in order to provide. Its separation half,
`FormalSpectrum.exists_basicOpen_res_eq`, is stated **on sections**: two sections over basic opens
with the same germ at `x` agree after `(structureSheaf I).presheaf.map` of a smaller basic open's
inclusion. Its surjectivity half, `FormalSpectrum.exists_adicCompletion_germ_eq`, is already stated
on `AdicCompletion (I · R_f) R_f`, because it needs only
`FormalSpectrum.sectionsBasicOpenEquiv` and no map between two different basic opens.

That asymmetry was forced, and that file said so: the restriction between two basic opens was
identified with no computed map of adic completions. It is now —
`FormalSpectrum.basicOpenRes_eq_awayCompletionRestrict`
(`FormalSchemes.BasicOpenRestrictionIdentification`) — so the separation half can be stated the same
way as the surjectivity half, and this file states it.

## Main results

* `FormalSpectrum.exists_basicOpen_basicOpenRes_eq`: two elements of `R{1/f}` and `R{1/g}` whose
  germs at `x` agree are carried to the same element of `R{1/e}` by
  `FormalSpectrum.basicOpenRes` (`FormalSchemes.BasicOpenRestriction`), for some basic `D(e) ∋ x`
  inside both. Its hypotheses are exactly those of the sections form it upgrades: **no `Ideal.FG`,
  no `IsAdicRing`, no topology on `R`.**
* `FormalSpectrum.exists_basicOpen_awayCompletionRestrict_eq`: the same equation for
  `FormalSpectrum.awayCompletionRestrict` (`FormalSchemes.AwayCompletionRestrict`), the map built
  from the algebra of the localizations. This one needs `hI : I.FG`, because its right-hand side
  does not exist without it — `AdicCompletion.mapCompletion` (`FormalSchemes.Completion`) asks for a
  finitely generated ideal — and it needs `[TopologicalSpace R] [IsAdicRing I]`, which the
  identification it rewrites along carries even though neither of the two maps it equates does.

Both are `∃`-statements over an `e : R`, exactly as
`FormalSpectrum.exists_basicOpen_res_eq` is, and both take their `e` from it.

## What is *not* proved here

**Anything about `FormalSpectrum.IsStalkLimit`.** That question — whether the comparison
`O_{Spf R, x} ⟶ lim_n O_{X_n, x}` of `FormalSchemes.StructureSheafStalks` is an isomorphism — is
undecided in both directions and nothing below bears on it. Restating the separation half over
completed localizations describes the *source* of that comparison in the same terms its target is
already described in; it is an input to a future decision, not a partial one. Nothing below mentions
it.

**The sections form is not replaced.** `FormalSpectrum.exists_basicOpen_res_eq` stays where it is
and keeps its hypotheses. The first statement below matches them exactly and the second adds
`Ideal.FG`, a topology and `IsAdicRing`; this file adds, it does not migrate.

**The colimit is still not formed**, and the finality result that would let
`CategoryTheory.Functor.Final.colimitIso` form it is still the negative search result recorded by
`FormalSchemes.StructureSheafStalkBasicOpen`, not a theorem.

**The germ hypothesis is not restated in completion terms.** It is still an equation between two
germs of *sections*, with the two elements pushed into sections by
`FormalSpectrum.sectionsBasicOpenEquiv`, because the stalk is a stalk of the structure sheaf and
there is no completion-side object for a germ to live in. Only the conclusion changes.

## Implementation notes

**This is a separate leaf rather than an addition to
`FormalSchemes.StructureSheafStalkBasicOpen`, and the reason is measured.** That file's transitive
project-import closure is **7** modules; `FormalSchemes.BasicOpenRestrictionIdentification`'s is
**40**, and it does not contain that file, so the union is **41**. Adding the import there would
raise a file of elementary basis-and-germ facts from 7 modules to 41 for the sake of the two
statements below. That file already refused the same trade once, in its implementation notes, for
`FormalSchemes.SpfGammaRoundTrip` at 32 modules; refusing it again at 41 is the consistent call. Its
reverse closure is 0, so nothing downstream pays for either choice — the cost is entirely the
closure of the file itself.

The proofs are the route the follow-up row set out and nothing more: take `e` and the two
inclusions from `FormalSpectrum.exists_basicOpen_res_eq` applied to the two elements pushed into
sections, then observe that `FormalSpectrum.basicOpenRes` is *definitionally*
`sectionsBasicOpenEquiv I e ∘ presheaf.map (homOfLE _).op ∘ (sectionsBasicOpenEquiv I f).symm`, so
its two values are the two sides of that conclusion with `sectionsBasicOpenEquiv I e` applied. No
level-wise computation, no `AdicCompletion.ext_evalₐ`, and the identification enters only in the
last rewrite of the second statement.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1 and §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory TopCat AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R) [TopologicalSpace R] [IsAdicRing I]

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The separation half of the stalk description, as an equation in a completed localization.**
Two elements `a ∈ R{1/f}` and `b ∈ R{1/g}` whose germs at `x` agree — read into sections by
`FormalSpectrum.sectionsBasicOpenEquiv` — already have the same restriction to some basic open
`D(e) ∋ x` contained in both, where the restriction is the structure-sheaf map
`FormalSpectrum.basicOpenRes` (`FormalSchemes.BasicOpenRestriction`).

This is `FormalSpectrum.exists_basicOpen_res_eq`
(`FormalSchemes.StructureSheafStalkBasicOpen`) with both sides read through
`sectionsBasicOpenEquiv`; `basicOpenRes` is by definition that conjugation, so the two conclusions
differ by unfolding one definition and one `congrArg`. Its hypotheses are exactly those of the
sections form: no `Ideal.FG`, no `IsAdicRing`, not even a topology on `R`, since `basicOpenRes`
needs none of them. -/
theorem exists_basicOpen_basicOpenRes_eq (x : FormalSpectrum I) {f g : R}
    (hf : x ∈ basicOpen I f) (hg : x ∈ basicOpen I g)
    (a : awayCompletion I f) (b : awayCompletion I g)
    (h : ((structureSheaf I).presheaf.germ (basicOpen I f) x hf)
        ((sectionsBasicOpenEquiv I f).symm a) =
      ((structureSheaf I).presheaf.germ (basicOpen I g) x hg)
        ((sectionsBasicOpenEquiv I g).symm b)) :
    ∃ e : R, x ∈ basicOpen I e ∧ ∃ (hef : basicOpen I e ≤ basicOpen I f)
      (heg : basicOpen I e ≤ basicOpen I g),
      basicOpenRes I hef a = basicOpenRes I heg b := by
  obtain ⟨e, hxe, hef, heg, he⟩ := exists_basicOpen_res_eq I x hf hg _ _ h
  refine ⟨e, hxe, hef, heg, ?_⟩
  simp only [basicOpenRes, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom]
  exact congrArg _ he

/-- **The separation half against the canonical map of completed localizations.** The same
statement as `FormalSpectrum.exists_basicOpen_basicOpenRes_eq`, with the restriction named on the
algebraic side: `FormalSpectrum.awayCompletionRestrict` (`FormalSchemes.AwayCompletionRestrict`),
the map obtained by inverting `f` in the complete ring `R{1/e}`.

Together with `FormalSpectrum.exists_adicCompletion_germ_eq`
(`FormalSchemes.StructureSheafStalkBasicOpen`) this says the stalk is the filtered colimit of the
`AdicCompletion (I · R_f) R_f` over the basic opens through `x`, with **both** halves stated on the
completed localizations and their canonical maps rather than on sections of the structure sheaf.

The `Ideal.FG` hypothesis is not an artefact of the proof: `awayCompletionRestrict` does not exist
without it. `FormalSpectrum.exists_basicOpen_basicOpenRes_eq` is the same statement without it. -/
theorem exists_basicOpen_awayCompletionRestrict_eq (hI : I.FG) (x : FormalSpectrum I) {f g : R}
    (hf : x ∈ basicOpen I f) (hg : x ∈ basicOpen I g)
    (a : awayCompletion I f) (b : awayCompletion I g)
    (h : ((structureSheaf I).presheaf.germ (basicOpen I f) x hf)
        ((sectionsBasicOpenEquiv I f).symm a) =
      ((structureSheaf I).presheaf.germ (basicOpen I g) x hg)
        ((sectionsBasicOpenEquiv I g).symm b)) :
    ∃ e : R, x ∈ basicOpen I e ∧ ∃ (hef : basicOpen I e ≤ basicOpen I f)
      (heg : basicOpen I e ≤ basicOpen I g),
      awayCompletionRestrict I f e hI hef a = awayCompletionRestrict I g e hI heg b := by
  obtain ⟨e, hxe, hef, heg, he⟩ := exists_basicOpen_basicOpenRes_eq I x hf hg a b h
  refine ⟨e, hxe, hef, heg, ?_⟩
  rw [← basicOpenRes_eq_awayCompletionRestrict I hI hef,
    ← basicOpenRes_eq_awayCompletionRestrict I hI heg]
  exact he

end FormalSpectrum
