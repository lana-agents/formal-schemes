import FormalSchemes.AwayBaseChangeTopFiniteType
import FormalSchemes.AwayCompletionAlgHomBasicOpen
import FormalSchemes.AwayCompletionCongrEquiv
import FormalSchemes.AwayCompletionUniversal
import FormalSchemes.RefinedOverlapRestrict

set_option linter.style.header false

/-!
# The refined overlap's cross-chart transition

Refining an arbitrary affine chart family of a formal scheme by basic opens — the construction
statement (A) of EGA I §10.15 waits on, issue 2148 — indexes the refined charts by pairs *⟨i, h⟩*
with `h : A_i`, and at a cross-chart refined pair *⟨i, h⟩*, *⟨j, h'⟩* it needs an `R`-algebra
equivalence

```
A_i{1/(h · e_ij)}  ≃ₐ[R]  A_j{1/(h' · e_ji)}
```

between the two refined presentations of one overlap. Here `e_ij` is
`FormalSpectrum.refinedOverlapElt` (`FormalSchemes.RefinedOverlapRestrict`) at that pair and `e_ji`
is the same element with the two charts and the two refining elements swapped, and the equivalence
has to sit over the coarse transition `τ_ij : A_i{1/g_ij} ≃ₐ[R] A_j{1/g_ji}` the unrefined datum
already carries. `FormalSchemes.RefinedOverlapRestrict`'s `## What is **not** proved here` named
this as the one thing that file's legs stop short of. It is
`FormalSpectrum.refinedOverlapTransition` below, and its symmetry law — the transition at the
swapped refined pair being this one's inverse, which is `τ_symm` in the language of
`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData` — is
`FormalSpectrum.refinedOverlapTransition_symm` beside it.

**It is a composite of statements this tree already has, and it is not a descent statement.** That
distinction is the whole reason this module is short: the span

```
A_i{1/g_ij} ⟶ A_i{1/(h · e_ij)}        A_j{1/g_ji} ⟶ A_j{1/(h' · e_ji)}
```

of `FormalSpectrum.refinedOverlapLeg` joined at the top by *τ_ij* invites reading the bottom
equivalence as descent along the two legs, and nothing here does that. The route goes *up* instead:
each refined presentation is recognised as a basic open of its own coarse chart, *τ_ij* is
transported to that basic open, and the two presentations are matched by the element that cuts them
out.

## Main results

* `FormalSpectrum.basicOpen_awayCompletionAlgEquiv_mul_refinedOverlapElt`: the two refined
  presentations cut out corresponding opens — inside `Spf (A_j{1/g_ji})`, the *τ_ij*-image of the
  refined overlap read in chart *i* is the refined overlap read in chart *j*. This is the
  hypothesis the third step of the route below asks for, and it is the only statement here with
  content.
* `FormalSpectrum.refinedOverlapTransition`: the equivalence itself, as the composite of four
  declarations and two bookkeeping steps.
* `FormalSpectrum.refinedOverlapTransition_symm`: the transition at the swapped refined pair is
  this one's inverse, and `FormalSpectrum.refinedOverlapTransition_trans_symm` is the same fact
  read as a round trip. The section after next says why the pointwise route to this is the wrong
  one and what replaces it.
* `FormalSpectrum.refinedOverlapTransition_conj_symm`: the **refined datum's `τ_symm` field** —
  the symmetry law conjugated by the identification that presents each refined chart as a completed
  localization of the chart algebra above it, with that identification left arbitrary, and with the
  bridge that respells the swapped overlap element inside the composite.
  `FormalSpectrum.refinedOverlapTransition_bridge_trans_eq_refl` is its middle.
* `FormalSpectrum.awayCompletionAlgEquivOfBase_congr_trans_eq_refl`: the one statement with content
  in the proof of the symmetry law — base change along an `R`-algebra equivalence of chart
  algebras, a basic-open re-presentation, base change back, and a second re-presentation, compose
  to the identity.
* `AlgEquiv.trans_symm_of_middle_eq_refl`, `AlgEquiv.trans_trans_eq_refl_of_middle_eq_refl`,
  `AlgEquiv.symm_trans_symm_of_middle_eq_refl` and `AlgEquiv.trans_trans_eq_refl_of_bridges`: the
  bookkeeping that carries those two statements out to the transition and to the datum's field,
  stated for `AlgEquiv` alone.

## The route, in the order the term takes it

1. `FormalSpectrum.awayCompletionNestedAlgEquivOfLe` (`FormalSchemes.AwayCompletionUniversal`)
   reads `A_i{1/(h · e_ij)}` as a completed localization of the coarse chart `A_i{1/g_ij}`, at the
   structural image of `h · e_ij`. It is the `basicOpen`-keyed form, so all it wants is the
   containment `D(h · e_ij) ≤ D(g_ij)`, which is
   `FormalSpectrum.basicOpen_mul_le_of_basicOpen_le` at
   `FormalSpectrum.basicOpen_refinedOverlapElt_le`.
2. `FormalSpectrum.awayCompletionAlgEquivOfBase` (`FormalSchemes.AwayBaseChangeTopFiniteType`,
   issue 2192) transports *τ_ij* to those localizations: an `R`-algebra equivalence `σ : S ≃ₐ[R] T`
   with `σ u = v` gives `S{1/u} ≃ₐ[R] T{1/v}`. At `u := ĥ · ê_ij` it is applied with `v` left to
   unification and `huv := rfl`, so no transport lemma is named at this step.
3. `FormalSpectrum.awayCompletionCongrBasicOpenAlg` (`FormalSchemes.AwayCompletionRestrictUnique`)
   then replaces that presenting element by the one chart *j* indexes, which is exactly
   `FormalSpectrum.basicOpen_awayCompletionAlgEquiv_mul_refinedOverlapElt` above.
4. Step 1 again on the *j* side, taken backwards.

## The two bookkeeping steps the four declarations do not name, and they fail differently

This is the only non-obvious thing on the route, and both halves are stated here because a paste of
the four alone hits them in order.

`FormalSpectrum.awayCompletionCongrBasicOpenAlg` is an equivalence over the base of *its own* ideal
rather than over `R`, so it wants `AlgEquiv.restrictScalars`; a paste that omits it does **not**
report a scalar mismatch but exhausts the default heartbeats at `isDefEq`, the elaborator having
been asked whether `R` and that completion are the same scalar ring and walking the completion
tower to answer. **A timeout there is that omission and not an obstruction** — raising the budget
to a million heartbeats only buys a longer one. The second step is that equivalence's hypothesis,
which is asked for at `I.map (algebraMap R _)` where `FormalSchemes.RefinedOverlapRestrict`'s
statements are at `FormalSpectrum.awayCompletionIdeal`;
`FormalSpectrum.map_algebraMap_awayCompletion_eq` (`FormalSchemes.BasicOpenChart`) is the bridge
and it is one `rw`, and omitting *that* one does fail with a type error in seconds, naming both
spellings of the ideal. The same pair of conventions is what
`FormalSchemes.RefinedOverlapRestrict`'s transport paragraph prices one step earlier.

## The symmetry law, and why the pointwise route to it is the wrong one

`FormalSpectrum.refinedOverlapTransition_symm` says the transition at the swapped refined pair is
this one's inverse. **It is well-typed, which is the first thing to know and is not obvious**: the
swapped pair presents its *i*-side element at `τ.symm.symm` rather than at `τ`, and those agree by
`rfl` — checked at the completions the statement lives at, not assumed from `AlgEquiv.symm_symm`.

**Every pointwise route to it is a heartbeat timeout and none of them is taken here.** Measured
with `lake env lean` outside the tree at the default budget: `rfl` times out at `isDefEq`,
`AlgEquiv.ext fun _ => rfl` at `isDefEq`, and `AlgEquiv.symm_bijective.injective (by rfl)` at
`whnf`. That is the species this cluster has recorded repeatedly at the completed-localization
layer, and more heartbeats are not the answer to it: both sides are composites of four equivalences
through different completions, so asking whether they agree at a point asks the elaborator to walk
all eight.

**What works is rigidity applied to the middle two steps alone, and the outer two cancelling
formally.** Of the four steps of the route above, the first and the last are the nested
identifications at the *i* and the *j* chart, and the swapped composite takes them in the opposite
order — its first step *is* this composite's last, on the nose, and its last is this one's first,
by proof irrelevance and `τ.symm.symm = τ`. So they cancel with **no naturality statement about
`FormalSpectrum.awayCompletionNestedAlgEquivOfLe` anywhere**, which is what keeps this cheap: a
naturality statement at a doubly nested completion is the expensive thing
`FormalSchemes.BasicOpenCoverCharts` prices at about 160 s a lemma unless it is discharged once at
the top level.

What is left is the middle, and that is
`FormalSpectrum.awayCompletionAlgEquivOfBase_congr_trans_eq_refl`. It is an automorphism of one
completed localization which fixes the image of its own base ring, because each of its four steps
is a map under that base —
`FormalSpectrum.awayCompletionAlgEquivOfBase_algebraMap`
(`FormalSchemes.AwayBaseChangeTopFiniteType`) for the two base changes and `AlgEquiv.commutes` for
the two re-presentations, which is free because
`FormalSpectrum.awayCompletionCongrBasicOpenAlg` is an equivalence over the base of its own ideal.
`FormalSpectrum.awayCompletion_hom_ext` (`FormalSchemes.AwayCompletionRestrictUnique`) then says a
map out of a completed localization carrying the ideal of definition across is determined by that
square, and the containment it asks for is
`FormalSpectrum.le_comap_awayCompletionIdeal_algHom` for any `R`-algebra map at all. **That is the
whole proof.** It runs in 6 s at the default budget with no `set_option`.

**`AlgEquiv.trans_symm_of_middle_eq_refl` is stated at this composite's own bracketing, and that is
not a stylistic choice.** It takes its six steps separately rather than the middle as one
equivalence. Re-associating `(N_i ≫ B) ≫ (C ≫ N_j⁻¹)` into `(N_i ≫ (B ≫ C)) ≫ N_j⁻¹` — which
`AlgEquiv.trans` justifies and which reads better — makes the elaborator compare two differently
bracketed composites of these completions, and the four-argument form of the lemma is then a
`whnf` timeout at the instantiation below where the six-argument form is 6 s. **A general lemma
about composites at this layer has to be shaped like the definition it will be applied to.**

## The conjugated symmetry law, and the one figure elaboration does not report

`FormalSpectrum.refinedOverlapTransition_conj_symm` is what a datum's `τ_symm` field asks for, and
it differs from `FormalSpectrum.refinedOverlapTransition_symm` in two ways that both come from the
datum rather than from the mathematics. A datum carries a *family* of coarse transitions, so at the
swapped pair the transition is the field `τ_ji` where the statement above has *τ_ij⁻¹*; the two
agree by the datum's own symmetry law, but only propositionally, so a bridge
`CompletedTensorAwayInterchange.awayCongrEquivOfEq` respelling the swapped overlap element sits
after each transition and the field is a **four**-fold composite. And each refined chart is
presented as a completed localization of the chart algebra above it, so the whole thing is
conjugated by that presentation at both ends.

**Neither widening costs anything, and issue 2198 §5 expected both to.** That section routed the
field through `AlgebraicGeometry.BasicOpenCover.tau_symm_conj`
(`FormalSchemes.BasicOpenCoverTransitions`), observed that the lemma is stated for a *three*-fold
composite and the field is four-fold, and recorded the mismatch as this row's open question. The
answer is that the outer-steps-cancel argument of the section above applies one level out
unchanged: the swapped conjugate opens with the presentation this one closes with, so
`AlgEquiv.symm_trans_symm_of_middle_eq_refl` cancels the two presentations formally, and the middle
is the round trip with the two bridges in it. **`AlgebraicGeometry.BasicOpenCover.tau_symm_conj` is
not used and neither is any naturality statement about the presentation**, so the ~160 s-a-lemma
cost
`FormalSchemes.BasicOpenCoverCharts` carries is not paid by this field. It is still owed by `hστ`.

**The one measurement worth carrying away is a `(deterministic) timeout` in the *kernel*, after
elaboration has already succeeded.** With the datum's symmetry law substituted, each bridge's two
sides coincide — the second only up to *τ_ij⁻¹⁻¹* against *τ_ij*, which is `rfl` here — so each
bridge is `AlgEquiv.refl` by `rfl`, and the obvious route is to rewrite with those two `rfl`s and
then cancel the trailing identities. Measured with `lake env lean` outside the tree at the default
budget:

* `rw` with the two `rfl`s, then `AlgEquiv.ext` and a `simp only` transferring the round trip:
  elaborates, then **`(kernel) deterministic timeout`** at about 100 s;
* the same without the `rw`, taking the bridges out pointwise instead: same kernel timeout;
* `e.trans AlgEquiv.refl = e` by `rfl` at these types: **`maximum recursion depth`**;
* `AlgEquiv.trans_trans_eq_refl_of_bridges`, which takes both bridges as *hypotheses* and does the
  `subst` where the carriers are variables: **EXIT 0 in 3 s**, axioms clean.

**So a `simp only` on the goal at this layer is a cost the elaborator does not price**, and a
scouting run that stubs its remaining goals will not see it either: the failing runs above reported
no elaboration error and the kernel rejected them afterwards. The species is the one
`AlgEquiv.trans_symm_of_middle_eq_refl`'s docstring records one level in — a general lemma has to
be shaped like the definition it is applied to — read now as *which of its arguments are already
evaluated*, and the remedy is the same: move the step to the abstract layer.

## Placement

A leaf over `FormalSchemes.RefinedOverlapRestrict`, `FormalSchemes.AwayCompletionAlgHomBasicOpen`,
`FormalSchemes.AwayCompletionCongrEquiv`, `FormalSchemes.AwayBaseChangeTopFiniteType` and
`FormalSchemes.AwayCompletionUniversal`: the forward closure of
`FormalSchemes.RefinedOverlapTransition` is **71** project modules besides itself (72 counted with
itself), and the reverse closure of `FormalSchemes.RefinedOverlapTransition` is **0**.

**A new module is forced, and that was measured rather than argued.** No module of this tree
reaches all five of the above — none reaches even three of the five: of the other 585, **554**
reach none, **26** reach exactly one and **5** reach two. So the *put it in a file that already
imports enough* option does not exist, and the alternative is an import into an existing file,
which is the expensive direction. `FormalSchemes.RefinedOverlapRestrict` is the closest candidate
and reaches **41**, and it is missing four of the five: the edges to
`FormalSchemes.AwayCompletionAlgHomBasicOpen`, `FormalSchemes.AwayCompletionCongrEquiv`,
`FormalSchemes.AwayBaseChangeTopFiniteType` and `FormalSchemes.AwayCompletionUniversal` cost
**+6**, **+12**, **+15** and **+16** modules there, and every consumer that file ever gains would
inherit them.

**One of the five imports is free in closure terms and is kept anyway.**
`FormalSchemes.AwayBaseChangeTopFiniteType` lies inside `FormalSchemes.AwayCompletionUniversal`'s
forward closure of **55** — that module imports it on its first line — so dropping the import line
would leave the 71 above unchanged. It is kept because
`FormalSpectrum.awayCompletionAlgEquivOfBase` is used here directly, which is this tree's practice
and not a departure from it: **140** of the **586** modules under `FormalSchemes/` carry an import
some other import of the same file already reaches, this one included. Counting only what each
import brings that no other of the five reaches, the split is **7** for
`FormalSchemes.AwayCompletionCongrEquiv`, **6** for
`FormalSchemes.AwayCompletionAlgHomBasicOpen`, **2** for
`FormalSchemes.RefinedOverlapRestrict`, **1** for `FormalSchemes.AwayCompletionUniversal` and
**0** for `FormalSchemes.AwayBaseChangeTopFiniteType`; the remaining 55 of the 71 are reached by
more than one of them.

**The fifth import is the conjugated symmetry law's, and it was priced before it was written.**
`CompletedTensorAwayInterchange.awayCongrEquivOfEq` is the only transport along an equality of away
elements on this tree — one `git grep` over `FormalSchemes/` finds exactly one declaration built by
matching on `rfl` — and a datum's `τ_symm` field cannot be stated without it, so the alternatives
were this edge or a new module over this one. `scripts/closure_audit.py --edge` prices the edge at
**7** modules and **3** figure repairs in **2** files, against the **37** in **17** that adding
this module cost; this file's reverse closure of **0** is what makes that comparison lopsided, and
the same edge at a file with consumers would not be.

**What the module costs is the figure sweep, not the build.** Adding any module under
`FormalSchemes/` falsifies every absolute *reverse*-closure figure quoted about anything it imports
— CONTRIBUTING.md's *What adding a module costs* is the standing account — and here that is **37**
numerals in **17** files, every one of them a `+1`. Editing those 17 re-elaborates **538** of the
586 modules, and the concentration is the same one CONTRIBUTING.md records: the reverse closure of
`FormalSchemes.StructureSheaf` is **529**, and dropping that one file from the 17 takes the sweep's
rebuild to **80**. Two of the 37 are not renumberings:
`FormalSchemes/RefinedOverlapRestrict.lean` and
`FormalSchemes/AwayCompletionAlgHomBasicOpen.lean` each state that they are **leaves**, and this
module is their first consumer, so both `## Placement` paragraphs are rewritten rather than
renumbered — in the first case because the ratio it declines a move on was argued from a *single
call site*, and this module is the second.

This paragraph's counts are measurements of the diff that added this file, at the base it was taken
at; they are not standing claims about any later tree and nothing re-runs them. Re-measure with
`scripts/closure_audit.py --tree`, and price any sixth import with `--edge` before writing a word
about it.

**Five of the statements below are general and all five are kept here, and the decisive one is
decided by a walk rather than by taste.**
`FormalSpectrum.awayCompletionAlgEquivOfBase_congr_trans_eq_refl` is general in both its chart
algebras and names nothing of the refined overlap, so its subject-matter home is beside the base
change it is about. It cannot go there: it needs
`FormalSchemes.AwayBaseChangeTopFiniteType`, `FormalSchemes.AwayCompletionRestrictUnique` and
`FormalSchemes.AwayCompletionAlgHomBasicOpen` at once, and **this module is the only one of the 586
that reaches all three** — 545 reach none of them, 35 reach exactly one, 5 reach two and this file
is the one that reaches three. So its only homes besides this file are a new module over this one
or an import into an existing one, and this section prices the second.
The four `AlgEquiv` lemmas name nothing of this tree at all — they are statements about
`AlgEquiv.trans` and `AlgEquiv.symm`, and Mathlib is where they belong, which is why all four are
stated at `CommSemiring` and `Semiring` with their six carriers in independent universes rather
than at this file's own `CommRing` and `Type u`: their proofs use nothing else, and a statement
offered to Mathlib on that argument should carry Mathlib's hypotheses. The nearest thing to a
subject-matter home here is an early module about algebra equivalences, and of those
`FormalSchemes.AdicCompletionCongrIdealAlg` is the cheapest, at a reverse closure of **196**
against this file's **0**, with one call site each. Declined on that ratio, which is this tree's
standing disposition for a general statement with a single call site. **Re-cost all five when a
consumer appears that does not reach this file**; a
consumer inside this file's own subtree buys nothing, for the reason
`FormalSchemes/RefinedOverlapRestrict.lean`'s `## Placement` gives at
`FormalSpectrum.basicOpen_mul_le_of_basicOpen_le`.

## What is *not* proved here

**The refined datum itself, and every field of it except `τ_symm`.**
`FormalSpectrum.refinedOverlapTransition_conj_symm` is one field of
`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData` at the refined index and nothing takes
the smart constructor's remaining arguments; no `AlgebraicGeometry.AffineChartedFibreDatumX` is
built anywhere on this tree from a refined chart family. Fed slot 0's scouting instantiation on
issue 2198, the conjugated law closes the `τ_symm` argument and leaves `σ`, `hστ` and `hσc`.

**The cocycle condition on a triple of charts**, and **nothing about `σ`, the triple overlap or the
refined datum's remaining laws**. Those are issue 2148's goal 2, scoped on issue 2198, where the
`σ` field is already built at an abstract total coarse family; this module is the cross-chart
transition, its symmetry and that symmetry's conjugate, and nothing else.

**The refining elements are arbitrary here, and a datum's are not.** Both statements of the
conjugated law quantify over `h`, `h'` and over the two coarse transitions independently, with the
datum's symmetry law supplied as a hypothesis `hs`. Producing that hypothesis from a family defined
at every ordered pair — including the diagonal, where a coarse datum supplies no overlap element —
is issue 2198 §6.3 and is not priced here.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13, §10.15.
-/

noncomputable section

universe u

namespace AlgEquiv

variable {R : Type u} [CommSemiring R]
variable {X P Q Q' Y P' : Type*} [Semiring X] [Semiring P] [Semiring Q] [Semiring Q']
  [Semiring Y] [Semiring P'] [Algebra R X] [Algebra R P] [Algebra R Q] [Algebra R Q']
  [Algebra R Y] [Algebra R P']

/-- **Two four-step composites sharing their outer identifications are mutually inverse as soon as
their middles are.** For

```
Ni ≫ B ≫ C ≫ Nj⁻¹  :  X ≃ Y        Nj ≫ B' ≫ C' ≫ Ni⁻¹  :  Y ≃ X
```

the second is the first's inverse once `B ≫ C ≫ B' ≫ C'` is the identity of `P`. The outer
identifications are taken in opposite orders by the two composites, so they cancel formally and
nothing is assumed about them.

**The six steps are separate arguments deliberately, and the middle is not packaged as one
equivalence.** Stating this with `E := B ≫ C` and `F := B' ≫ C'` needs the conclusion re-associated
to `(Ni ≫ E) ≫ Nj⁻¹`, and at the completed localizations
`FormalSpectrum.refinedOverlapTransition_symm` applies it to, that re-association is a
`(deterministic) timeout at whnf` at the default budget where this shape is seconds. The module
docstring's `## The symmetry law` section carries the measurement. A general lemma about composites
has to be shaped like the definition it is applied to, and this is that shape.

Nothing of this project's subject matter appears here; see this module's `## Placement` for why the
statement is nevertheless local. -/
theorem trans_symm_of_middle_eq_refl
    (Ni : X ≃ₐ[R] P) (B : P ≃ₐ[R] Q) (C : Q ≃ₐ[R] Q') (Nj : Y ≃ₐ[R] Q')
    (B' : Q' ≃ₐ[R] P') (C' : P' ≃ₐ[R] P)
    (hmid : (B.trans C).trans (B'.trans C') = AlgEquiv.refl) :
    (Nj.trans B').trans (C'.trans Ni.symm)
      = (((Ni.trans B).trans (C.trans Nj.symm)) : X ≃ₐ[R] Y).symm := by
  have hback : ∀ q, C (B (C' (B' q))) = q := fun q => by
    have hp := DFunLike.congr_fun hmid (C' (B' q))
    simp only [AlgEquiv.trans_apply, AlgEquiv.coe_refl, id_eq] at hp
    exact B'.injective (C'.injective hp)
  refine AlgEquiv.ext fun y => ?_
  refine (AlgEquiv.eq_symm_apply _).mpr ?_
  simp only [AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply, hback, AlgEquiv.symm_apply_apply]

/-- **The round-trip form of `AlgEquiv.trans_symm_of_middle_eq_refl`**, at the same six steps and
the same hypothesis. Not a corollary of that lemma in practice: deriving it by rewriting with the
`symm` form puts the swapped composite's target type back in the goal in a spelling the rewrite has
already moved, which is a recursion-depth failure at the instantiation
`FormalSpectrum.refinedOverlapTransition_trans_symm` makes. Proved from `hmid` directly instead,
which is three lines. -/
theorem trans_trans_eq_refl_of_middle_eq_refl
    (Ni : X ≃ₐ[R] P) (B : P ≃ₐ[R] Q) (C : Q ≃ₐ[R] Q') (Nj : Y ≃ₐ[R] Q')
    (B' : Q' ≃ₐ[R] P') (C' : P' ≃ₐ[R] P)
    (hmid : (B.trans C).trans (B'.trans C') = AlgEquiv.refl) :
    (((Ni.trans B).trans (C.trans Nj.symm)).trans
        ((Nj.trans B').trans (C'.trans Ni.symm)) : X ≃ₐ[R] X) = AlgEquiv.refl := by
  refine AlgEquiv.ext fun x => ?_
  have hx := DFunLike.congr_fun hmid (Ni x)
  simp only [AlgEquiv.trans_apply, AlgEquiv.coe_refl, id_eq] at hx
  simp only [AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply, AlgEquiv.coe_refl, id_eq, hx,
    AlgEquiv.symm_apply_apply]

/-- **`AlgEquiv.trans_symm_of_middle_eq_refl` with the outer identifications given in the direction
a conjugation supplies them.** A four-step composite that *opens* with the inverse of an
identification and *closes* with another one —

```
Mi⁻¹ ≫ B ≫ C ≫ Mj  :  X ≃ Y        Mj⁻¹ ≫ B' ≫ C' ≫ Mi  :  Y ≃ X
```

— is the shape of a datum's transition field, whose two identifications present the two charts and
are therefore given as maps *into* the field's source and target rather than out of them. The
hypothesis is the same as `AlgEquiv.trans_symm_of_middle_eq_refl`'s and so is the proof.

**This is a different statement and not that one instantiated at the inverses of `Mi` and `Mj`.**
Doing that leaves a double `AlgEquiv.symm` on each of them in the conclusion where a conjugation
has `Mi` and `Mj` themselves, and closing the gap is a `simp` under the composite. Harmless here,
where the carriers are
variables; a `simp` on the goal at the completions
`FormalSpectrum.refinedOverlapTransition_conj_symm` instantiates this at is a **kernel** timeout,
which is the measurement the module docstring's `## The conjugated symmetry law` section records.
Stating both shapes is the cheap side of that trade. -/
theorem symm_trans_symm_of_middle_eq_refl
    (Mi : P ≃ₐ[R] X) (B : P ≃ₐ[R] Q) (C : Q ≃ₐ[R] Q') (Mj : Q' ≃ₐ[R] Y)
    (B' : Q' ≃ₐ[R] P') (C' : P' ≃ₐ[R] P)
    (hmid : (B.trans C).trans (B'.trans C') = AlgEquiv.refl) :
    (Mj.symm.trans B').trans (C'.trans Mi)
      = (((Mi.symm.trans B).trans (C.trans Mj)) : X ≃ₐ[R] Y).symm := by
  have hback : ∀ q, C (B (C' (B' q))) = q := fun q => by
    have hp := DFunLike.congr_fun hmid (C' (B' q))
    simp only [AlgEquiv.trans_apply, AlgEquiv.coe_refl, id_eq] at hp
    exact B'.injective (C'.injective hp)
  refine AlgEquiv.ext fun y => ?_
  refine (AlgEquiv.eq_symm_apply _).mpr ?_
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, hback, AlgEquiv.apply_symm_apply]

/-- **Two mutually inverse equivalences stay mutually inverse when each is followed by an
equivalence that is the identity.** The two trailing steps are given as arbitrary equivalences with
an equation saying each is `AlgEquiv.refl`, rather than as `AlgEquiv.refl` itself.

**That is the whole point of the statement and it is a measurement, not a preference.** At the
completed localizations `FormalSpectrum.refinedOverlapTransition_bridge_trans_eq_refl` applies this
to, the two trailing steps are transports along equalities of away elements
(`CompletedTensorAwayInterchange.awayCongrEquivOfEq`) whose two sides have become the same, so each
*is* `AlgEquiv.refl` by `rfl` — but **rewriting with those two `rfl`s and then discharging
`e.trans AlgEquiv.refl = e` is a `(deterministic) timeout` in the *kernel* after elaboration has
already succeeded**, 100 s against this route's 3 s, and `e.trans AlgEquiv.refl = e` by `rfl` is a
`maximum recursion depth` at those types. Taking the two equations as hypotheses moves both steps
here, where the carriers are variables and `subst` is free.

Same species as `AlgEquiv.trans_symm_of_middle_eq_refl`'s bracketing note one paragraph up, one
level further out: not only the shape of a general lemma but *which of its arguments are already
evaluated* is decided by the layer it is applied at. -/
theorem trans_trans_eq_refl_of_bridges (B : P ≃ₐ[R] Q) (Cj : Q ≃ₐ[R] Q) (B' : Q ≃ₐ[R] P)
    (Ci : P ≃ₐ[R] P) (hCj : Cj = AlgEquiv.refl) (hCi : Ci = AlgEquiv.refl)
    (hBB' : B.trans B' = AlgEquiv.refl) :
    ((B.trans Cj).trans (B'.trans Ci) : P ≃ₐ[R] P) = AlgEquiv.refl := by
  subst hCj
  subst hCi
  refine AlgEquiv.ext fun x => ?_
  have hx := DFunLike.congr_fun hBB' x
  simp only [AlgEquiv.trans_apply, AlgEquiv.coe_refl, id_eq] at hx ⊢
  exact hx

end AlgEquiv

open CompletedTensorAwayInterchange

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {Ai Aj : Type u} [CommRing Ai] [CommRing Aj] [Algebra R Ai] [Algebra R Aj]

/-- **The two refined presentations of one overlap correspond under the coarse transition.** Inside
`Spf (A_j{1/g_ji})`, the *τ_ij*-image of the open cut out by the *i*-side refined element
`h · e_ij` is the open cut out by the *j*-side one, `h' · e_ji`.

This is the hypothesis `FormalSpectrum.awayCompletionCongrBasicOpenAlg`
(`FormalSchemes.AwayCompletionRestrictUnique`) asks for in the third step of
`FormalSpectrum.refinedOverlapTransition`, and it is the only statement in this module with
content.

**Nothing topological happens here.** That was spent in
`FormalSpectrum.basicOpen_awayCompletionHom_mul_refinedOverlapElt`
(`FormalSchemes.RefinedOverlapRestrict`), which reads either refined presentation inside its *own*
coarse chart as the meet of the two refining elements. Both sides below are that statement — once
at *⟨i, h⟩*, *⟨j, h'⟩* and once at the swapped pair, where it arrives with a `τ.symm.symm` that is
`τ` by `AlgEquiv.symm_symm` — so what is left is to carry a meet across *τ_ij*, which is
`FormalSpectrum.basicOpen_awayCompletionAlgEquiv_eq_iff`
(`FormalSchemes.AwayCompletionAlgHomBasicOpen`, issue 2193) in the four-rewrite idiom that module's
docstring prescribes for exactly this shape. **One step beyond the idiom is needed and it is worth
naming**: the *j*-side meet has one factor already in the target chart, so
`AlgEquiv.apply_symm_apply` has to put it back under *τ_ij* before the two factors can be
multiplied under one `map_mul`. The two meets then differ by `inf_comm`.

The statement is asymmetric in appearance only. `e_ij` and `e_ji` are both
`FormalSpectrum.refinedOverlapElt`, at the two orders of the same pair, and each is pinned only up
to an equality of basic opens — which is why the elements the refined datum indexes by, `h`, `h'`
and *τ_ij*, are the ones written on both sides, and `e_ij`, `e_ji` appear only inside the
products. -/
theorem basicOpen_awayCompletionAlgEquiv_mul_refinedOverlapElt (hI : I.FG) (gij : Ai) (gji : Aj)
    (τ : awayCompletion (I.map (algebraMap R Ai)) gij ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) gji)
    (h : Ai) (h' : Aj) :
    basicOpen (awayCompletionIdeal (I.map (algebraMap R Aj)) gji)
        (τ (awayCompletionHom (I.map (algebraMap R Ai)) gij
          (h * refinedOverlapElt I hI gij gji τ h h')))
      = basicOpen (awayCompletionIdeal (I.map (algebraMap R Aj)) gji)
          (awayCompletionHom (I.map (algebraMap R Aj)) gji
            (h' * refinedOverlapElt I hI gji gij τ.symm h' h)) := by
  rw [basicOpen_awayCompletionHom_mul_refinedOverlapElt I hI gji gij τ.symm h' h,
    AlgEquiv.symm_symm, ← τ.apply_symm_apply (awayCompletionHom
      (I.map (algebraMap R Aj)) gji h'), ← basicOpen_mul, ← map_mul,
    basicOpen_awayCompletionAlgEquiv_eq_iff I gij gji τ, basicOpen_mul,
    basicOpen_awayCompletionHom_mul_refinedOverlapElt I hI gij gji τ h h']
  exact inf_comm _ _

/-- **The transition of the refined chart family at a cross-chart refined pair.** For chart
algebras `A_i`, `A_j` over `R`, coarse overlap elements `g_ij : A_i`, `g_ji : A_j` joined by an
`R`-algebra equivalence *τ_ij* of their completed localizations, and refining elements `h : A_i`,
`h' : A_j`, the `R`-algebra equivalence

```
A_i{1/(h · e_ij)}  ≃ₐ[R]  A_j{1/(h' · e_ji)}
```

between the two refined presentations of the refined overlap, with `e_ij`, `e_ji` the two orders of
`FormalSpectrum.refinedOverlapElt` (`FormalSchemes.RefinedOverlapRestrict`).

**This is a composite of four declarations already on the tree, and not a descent statement.** The
module docstring lists the four in the order the term takes them and states the two bookkeeping
steps they do not name; the one thing worth repeating here is that a paste of the four which drops
`AlgEquiv.restrictScalars` at the third step does not report a scalar mismatch but exhausts the
default heartbeats at `isDefEq`, so **a timeout there is that omission and not an obstruction**.

No hypothesis beyond `I.FG` is needed, and in particular nothing is assumed about *τ_ij* beyond its
being an `R`-algebra equivalence of the two coarse overlap algebras: the refined overlap element is
a function of it, so the cross-chart data are pinned by the coarse datum alone. -/
def refinedOverlapTransition (hI : I.FG) (gij : Ai) (gji : Aj)
    (τ : awayCompletion (I.map (algebraMap R Ai)) gij ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) gji)
    (h : Ai) (h' : Aj) :
    awayCompletion (I.map (algebraMap R Ai)) (h * refinedOverlapElt I hI gij gji τ h h') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj))
        (h' * refinedOverlapElt I hI gji gij τ.symm h' h) :=
  ((awayCompletionNestedAlgEquivOfLe I hI gij _
        (basicOpen_mul_le_of_basicOpen_le _ h
          (basicOpen_refinedOverlapElt_le I hI gij gji τ h h'))).trans
      (awayCompletionAlgEquivOfBase I hI τ rfl)).trans
    (((awayCompletionCongrBasicOpenAlg _ _ _ (hI.map _) (by
          rw [map_algebraMap_awayCompletion_eq]
          exact basicOpen_awayCompletionAlgEquiv_mul_refinedOverlapElt I hI gij gji τ h h'
          )).restrictScalars R).trans
      (awayCompletionNestedAlgEquivOfLe I hI gji _
        (basicOpen_mul_le_of_basicOpen_le _ h'
          (basicOpen_refinedOverlapElt_le I hI gji gij τ.symm h' h))).symm)

/-! ### The base-change round trip, and the symmetry law it gives -/

section BaseChangeRoundTrip

variable {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- **Base change along `σ` and back is the identity, through any re-presentation of the presenting
element on the way.** For an `R`-algebra equivalence `σ : S ≃ₐ[R] T` of chart algebras and `u : S`,
`w : T` cutting out corresponding opens at each end, the composite

```
S{1/u}  ⟶  T{1/σu}  ⟶  T{1/w}  ⟶  S{1/σ⁻¹w}  ⟶  S{1/u}
```

of `FormalSpectrum.awayCompletionAlgEquivOfBase` twice and
`FormalSpectrum.awayCompletionCongrBasicOpenAlg` twice is `AlgEquiv.refl`.

**This is the only statement with content in the proof of
`FormalSpectrum.refinedOverlapTransition_symm`**, and it is rigidity and not computation. The
composite is an automorphism of `S{1/u}` fixing the image of `S`: the two base changes are maps
under `S` and `T` by `FormalSpectrum.awayCompletionAlgEquivOfBase_algebraMap`, and the two
re-presentations are maps under the base of their own ideal by `AlgEquiv.commutes`, which is what
`AlgEquiv.restrictScalars` leaves intact. `FormalSpectrum.awayCompletion_hom_ext`
(`FormalSchemes.AwayCompletionRestrictUnique`) then forces it to be the identity, its continuity
hypothesis being `FormalSpectrum.le_comap_awayCompletionIdeal_algHom`
(`FormalSchemes.AwayCompletionAlgHomBasicOpen`) at an arbitrary `R`-algebra map.

**Both `huv` arguments are `rfl`**, which is what makes the two hypotheses `m` and `m'` the only
data: the target of each base change is left to unification rather than named.

Nothing about the refined overlap is used, and the two hypotheses are exactly what a cross-chart
refined pair supplies twice over. -/
theorem awayCompletionAlgEquivOfBase_congr_trans_eq_refl (hI : I.FG) (σ : S ≃ₐ[R] T)
    (u : S) (w : T)
    (m : basicOpen (I.map (algebraMap R T)) (σ u) = basicOpen (I.map (algebraMap R T)) w)
    (m' : basicOpen (I.map (algebraMap R S)) (σ.symm w) = basicOpen (I.map (algebraMap R S)) u) :
    ((awayCompletionAlgEquivOfBase I hI σ (rfl : σ u = σ u)).trans
          ((awayCompletionCongrBasicOpenAlg _ _ _ (hI.map _) m).restrictScalars R)).trans
        ((awayCompletionAlgEquivOfBase I hI σ.symm (rfl : σ.symm w = σ.symm w)).trans
          ((awayCompletionCongrBasicOpenAlg _ _ _ (hI.map _) m').restrictScalars R))
      = AlgEquiv.refl := by
  set E := ((awayCompletionAlgEquivOfBase I hI σ (rfl : σ u = σ u)).trans
        ((awayCompletionCongrBasicOpenAlg _ _ _ (hI.map _) m).restrictScalars R)).trans
      ((awayCompletionAlgEquivOfBase I hI σ.symm (rfl : σ.symm w = σ.symm w)).trans
        ((awayCompletionCongrBasicOpenAlg _ _ _ (hI.map _) m').restrictScalars R)) with hE
  have key : (E : awayCompletion (I.map (algebraMap R S)) u →ₐ[R] _).toRingHom = RingHom.id _ := by
    refine awayCompletion_hom_ext (I.map (algebraMap R S)) u u (hI.map _)
      (le_comap_awayCompletionIdeal_algHom I u u E.toAlgHom)
      (le_comap_awayCompletionIdeal_algHom I u u (AlgHom.id R _)) ?_
    refine RingHom.ext fun s => ?_
    change E (awayCompletionHom (I.map (algebraMap R S)) u s)
      = awayCompletionHom (I.map (algebraMap R S)) u s
    rw [awayCompletionHom_eq_algebraMap, hE]
    simp only [AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
      awayCompletionAlgEquivOfBase_algebraMap, AlgEquiv.commutes, AlgEquiv.symm_apply_apply]
  exact AlgEquiv.ext fun x => RingHom.congr_fun key x

end BaseChangeRoundTrip

/-- **The transition at the swapped refined pair is this one's inverse.** This is `τ_symm` in the
language of `AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData`, which spells it
`τ j i h.symm = (τ i j h).symm`, read at `FormalSpectrum.refinedOverlapTransition` rather than at a
datum's field — the conjugation that turns one into the other is issue 2198's and is named in this
module's `## What is *not* proved here`.

**The statement is well-typed for a reason worth stating**: the swapped pair presents its *i*-side
refined element at `τ.symm.symm`, and that is `τ` by `rfl` at these completions.

The proof is `AlgEquiv.trans_symm_of_middle_eq_refl` at the six steps of
`FormalSpectrum.refinedOverlapTransition` and its swap, with
`FormalSpectrum.awayCompletionAlgEquivOfBase_congr_trans_eq_refl` as the middle. The two nested
identifications never appear in it: the swapped composite opens with the one this composite closes
with, so no naturality statement about `FormalSpectrum.awayCompletionNestedAlgEquivOfLe` is needed,
and that is the whole reason this is cheap rather than the 160 s-per-lemma shape
`FormalSchemes.BasicOpenCoverCharts` prices. **No pointwise route works** — see the module
docstring. -/
theorem refinedOverlapTransition_symm (hI : I.FG) (gij : Ai) (gji : Aj)
    (τ : awayCompletion (I.map (algebraMap R Ai)) gij ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) gji) (h : Ai) (h' : Aj) :
    refinedOverlapTransition I hI gji gij τ.symm h' h
      = (refinedOverlapTransition I hI gij gji τ h h').symm :=
  AlgEquiv.trans_symm_of_middle_eq_refl
    (awayCompletionNestedAlgEquivOfLe I hI gij _
      (basicOpen_mul_le_of_basicOpen_le _ h
        (basicOpen_refinedOverlapElt_le I hI gij gji τ h h')))
    (awayCompletionAlgEquivOfBase I hI τ rfl)
    ((awayCompletionCongrBasicOpenAlg _ _ _ (hI.map _) (by
        rw [map_algebraMap_awayCompletion_eq]
        exact basicOpen_awayCompletionAlgEquiv_mul_refinedOverlapElt I hI gij gji τ h h'
        )).restrictScalars R)
    (awayCompletionNestedAlgEquivOfLe I hI gji _
      (basicOpen_mul_le_of_basicOpen_le _ h'
        (basicOpen_refinedOverlapElt_le I hI gji gij τ.symm h' h)))
    (awayCompletionAlgEquivOfBase I hI τ.symm rfl)
    ((awayCompletionCongrBasicOpenAlg _ _ _ (hI.map _) (by
        rw [map_algebraMap_awayCompletion_eq]
        exact basicOpen_awayCompletionAlgEquiv_mul_refinedOverlapElt I hI gji gij τ.symm h' h
        )).restrictScalars R)
    (awayCompletionAlgEquivOfBase_congr_trans_eq_refl I hI τ _ _ _ _)

/-- **The round-trip reading of `FormalSpectrum.refinedOverlapTransition_symm`**: going to the *j*
presentation and back is the identity. Stated because a consumer composing refined transitions
wants it in this form and should not have to turn the `symm` form into it — which is not free, for
the reason `AlgEquiv.trans_trans_eq_refl_of_middle_eq_refl`'s docstring records. -/
theorem refinedOverlapTransition_trans_symm (hI : I.FG) (gij : Ai) (gji : Aj)
    (τ : awayCompletion (I.map (algebraMap R Ai)) gij ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) gji) (h : Ai) (h' : Aj) :
    (refinedOverlapTransition I hI gij gji τ h h').trans
        (refinedOverlapTransition I hI gji gij τ.symm h' h) = AlgEquiv.refl :=
  AlgEquiv.trans_trans_eq_refl_of_middle_eq_refl
    (awayCompletionNestedAlgEquivOfLe I hI gij _
      (basicOpen_mul_le_of_basicOpen_le _ h
        (basicOpen_refinedOverlapElt_le I hI gij gji τ h h')))
    (awayCompletionAlgEquivOfBase I hI τ rfl)
    ((awayCompletionCongrBasicOpenAlg _ _ _ (hI.map _) (by
        rw [map_algebraMap_awayCompletion_eq]
        exact basicOpen_awayCompletionAlgEquiv_mul_refinedOverlapElt I hI gij gji τ h h'
        )).restrictScalars R)
    (awayCompletionNestedAlgEquivOfLe I hI gji _
      (basicOpen_mul_le_of_basicOpen_le _ h'
        (basicOpen_refinedOverlapElt_le I hI gji gij τ.symm h' h)))
    (awayCompletionAlgEquivOfBase I hI τ.symm rfl)
    ((awayCompletionCongrBasicOpenAlg _ _ _ (hI.map _) (by
        rw [map_algebraMap_awayCompletion_eq]
        exact basicOpen_awayCompletionAlgEquiv_mul_refinedOverlapElt I hI gji gij τ.symm h' h
        )).restrictScalars R)
    (awayCompletionAlgEquivOfBase_congr_trans_eq_refl I hI τ _ _ _ _)

/-! ### The conjugated symmetry law: a datum's `τ_symm` field -/

/-- **The round trip of `FormalSpectrum.refinedOverlapTransition_trans_symm` read at a transition
family, with the two spelling bridges in it.** A datum carries its coarse transitions as a family
`τ`, so the transition at the swapped pair is `τ_ji` — a datum field — while
`FormalSpectrum.refinedOverlapTransition`'s target is spelled at *τ_ij⁻¹*. The two agree by the
datum's own symmetry law, which is the hypothesis `hs` here, but only propositionally, so a bridge
`CompletedTensorAwayInterchange.awayCongrEquivOfEq` sits after each of the two transitions and the
round trip is a **four**-fold composite rather than the two-fold one
`FormalSpectrum.refinedOverlapTransition_trans_symm` states.

**It is still that statement and no new content.** With `hs` substituted, the first bridge's two
sides are literally equal and the second's differ by *τ_ij⁻¹⁻¹* against *τ_ij*, which is `rfl` at
these completions; each bridge is therefore `AlgEquiv.refl` by `rfl`, and
`AlgEquiv.trans_trans_eq_refl_of_bridges` takes them out. Its docstring records why they are taken
out *there* and not here.

The two bridge equalities are hypotheses rather than consequences of `hs` spelled out in the
statement, because a caller has already written them — they are the same two equalities that pin
the refined chart's overlap element — and because it keeps a tactic block out of a statement that
`scripts/citation_audit.py` reads. -/
theorem refinedOverlapTransition_bridge_trans_eq_refl (hI : I.FG) (gij : Ai) (gji : Aj)
    (τij : awayCompletion (I.map (algebraMap R Ai)) gij ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) gji)
    (τji : awayCompletion (I.map (algebraMap R Aj)) gji ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ai)) gij)
    (hs : τji = τij.symm) (h : Ai) (h' : Aj)
    (hj : h' * refinedOverlapElt I hI gji gij τij.symm h' h
      = h' * refinedOverlapElt I hI gji gij τji h' h)
    (hi : h * refinedOverlapElt I hI gij gji τji.symm h h'
      = h * refinedOverlapElt I hI gij gji τij h h') :
    ((refinedOverlapTransition I hI gij gji τij h h').trans (awayCongrEquivOfEq I hj)).trans
        ((refinedOverlapTransition I hI gji gij τji h' h).trans (awayCongrEquivOfEq I hi))
      = AlgEquiv.refl := by
  subst hs
  exact AlgEquiv.trans_trans_eq_refl_of_bridges _ _ _ _ rfl rfl
    (refinedOverlapTransition_trans_symm I hI gij gji τij h h')

/-- **The refined datum's `τ_symm` field.**
`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData` asks for `τ j i = (τ i j).symm` at the
refined index, where its `τ` field is
`FormalSpectrum.refinedOverlapTransition` conjugated by the identification that presents each
refined chart `A_i{1/(h · e_ij)}` as a completed localization of the chart algebra `A_i{1/h}` above
it. That conjugation is this statement, with the identification left as an arbitrary `R`-algebra
equivalence `Mi`, `Mj` out of the refined presentation: a caller supplies
`FormalSpectrum.awayCompletionNestedAlgEquivOfLe` and nothing here needs to know that.

**`AlgebraicGeometry.BasicOpenCover.tau_symm_conj` is not used and its shape mismatch is not an
obstacle after all.** That lemma — the one-chart tower's conjugation, issue 2198 §5's route — is
stated for a *three*-fold composite, while a datum's refined field is four-fold because the
spelling bridge sits inside it; issue 2198 §5 recorded that as the open question and asked whether
the outer-steps-cancel argument of `FormalSpectrum.refinedOverlapTransition_symm` applies one level
up. **It does**, and that is the whole content of this proof: the swapped conjugate opens with the
identification this one closes with, so `AlgEquiv.symm_trans_symm_of_middle_eq_refl` cancels the
two without any naturality statement about them, and the middle is
`FormalSpectrum.refinedOverlapTransition_bridge_trans_eq_refl`. So this costs nothing of
`FormalSchemes.BasicOpenCoverCharts`'s 160 s-per-lemma naturality, which the `hστ` field still
owes. -/
theorem refinedOverlapTransition_conj_symm (hI : I.FG) (gij : Ai) (gji : Aj)
    (τij : awayCompletion (I.map (algebraMap R Ai)) gij ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) gji)
    (τji : awayCompletion (I.map (algebraMap R Aj)) gji ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ai)) gij)
    (hs : τji = τij.symm) (h : Ai) (h' : Aj)
    (hj : h' * refinedOverlapElt I hI gji gij τij.symm h' h
      = h' * refinedOverlapElt I hI gji gij τji h' h)
    (hi : h * refinedOverlapElt I hI gij gji τji.symm h h'
      = h * refinedOverlapElt I hI gij gji τij h h')
    {Xi Xj : Type u} [CommRing Xi] [CommRing Xj] [Algebra R Xi] [Algebra R Xj]
    (Mi : awayCompletion (I.map (algebraMap R Ai))
      (h * refinedOverlapElt I hI gij gji τij h h') ≃ₐ[R] Xi)
    (Mj : awayCompletion (I.map (algebraMap R Aj))
      (h' * refinedOverlapElt I hI gji gij τji h' h) ≃ₐ[R] Xj) :
    (Mj.symm.trans (refinedOverlapTransition I hI gji gij τji h' h)).trans
        ((awayCongrEquivOfEq I hi).trans Mi)
      = (((Mi.symm.trans (refinedOverlapTransition I hI gij gji τij h h')).trans
          ((awayCongrEquivOfEq I hj).trans Mj)) : Xi ≃ₐ[R] Xj).symm :=
  AlgEquiv.symm_trans_symm_of_middle_eq_refl _ _ _ _ _ _
    (refinedOverlapTransition_bridge_trans_eq_refl I hI gij gji τij τji hs h h' hj hi)

end FormalSpectrum

end
