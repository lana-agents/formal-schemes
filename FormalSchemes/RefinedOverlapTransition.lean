import FormalSchemes.AwayBaseChangeTopFiniteType
import FormalSchemes.AwayCompletionAlgHomBasicOpen
import FormalSchemes.AwayCompletionCongrEquiv
import FormalSchemes.AwayCompletionUniversal
import FormalSchemes.CompletedTensorAwayInterchangePullbackLegs
import FormalSchemes.RefinedOverlapRestrict

set_option linter.style.header false

/-!
# The refined overlap's cross-chart transition and its triple-overlap equivalence

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

**At an ordered *triple* of refined charts the same refinement needs one more piece of algebra
data**, the `σ` field of `AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData`: an `R`-algebra
equivalence

```
A_i{1/((h · e_ij) · (h · e_ik))}  ≃ₐ[R]  A_j{1/((h' · e_jk) · (h' · e_ji))}
```

between the two readings of one refined triple overlap, sitting over the coarse
`σ_ijk : A_i{1/(g_ij · g_ik)} ≃ₐ[R] A_j{1/(g_jk · g_ji)}`. That is
`FormalSpectrum.refinedOverlapSigma`, in the second half of this module, by the same four-step
route with `FormalSpectrum.basicOpen_sigma_refinedTripleOverlap` — the **triple chart-match** — in
place of the double chart-match at the third step.

**It is a composite of statements this tree already has, and it is not a descent statement.** That
distinction is the whole reason the transition half of this module is short: the span

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
* `FormalSpectrum.basicOpen_sigma_refinedTripleOverlap`: the **triple chart-match** — inside
  `Spf (A_j{1/(g_jk · g_ji)})` the *σ_ijk*-image of the *i*-side refined triple overlap is the
  *j*-side one. This is the third step's hypothesis at the triple, it is the only statement in the
  second half with content, and the section on it says what its crux actually is.
* `FormalSpectrum.sigma_furtherLocSnd_transition_symm`: that crux, isolated — the *k*-chart section
  transported into the triple overlap through chart *i* and through chart *j* is the **same
  section**. It consumes `hστ` at the two *permuted* triples and the cocycle, and not `hστ` at the
  unpermuted one.
* `FormalSpectrum.refinedOverlapSigma`: the equivalence itself, and the refined datum's `σ` field
  once a caller conjugates it by the presentation of each refined chart.
* `FormalSpectrum.refinedOverlapSigma_trans₃_eq_refl`: the **refined datum's `hσc` field** — the
  three rotations of one ordered triple compose to the identity. It asks a caller for nothing the
  `σ` field did not already ask for, and the section on it says why the argument that made the
  symmetry law cheap transfers to a cycle of three after all.
* `FormalSpectrum.awayCompletionAlgEquivOfBase_congr_trans₃_eq_refl`: the one statement with
  content in the proof of the cocycle, and the three-fold form of the symmetry law's own — base
  change and a basic-open re-presentation, three times round a cycle, compose to the identity as
  soon as the coarse `σ`s do.
* `AlgEquiv.trans₃_eq_refl_of_middle_eq_refl` and `AlgEquiv.trans₃_eq_refl_rotate`: the
  bookkeeping that carries that statement out to the datum's field, and the rotation of a coarse
  cocycle that its three instances need.
* `FormalSpectrum.SigmaIntertwinesLegs`: `hστ` at one ordered triple, so that the statements above
  quantify over a triple of coarse transitions and a triple of coarse `σ`s rather than over a
  datum.
* `FormalSpectrum.basicOpen_eq_top_of_factorwise_match`: the **refutation** of the factorwise
  reading of the triple chart-match, which is why that statement is an identity of meets.
* `FormalSpectrum.basicOpen_awayCompletionAlgHom_congr` and
  `FormalSpectrum.basicOpen_awayCompletionAlgHom_inf`: the preimage statement of
  `FormalSchemes.AwayCompletionAlgHomBasicOpen` read forwards, at an equality and at a meet.
* `FormalSpectrum.furtherLocFst_nestedOfLe` and
  `FormalSpectrum.furtherLocSnd_nestedOfLe`: the identification that presents a refined chart
  commutes with each further-localization leg — the naturality `hστ` at the refined index waits on,
  at the containment this file's charts actually have rather than at the uncompleted unit
  `FormalSchemes.AwayCompletionNestedNaturality` is keyed on.
* `FormalSpectrum.algHom_eq_of_algebraMap`: the rigidity those two are proved by, at two
  independent ambients, and the section on it records what packaging it this way is worth.
* `FormalSpectrum.awayCompletionNestedAlgEquivOfLe_algebraMap`,
  `FormalSpectrum.awayCompletionChartAlgEquivOfLe_algebraMap` and
  `CompletedTensorAwayInterchange.awayCongrEquivOfEq_algebraMap`: each step of those squares fixes
  the structural image of the base ring, which is the only thing the rigidity consumes.

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

## The triple chart-match, and the two things about it that are not the obvious ones

`FormalSpectrum.basicOpen_sigma_refinedTripleOverlap` is the three-chart analogue of
`FormalSpectrum.basicOpen_awayCompletionAlgEquiv_mul_refinedOverlapElt`, and it is what the third
step of the route asks for at a triple. Both sides of it are a product of two factors — the
*i*-side one is `(h · e_ij) · (h · e_ik)` and the *j*-side one is `(h' · e_jk) · (h' · e_ji)` — and
two readings of that suggest themselves. **Both are wrong, and each is wrong in its own way.**

**The factorwise reading is not merely unproved, it is refutable.** Matching the *(i, j)* factor
against the *(j, i)* factor is a theorem — `FormalSpectrum.basicOpen_sigma_refinedOverlapElt_ij`,
and `hστ` at the unpermuted triple `(i, j, k)` is exactly what answers it. Matching the two
remaining factors is **false**: `FormalSpectrum.basicOpen_sigma_refinedOverlapElt_ik` cuts the
*(i, k)* factor down to `D(ĥ) ⊓ D(ĥ'')` and `FormalSpectrum.basicOpen_refinedOverlapElt_jk` cuts
the *(j, k)* factor down to `D(ĥ') ⊓ D(ĥ'')`, and asserting those equal forces, at `h' = 1` and
`h'' = 1`, that `D(τ_ij(ĥ))` is the whole space for **every** refining element `h`. That is
`FormalSpectrum.basicOpen_eq_top_of_factorwise_match`, and it is stated rather than described
because the factorwise reading is the one a reader reconstructs. So the chart match is an identity
of **meets** — the last step of its proof is the lattice identity
`(a ⊓ b) ⊓ (b ⊓ c) = (a ⊓ c) ⊓ (a ⊓ b)`, both sides `a ⊓ b ⊓ c`.

**The content is an equality of *elements*, not of opens.** Once the two sides are resolved into
the three refining elements, everything cancels except one thing: the *k*-chart section read into
the triple overlap through chart *i* and read into it through chart *j* has to be the **same
section**. That is `FormalSpectrum.sigma_furtherLocSnd_transition_symm`, it is three rewrites long,
and what it consumes is the surprise — `hστ` at `(k, i, j)` and at `(j, k, i)`, and the **cocycle**
`hσc` at `(i, j, k)`. `hστ` at `(i, j, k)` is not among them and cannot be: that hypothesis is
spent, in full, on the *(i, j)* factor. A triple-overlap statement at this layer therefore needs
the coarse datum's laws at all three rotations of the triple, and a scout that budgets only the
unpermuted one has under-counted.

**Neither half needs a naturality statement and neither carries a `set_option`.** Everything above
is `rw` and `simp only` at the *coarse* charts, below all four nested identifications, which is
what keeps the ~160 s-a-lemma cost `FormalSchemes.BasicOpenCoverCharts` records off this file for
a second time. The two general transport steps that do the work,
`FormalSpectrum.basicOpen_awayCompletionAlgHom_congr` and
`FormalSpectrum.basicOpen_awayCompletionAlgHom_inf`, are
`FormalSpectrum.preimage_basicOpen_awayCompletionAlgHom` read forwards, at an equality and at a
meet.

## The hypotheses are taken at a triple, and that is what leaves the totalising question open

`FormalSpectrum.SigmaIntertwinesLegs` is `hστ` at one ordered triple, written with its transition
in the direction that occurs in the statement — *out of* the target chart's overlap rather than
into it. That spelling is chosen so that a datum's own field is this predicate **on the nose** at
the unpermuted triple, and one `AlgEquiv.symm_symm` away from it at the two permuted ones, after
the datum's `τ_symm`; taking the transition the other way round moves the same `AlgEquiv.symm_symm`
into the proofs here instead, where it would be paid three times rather than twice.

**So nothing in the second half knows about a datum**, exactly as in the first: the six overlap
elements, the three coarse transitions and the three coarse `σ`s are independent arguments, and
the three instances of `hστ` and the cocycle are hypotheses. Producing them from a family defined
at every ordered pair and triple — the diagonal included, where a coarse datum supplies no overlap
element — is issue 2198 §6.3, and this module does not touch it.

## The naturality the refined `hστ` waits on, and the 416 s that is not where it looks

The two squares of `FormalSpectrum.furtherLocFst_nestedOfLe` and
`FormalSpectrum.furtherLocSnd_nestedOfLe` say that presenting a refined chart over the coarse
chart above it commutes with each of the two further-localization legs
`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData` states `hστ` with. Both are needed and
neither follows from the other: that obligation has its first leg over one chart algebra and its
second over another, and the only thing joining them is the coarse law.

**They are not instances of `FormalSpectrum.awayCongrHom_nested`**
(`FormalSchemes.AwayCompletionNestedNaturality`), and the reason is the one this file's first step
is built around. That square is keyed on `IsUnit (algebraMap B (Localization.Away u) f)`, a
statement in the **uncompleted** localization; the refined presentation has `f := g_ij` and
supplies only `FormalSpectrum.basicOpen_refinedOverlapElt_le`, the containment in `Spf (B, I·B)`,
which is strictly weaker. Its proof does not transfer either: it collapses both legs to a single
`AdicCompletion.mapCompletion` and applies
`AdicCompletion.mapCompletion_congr_localizationAway`, and
`FormalSpectrum.awayCompletionChartEquivOfLe` is not built as an `AdicCompletion.mapCompletion`.

What replaces that route is rigidity, and it is shorter: every step of both squares fixes the
structural image of the base ring, so
`FormalSpectrum.algHom_eq_of_algebraMap` closes each of them in one rewrite chain.

**The cost is in the kernel, and packaging the rigidity at abstract carriers removes all of it.**
Proved by applying `FormalSpectrum.awayCompletion_hom_ext'`
(`FormalSchemes.AwayCompletionRestrictUnique`) directly at the doubly nested completion, the first
square costs **416 s** — and the profiler attributes **1.19 s** of that to tactic execution and the
rest to `type checking`, so it is the kernel reducing the nested carrier while it checks the
application, not the elaborator. Factored through `FormalSpectrum.algHom_eq_of_algebraMap`, whose
two ambients stay abstract, the six declarations of that section elaborate and check together in
about **10 s**. Two things follow and both are general: `FormalSchemes.BasicOpenCoverCharts`'s
*state it abstractly* note is about the kernel and not about elaboration, and the figure to read on
a statement at these completions is `type checking took`, which `set_option profiler true` prints
and which no heartbeat budget reports.

**What `hστ` still owes after these two, measured rather than predicted.** Issue 2198 §5 names
`AlgebraicGeometry.BasicOpenCover.sigma_tau_conj` as this field's supplier. It cannot be, and the
mismatch is structural rather than incidental: that lemma conjugates by `N₁`, `N₂` landing in one
chart algebra `A₁`, whereas the refined transition is presented over `A_i{1/g_ij}` and the refined
`σ` over `A_i{1/(g_ij · g_ik)}` — two different chart algebras at the same index. So the square
still missing is a **cross-chart** one, comparing the two presentations of `A_i{1/(h · e_ij)}`
along `CompletedTensorAwayInterchange.furtherLocFst` downstairs, and it is not the fixed-chart
square §6.2 describes. The two here are the fixed-chart half and are what that comparison will be
stated against.

## Placement

A leaf over `FormalSchemes.RefinedOverlapRestrict`, `FormalSchemes.AwayCompletionAlgHomBasicOpen`,
`FormalSchemes.AwayCompletionCongrEquiv`, `FormalSchemes.AwayBaseChangeTopFiniteType`,
`FormalSchemes.AwayCompletionUniversal` and
`FormalSchemes.CompletedTensorAwayInterchangePullbackLegs`: the forward closure of
`FormalSchemes.RefinedOverlapTransition` is **71** project modules besides itself (72 counted with
itself), and the reverse closure of `FormalSchemes.RefinedOverlapTransition` is **0**.

**A new module was forced for the transition, and that was measured rather than argued.** No
module of this tree reaches all six of the above — the best any of the other 586 does is **three**,
and only 4 of them manage that: **416** reach none, **146** reach exactly one and **20** reach two.
(*Reaches* here counts a module as reaching itself, since a declaration placed in a file has that
file's own contents; the closure convention of this section, which does not, gives 420 / 144 / 18 /
4.) So the *put it in a file that already imports enough* option does not exist, and the
alternative is an import into an existing file, which is the expensive direction.
`FormalSchemes.RefinedOverlapRestrict` is the closest candidate and reaches **41**, and it is
missing five of the six: the edges to `FormalSchemes.AwayCompletionAlgHomBasicOpen`,
`FormalSchemes.CompletedTensorAwayInterchangePullbackLegs`,
`FormalSchemes.AwayCompletionCongrEquiv`, `FormalSchemes.AwayBaseChangeTopFiniteType` and
`FormalSchemes.AwayCompletionUniversal` cost **+6**, **+11**, **+12**, **+15** and **+16** modules
there, and every consumer that file ever gains would inherit them.

**Two of the six imports are free in closure terms and both are kept anyway.**
`FormalSchemes.AwayBaseChangeTopFiniteType` lies inside `FormalSchemes.AwayCompletionUniversal`'s
forward closure of **55** — that module imports it on its first line — and
`FormalSchemes.CompletedTensorAwayInterchangePullbackLegs` lies inside
`FormalSchemes.AwayCompletionCongrEquiv`'s of **38**, so dropping either import line would leave
the 71 above unchanged. Both are kept because `FormalSpectrum.awayCompletionAlgEquivOfBase` and
`CompletedTensorAwayInterchange.furtherLocFst` are used here directly, which is this tree's
practice and not a departure from it: **140** of the **587** modules under `FormalSchemes/` carry
an import some other import of the same file already reaches, this one included. Counting only
what each import brings that no other of the six reaches, the split is **6** for
`FormalSchemes.AwayCompletionAlgHomBasicOpen`, **2** for
`FormalSchemes.RefinedOverlapRestrict`, **1** each for
`FormalSchemes.AwayCompletionCongrEquiv` and `FormalSchemes.AwayCompletionUniversal`, and **0**
for the two free ones; the remaining 61 of the 71 are reached by more than one of them. **The
sixth import is what moved that split**, and it is worth naming as the general fact: it took
`FormalSchemes.AwayCompletionCongrEquiv`'s unique contribution from **7** to **1**, because six of
that module's seven are inside the sixth import's own closure. *A free import can still change
what every other import of the same file is buying.*

**The fifth import is the conjugated symmetry law's, and it was priced before it was written.**
`CompletedTensorAwayInterchange.awayCongrEquivOfEq` is the only transport along an equality of away
elements on this tree — one `git grep` over `FormalSchemes/` finds exactly one declaration built by
matching on `rfl` — and a datum's `τ_symm` field cannot be stated without it, so the alternatives
were this edge or a new module over this one. `scripts/closure_audit.py --edge` prices the edge at
**7** modules and **3** figure repairs in **2** files, against the **37** in **17** that adding
this module cost; this file's reverse closure of **0** is what makes that comparison lopsided, and
the same edge at a file with consumers would not be.

**The sixth import is the triple overlap's, and it is the reason the second half is in this file
rather than in a module over it.** `CompletedTensorAwayInterchange.furtherLocFst` and
`CompletedTensorAwayInterchange.furtherLocSnd` are the two legs
`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData` states `hστ` with, so nothing about a
refined `σ` can be said without reaching
`FormalSchemes.CompletedTensorAwayInterchangePullbackLegs`, and the choice was that edge or a
module over this one. `scripts/closure_audit.py --edge` prices the edge at **0** modules brought
in, and reports that it moves no forward closure, no reverse closure and no quoted figure anywhere
on the tree — that module is already inside this file's 71, through
`FormalSchemes.AwayCompletionCongrEquiv`. The module was priced the way CONTRIBUTING.md's *What
adding a module costs* says to, by writing the file and running `--tree` against it, and the stub
is `import FormalSchemes.RefinedOverlapTransition` and nothing else — a module *over* this one,
not a sibling repeating this file's six imports, which is a different and cheaper experiment at
**40**. Over this one it is **44** figure repairs in **18** files, whose union re-elaborates
**540** of the **588** modules that tree would have, **81** of them without
`FormalSchemes/StructureSheaf.lean`. The **44** is `--tree`'s own header count and it counts
*figures*, so it is one more than the **43** distinct positions the report prints, one of which
carries two; the **540** and the **81** are counted with the stub on the tree, because the new
module has to be elaborated too, and without it the same two are **539** and **80**. So the
comparison here is **0 against 44**, the widest this file has seen, and it is not close.

**What the module costs is the figure sweep, not the build.** Adding any module under
`FormalSchemes/` falsifies every absolute *reverse*-closure figure quoted about anything it imports
— CONTRIBUTING.md's *What adding a module costs* is the standing account — and here that is **37**
numerals in **17** files, every one of them a `+1`. Editing those 17 re-elaborates **539** of the
587 modules, and the concentration is the same one CONTRIBUTING.md records: the reverse closure of
`FormalSchemes.StructureSheaf` is **530**, and dropping that one file from the 17 takes the sweep's
rebuild to **80**. Two of the 37 are not renumberings:
`FormalSchemes/RefinedOverlapRestrict.lean` and
`FormalSchemes/AwayCompletionAlgHomBasicOpen.lean` each state that they are **leaves**, and this
module is their first consumer, so both `## Placement` paragraphs are rewritten rather than
renumbered — in the first case because the ratio it declines a move on was argued from a *single
call site*, and this module is the second.

This paragraph's counts are measurements of the diff that added this file, at the base it was taken
at; they are not standing claims about any later tree and nothing re-runs them — except the **530**,
which `--tree` attributes and checks as a claim in its own right, so that one numeral is renumbered
with the tree while the **37**, the **17** and the two union figures beside it are not. Re-measure
with `scripts/closure_audit.py --tree`, and price any sixth import with `--edge` before writing a
word about it.

**Sixteen of the statements below are general and all sixteen are kept here, and the decisive one
is decided by a walk rather than by taste.** This paragraph said *seven* until this diff, and it
was already wrong before it: the count was right when #808 and #809 wrote it and stale from #816,
which added two `AlgEquiv` lemmas and a second base-change round trip without touching either
numeral. The count is `git grep`-able — six under `namespace AlgEquiv`, two
`FormalSpectrum.awayCompletionAlgEquivOfBase_congr_trans…`, two
`FormalSpectrum.basicOpen_awayCompletionAlgHom_…`, and this diff's six — and the general lesson is
the one issue 2211 was filed for: **the declarations a file lists as *general and kept local* are
the ones its author already thought about, so a stale count is the cheapest tell that a later diff
added one nobody re-costed.**
`FormalSpectrum.awayCompletionAlgEquivOfBase_congr_trans_eq_refl` is general in both its chart
algebras and names nothing of the refined overlap, so its subject-matter home is beside the base
change it is about. It cannot go there: it needs
`FormalSchemes.AwayBaseChangeTopFiniteType`, `FormalSchemes.AwayCompletionRestrictUnique` and
`FormalSchemes.AwayCompletionAlgHomBasicOpen` at once, and **this module is the only one of the 587
that reaches all three** — 546 reach none of them, 35 reach exactly one, 5 reach two and this file
is the one that reaches three. So its only homes besides this file are a new module over this one
or an import into an existing one, and this section prices the second.
`FormalSpectrum.awayCompletionAlgEquivOfBase_congr_trans₃_eq_refl` is the same statement at a
cycle of three and is kept beside it, on the same walk.
The six `AlgEquiv` lemmas name nothing of this tree at all — they are statements about
`AlgEquiv.trans` and `AlgEquiv.symm`, and Mathlib is where they belong, which is why all six are
stated at `CommSemiring` and `Semiring` with their carriers in independent universes rather
than at this file's own `CommRing` and `Type u`: their proofs use nothing else, and a statement
offered to Mathlib on that argument should carry Mathlib's hypotheses. The nearest thing to a
subject-matter home here is an early module about algebra equivalences, and of those
`FormalSchemes.AdicCompletionCongrIdealAlg` is the cheapest, at a reverse closure of **196**
against this file's **0**, with one call site each. Declined on that ratio, which is this tree's
standing disposition for a general statement with a single call site.
`FormalSpectrum.basicOpen_awayCompletionAlgHom_congr` and
`FormalSpectrum.basicOpen_awayCompletionAlgHom_inf` are the two where that argument is **weakest
and is stated as such**: their subject-matter home is exact —
`FormalSchemes.AwayCompletionAlgHomBasicOpen`, whose own preimage statement they are — and they
elaborate there, measured, in **2.9 s** against that module alone, so the move is available and
not merely conjectured. The reverse closure of `FormalSchemes.AwayCompletionAlgHomBasicOpen` is
**1**, this file, so the move would cost a one-module re-elaboration rather than the 196 above.
They are kept here on the single-call-site half of the disposition alone, and **that is the one to
revisit first** when anything else on this tree wants a basic open transported along a map of
completed localizations. **The six this diff adds are the ones with the clearest subject-matter
home and the clearest price, and both were measured before they were written here.**
`FormalSpectrum.algHom_eq_of_algebraMap`,
`FormalSpectrum.awayCompletionChartAlgEquivOfLe_algebraMap`,
`FormalSpectrum.awayCompletionNestedAlgEquivOfLe_algebraMap`,
`FormalSpectrum.furtherLocFst_nestedOfLe`, `FormalSpectrum.furtherLocSnd_nestedOfLe` and
`CompletedTensorAwayInterchange.awayCongrEquivOfEq_algebraMap` say nothing about a refined overlap;
`FormalSchemes.AwayCompletionNestedNaturality` is their subject-matter home by name, and its own
docstring says it exists for a datum's `hστ`. It does not reach
`FormalSchemes.AwayCompletionUniversal`, where the *OfLe* identification lives, and
`scripts/closure_audit.py --edge` prices that import at **13** figure repairs in **8** files,
against **0** here — this file needs no new import for any of the six, both modules being already
among its own. `closure_audit --edge` prices a later edge from this file to that one — which is
what moving them would also cost — at **5** figure repairs in **3** files. So the disposition is
*keep, and move them together with the cross-chart square when it exists*, since that square will
want the same imports and the two edges should be paid once.
`CompletedTensorAwayInterchange.awayCongrEquivOfEq_algebraMap` is the one with a closer home than
that: its two siblings
`CompletedTensorAwayInterchange.awayCongrHom_algebraMap` and
`CompletedTensorAwayInterchange.awayCongrEquiv_algebraMap` are `FormalSchemes.AwayCongrAlgebraMap`,
a file whose whole subject is that these maps fix the base and whose own docstring says it exists
so that leaves can import it; `--edge` prices that import at **4** figure repairs in **2** files,
all four of them this file's forward closure of **71** going to **72** or its *counted with itself*
companion. **One of the four is the figure in this very sentence**, which is why a price for an
edge out of the file you are editing has to be measured at your own head and after the docstring
line that quotes it: at the base it comes out one short, and that is how the **3** this sentence
used to say got here. It is declined here only because this diff adds no import at all, and it is
the first one to revisit. **That module is also
why the third of these lemmas is the transport and not the comparison map**: the first draft proved
the squares through `CompletedTensorAwayInterchange.awayCongrHom` and restated
`CompletedTensorAwayInterchange.awayCongrHom_algebraMap` locally, which is a **duplicate** of an
existing declaration and compiled only because that file is outside this one's imports. The tell
was arithmetic: `scripts/option_reference_audit.py --tree` reported **+5** declarations against a
`git grep` of the file's own `+6`, because it keys on the fully qualified name. **Re-cost all
sixteen when a consumer appears that does not reach this file**; a consumer inside this file's own
subtree buys nothing, for the reason `FormalSchemes/RefinedOverlapRestrict.lean`'s `## Placement`
gives at `FormalSpectrum.basicOpen_mul_le_of_basicOpen_le`.

## What is *not* proved here

**The refined datum itself, and the law `hστ` at the refined index.**
`FormalSpectrum.refinedOverlapTransition_conj_symm`, `FormalSpectrum.refinedOverlapSigma` and
`FormalSpectrum.refinedOverlapSigma_trans₃_eq_refl` are three of the fields
`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData` asks for at that index, and nothing here
takes the smart constructor's remaining arguments; no
`AlgebraicGeometry.AffineChartedFibreDatumX` is built anywhere on this tree from a refined chart
family. Fed slot 0's scouting instantiation on issue 2198 — with the refined `σ` conjugated by the
nested identification at the triple, which is a caller's three lines and not a statement here —
the three of them close the `τ_symm`, `σ` and `hσc` arguments and leave **`hστ` alone**.

**The refined `σ`'s compatibility with the refined transition.**
`FormalSpectrum.refinedOverlapSigma` is a four-step composite exactly as
`FormalSpectrum.refinedOverlapTransition` is, and its **cocycle** is now stated —
`FormalSpectrum.refinedOverlapSigma_trans₃_eq_refl` — but its compatibility with the refined
transition, the `hστ` of the refined index, is not. That one is the field whose two legs are over
*different* ambients, so the outer identifications do not cancel and a naturality statement about
`FormalSpectrum.awayCompletionNestedAlgEquivOfLe` really is wanted.

**Two thirds of that naturality is now here and the remaining third is named.**
`FormalSpectrum.furtherLocFst_nestedOfLe` and `FormalSpectrum.furtherLocSnd_nestedOfLe` are
the two squares at a **fixed** coarse chart, and the section above prices them at nothing once the
rigidity is packaged. What is still owed is the **cross-chart** square: the refined transition
presents `A_i{1/(h · e_ij)}` over `A_i{1/g_ij}` and the refined `σ` presents
`A_i{1/((h · e_ij) · (h · e_ik))}` over `A_i{1/(g_ij · g_ik)}`, and `hστ` compares the two, so the
comparison downstairs is `CompletedTensorAwayInterchange.furtherLocFst` at the *coarse* elements
and not the identity. That is also why
`AlgebraicGeometry.BasicOpenCover.sigma_tau_conj` — issue 2198 §5's named supplier for this field —
cannot be it: that lemma's `N₁` and `N₂` land in **one** chart algebra `A₁`, and here they land in
two. Neither this file nor `FormalSchemes.BasicOpenCoverTransitions` states the cross-chart square,
and it is unpriced.

**A prediction this module made about the cocycle was wrong, and it is corrected rather than
deleted.** An earlier reading of this section said the outer-steps-cancel argument *"does not
obviously transfer, because a triple's three nested identifications are at three different charts
and do not pair off"*. They pair off. Each rotation closes with the inverse of the identification
the next one opens with, so a cycle of three cancels two pairs internally and leaves the third as
the outside — the same shape as the two-fold law, not a new one. The measurement is in
`AlgEquiv.trans₃_eq_refl_of_middle_eq_refl`'s docstring and the field's proof is one term. **Three
charts is three pairs, one of which is the outside**, and that is the sentence the earlier reading
was missing.

**The refining elements are arbitrary here, and a datum's are not.** Every statement in both
halves quantifies over `h`, `h'`, `h''` and over the coarse transitions and the coarse `σ`s
independently, with the datum's symmetry law and its two triple laws supplied as hypotheses.
Producing those from families defined at every ordered pair and triple — including the diagonal,
where a coarse datum supplies no overlap element — is issue 2198 §6.3 and is not priced here.

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
variable {Z P'' W : Type*} [Semiring Z] [Semiring P''] [Semiring W]
  [Algebra R Z] [Algebra R P''] [Algebra R W]

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

/-- **A three-fold composite that is the identity stays the identity when its cycle is rotated.**
`a ≫ b ≫ c = id` gives `b ≫ c ≫ a = id`, at three carriers with no relation between them.

Stated because the refined cocycle is a statement about *one* ordered triple, while
`FormalSpectrum.refinedOverlapSigma` asks for the coarse cocycle at the triple it is instantiated
at: the rotated instances of that definition need the rotated coarse cocycle, and nothing else in
their argument lists has to move. Two applications reach the third rotation. -/
theorem trans₃_eq_refl_rotate (a : X ≃ₐ[R] P) (b : P ≃ₐ[R] Q) (c : Q ≃ₐ[R] X)
    (h : a.trans (b.trans c) = AlgEquiv.refl) :
    (b.trans (c.trans a) : P ≃ₐ[R] P) = AlgEquiv.refl := by
  refine AlgEquiv.ext fun q => ?_
  have hx := DFunLike.congr_fun h (a.symm q)
  simp only [AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply, AlgEquiv.coe_refl, id_eq] at hx
  simp only [AlgEquiv.trans_apply, AlgEquiv.coe_refl, id_eq]
  rw [hx]
  exact a.apply_symm_apply q

/-- **Three four-step composites arranged in a cycle compose to the identity as soon as their
middles do.** The three-fold analogue of `AlgEquiv.trans_trans_eq_refl_of_middle_eq_refl`, at the
same shape and with the same three-line proof.

**The outer identifications pair off, and that is the finding rather than the statement.** This
module's `## What is *not* proved here` said of the refined cocycle that *"the
outer-steps-cancel argument that made the symmetry law cheap twice does not obviously transfer,
because a triple's three nested identifications are at three different charts and do not pair
off"*. They do. Each composite *closes* with the inverse of the identification the next one
*opens* with — `Nj⁻¹` then `Nj`, `Nk⁻¹` then `Nk` — so the cycle cancels them in adjacent pairs
exactly as the two-fold case cancels its one pair, and only `Ni` and `Ni⁻¹` survive, at the ends.
Three charts is not three unpaired identifications; it is three pairs, one of which is the outside.

As with the two-fold lemma the six steps of each composite are separate arguments and the middles
are not packaged: at the doubly nested completions
`FormalSpectrum.refinedOverlapSigma_trans₃_eq_refl` applies this to, re-associating a packaged
middle is the `(deterministic) timeout at whnf` that section records. -/
theorem trans₃_eq_refl_of_middle_eq_refl
    (Ni : X ≃ₐ[R] P) (B : P ≃ₐ[R] Q) (C : Q ≃ₐ[R] Q') (Nj : Y ≃ₐ[R] Q')
    (B' : Q' ≃ₐ[R] P') (C' : P' ≃ₐ[R] P'') (Nk : Z ≃ₐ[R] P'')
    (B'' : P'' ≃ₐ[R] W) (C'' : W ≃ₐ[R] P)
    (hmid : (B.trans C).trans ((B'.trans C').trans (B''.trans C'')) = AlgEquiv.refl) :
    (((Ni.trans B).trans (C.trans Nj.symm)).trans
        (((Nj.trans B').trans (C'.trans Nk.symm)).trans
          ((Nk.trans B'').trans (C''.trans Ni.symm))) : X ≃ₐ[R] X) = AlgEquiv.refl := by
  refine AlgEquiv.ext fun x => ?_
  have hx := DFunLike.congr_fun hmid (Ni x)
  simp only [AlgEquiv.trans_apply, AlgEquiv.coe_refl, id_eq] at hx
  simp only [AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply, AlgEquiv.coe_refl, id_eq, hx,
    AlgEquiv.symm_apply_apply]

end AlgEquiv

namespace CompletedTensorAwayInterchange

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- **The transport along an equality of away elements fixes the base ring.**
`CompletedTensorAwayInterchange.awayCongrEquivOfEq` is built by matching on `rfl`, so this is
`rfl` after a `subst` and the statement is the whole of it; it is stated because a rigidity
argument reads a composite one step at a time and this is the step that would otherwise have to be
unfolded inside a doubly nested completion. The companion facts for
`CompletedTensorAwayInterchange.awayCongrHom` and
`CompletedTensorAwayInterchange.awayCongrEquiv` are
`FormalSchemes.AwayCongrAlgebraMap`'s, and this one belongs beside them; see this module's
`## Placement`. -/
theorem awayCongrEquivOfEq_algebraMap {A : Type u} [CommRing A] [Algebra R A] {x y : A}
    (h : x = y) (a : A) :
    awayCongrEquivOfEq I h
        (algebraMap A (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) x) a) =
      algebraMap A (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) y) a := by
  subst h
  rfl

end CompletedTensorAwayInterchange

open CompletedTensorAwayInterchange

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {Ai Aj : Type u} [CommRing Ai] [CommRing Aj] [Algebra R Ai] [Algebra R Aj]

/-! ### Rigidity at two ambients, and the identification at a containment against the legs -/

section NestedOfLeLegs

variable {B : Type u} [CommRing B] [Algebra R B]

/-- **Two `R`-algebra maps of completed localizations agree as soon as they agree on the structural
image of the source's base ring**, with the two base rings independent.

`FormalSpectrum.awayCompletion_hom_ext` (`FormalSchemes.AwayCompletionRestrictUnique`) is this at
one ambient, and the primed form there already allows an arbitrary complete target; what is packaged
here is the `R`-algebra shape, with the continuity of both maps discharged by
`FormalSpectrum.le_comap_awayCompletionIdeal_algHom` rather than asked for, and the
`IsAdicComplete` instance of the target produced rather than assumed.

**The packaging is the whole point and it is a cost, not a convenience.** Applying the rigidity
directly at a *doubly nested* completion — the shape the statements below are about — elaborates in
about a second and then costs **416 s of kernel time**, because the kernel reduces the nested
carrier while checking the application; the same proof factored through this lemma, whose carriers
`B` and `C` stay abstract, costs nothing measurable. That is
`FormalSchemes.BasicOpenCoverCharts`'s 368 s → 20 s note in its sharpest form, and the thing to
carry away is that the measurement to take is `type checking took`, not the elaborator's. -/
theorem algHom_eq_of_algebraMap {C : Type u} [CommRing C] [Algebra R C] (hI : I.FG)
    (u : B) (c : C)
    (F G : awayCompletion (I.map (algebraMap R B)) u →ₐ[R]
      awayCompletion (I.map (algebraMap R C)) c)
    (h : ∀ b : B, F (algebraMap B (awayCompletion (I.map (algebraMap R B)) u) b) =
      G (algebraMap B (awayCompletion (I.map (algebraMap R B)) u) b)) :
    F = G := by
  haveI : IsAdicComplete (awayCompletionIdeal (I.map (algebraMap R C)) c)
      (awayCompletion (I.map (algebraMap R C)) c) :=
    (AdicCompletion.isAdicRing_map _ ((hI.map _).map _)).toIsAdicComplete
  exact AlgHom.coe_ringHom_injective
    (awayCompletion_hom_ext' (I.map (algebraMap R B)) u (hI.map _)
      (le_comap_awayCompletionIdeal_algHom I u c F)
      (le_comap_awayCompletionIdeal_algHom I u c G)
      (RingHom.ext fun b => by
        rw [RingHom.comp_apply, RingHom.comp_apply, awayCompletionHom_eq_algebraMap]
        exact h b))

/-- **The `R`-algebra upgrade of the identification at a containment still fixes `B`**, which is
`FormalSpectrum.awayCompletionChartEquivOfLe_algebraMap` at the upgraded map — the *OfLe*
counterpart of `FormalSpectrum.awayCompletionChartAlgEquiv_algebraMap`. -/
theorem awayCompletionChartAlgEquivOfLe_algebraMap (hI : I.FG) (x y : B)
    (hle : basicOpen (I.map (algebraMap R B)) y ≤ basicOpen (I.map (algebraMap R B)) x) (b : B) :
    awayCompletionChartAlgEquivOfLe I hI x y hle
        (algebraMap B (awayCompletion (I.map (algebraMap R B)) y) b) =
      algebraMap B (awayCompletion (awayCompletionIdeal (I.map (algebraMap R B)) x)
        (awayCompletionHom (I.map (algebraMap R B)) x y)) b :=
  awayCompletionChartEquivOfLe_algebraMap (I.map (algebraMap R B)) x y (hI.map _) hle b

/-- **The identification a refined chart is presented by fixes the base ring.** The *OfLe*
counterpart of `FormalSpectrum.awayCompletionNestedAlgEquiv_algebraMap`
(`FormalSchemes.AwayCompletionNested`), and the statement issue 2198 §6.2 asks for first: it is the
`…_apply` fact that stops every later equation between doubly nested completions from having to
reduce the identification at all.

The transport contributes nothing, because `AdicCompletion.congrIdealₐ` is `subst`-built; the proof
is the strong version's with `FormalSpectrum.awayCompletionChartAlgEquivOfLe_algebraMap` in place
of `FormalSpectrum.awayCompletionChartAlgEquiv_algebraMap`. -/
theorem awayCompletionNestedAlgEquivOfLe_algebraMap (hI : I.FG) (x y : B)
    (hle : basicOpen (I.map (algebraMap R B)) y ≤ basicOpen (I.map (algebraMap R B)) x) (b : B) :
    awayCompletionNestedAlgEquivOfLe I hI x y hle
        (algebraMap B (awayCompletion (I.map (algebraMap R B)) y) b) =
      algebraMap B (awayCompletion (I.map (algebraMap R (awayCompletion
        (I.map (algebraMap R B)) x))) (awayCompletionHom (I.map (algebraMap R B)) x y)) b := by
  rw [awayCompletionNestedAlgEquivOfLe, AlgEquiv.trans_apply,
    awayCompletionChartAlgEquivOfLe_algebraMap,
    IsScalarTower.algebraMap_apply B
      (Localization.Away (awayCompletionHom (I.map (algebraMap R B)) x y))
      (awayCompletion (awayCompletionIdeal (I.map (algebraMap R B)) x)
        (awayCompletionHom (I.map (algebraMap R B)) x y)),
    AdicCompletion.congrIdealₐ_algebraMap, ← IsScalarTower.algebraMap_apply]

/-- **The naturality square, at a containment and at the first further-localization leg.** Reading
`B{1/u₁} ⟶ B{1/(u₁ · u₂)}` and then presenting the target over the chart `B{1/f}` is presenting the
source over that chart and then reading the corresponding leg inside it:

```
B{1/u₁}        --furtherLocFst-->   B{1/(u₁ · u₂)}
   |  N_{f, u₁}                        |  N_{f, u₁·u₂}
   v                                   v
B{1/f}{1/ū₁}   --furtherLocFst-->   B{1/f}{1/(ū₁ · ū₂)}
```

**The bridge in the corner is not avoidable and is why `hmul` is a hypothesis.** `N_{f, u₁·u₂}`
lands at `awayCompletionHom (I·B) f (u₁ · u₂)` and the upstairs leg lands at the product of the two
images, and those are equal by `map_mul` and not by `rfl`; taking the equality as an argument keeps
a `map_mul` out of the statement's own type, which is what lets a caller instantiate it without the
kernel reducing either side.

**This is `FormalSpectrum.awayCongrHom_nested` (`FormalSchemes.AwayCompletionNestedNaturality`) at
the containment the refined overlap actually has, and it is not an instance of it.** That square is
keyed on `IsUnit (algebraMap B (Localization.Away u₁) f)`, a statement in the *uncompleted*
localization; at the refined presentation the chart element is `f := g_ij` and all that is
available is `FormalSpectrum.basicOpen_refinedOverlapElt_le`, which is the containment in
`Spf (B, I·B)` and strictly weaker —
`FormalSchemes.AwayCompletionUniversal`'s own `## Placement` separates the two at `B = ℤ`,
`J = (2)`, `f = 3`, `g = 5`. Its proof does not transfer either: it collapses both legs to a single
`AdicCompletion.mapCompletion` and applies
`AdicCompletion.mapCompletion_congr_localizationAway`, and
`FormalSpectrum.awayCompletionChartEquivOfLe` is not built as an `AdicCompletion.mapCompletion`.

What replaces it is rigidity, and it is shorter: every step of both sides fixes the structural
image of `B` — `FormalSpectrum.awayCompletionNestedAlgEquivOfLe_algebraMap` for `N`,
`CompletedTensorAwayInterchange.furtherLocFst_algebraMap` for each leg and
`CompletedTensorAwayInterchange.awayCongrEquivOfEq_algebraMap` for the bridge — so
`FormalSpectrum.algHom_eq_of_algebraMap` closes it and nothing about the completion is reduced. -/
theorem furtherLocFst_nestedOfLe (hI : I.FG) (f u₁ u₂ : B)
    (h1 : basicOpen (I.map (algebraMap R B)) u₁ ≤ basicOpen (I.map (algebraMap R B)) f)
    (h12 : basicOpen (I.map (algebraMap R B)) (u₁ * u₂) ≤ basicOpen (I.map (algebraMap R B)) f)
    (hmul : awayCompletionHom (I.map (algebraMap R B)) f (u₁ * u₂) =
      awayCompletionHom (I.map (algebraMap R B)) f u₁ *
        awayCompletionHom (I.map (algebraMap R B)) f u₂) :
    (furtherLocFst I (awayCompletionHom (I.map (algebraMap R B)) f u₁)
          (awayCompletionHom (I.map (algebraMap R B)) f u₂) hI).comp
        (awayCompletionNestedAlgEquivOfLe I hI f u₁ h1).toAlgHom =
      ((awayCongrEquivOfEq I hmul).toAlgHom.comp
          (awayCompletionNestedAlgEquivOfLe I hI f (u₁ * u₂) h12).toAlgHom).comp
        (furtherLocFst I u₁ u₂ hI) :=
  algHom_eq_of_algebraMap I hI u₁ _ _ _ fun b => by
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom,
      awayCompletionNestedAlgEquivOfLe_algebraMap, furtherLocFst_algebraMap,
      awayCompletionNestedAlgEquivOfLe_algebraMap,
      IsScalarTower.algebraMap_apply B (awayCompletion (I.map (algebraMap R B)) f)
        (awayCompletion (I.map (algebraMap R (awayCompletion (I.map (algebraMap R B)) f)))
          (awayCompletionHom (I.map (algebraMap R B)) f u₁)),
      IsScalarTower.algebraMap_apply B (awayCompletion (I.map (algebraMap R B)) f)
        (awayCompletion (I.map (algebraMap R (awayCompletion (I.map (algebraMap R B)) f)))
          (awayCompletionHom (I.map (algebraMap R B)) f (u₁ * u₂))),
      furtherLocFst_algebraMap, awayCongrEquivOfEq_algebraMap]

/-- **The same square at the second leg**, which a datum's `hστ` needs beside the first: that
obligation has `CompletedTensorAwayInterchange.furtherLocFst` over one chart algebra and
`CompletedTensorAwayInterchange.furtherLocSnd` over the other, and the two never meet. Same proof,
with `CompletedTensorAwayInterchange.furtherLocSnd_algebraMap` in place of the first leg's own. -/
theorem furtherLocSnd_nestedOfLe (hI : I.FG) (f u₁ u₂ : B)
    (h2 : basicOpen (I.map (algebraMap R B)) u₂ ≤ basicOpen (I.map (algebraMap R B)) f)
    (h12 : basicOpen (I.map (algebraMap R B)) (u₁ * u₂) ≤ basicOpen (I.map (algebraMap R B)) f)
    (hmul : awayCompletionHom (I.map (algebraMap R B)) f (u₁ * u₂) =
      awayCompletionHom (I.map (algebraMap R B)) f u₁ *
        awayCompletionHom (I.map (algebraMap R B)) f u₂) :
    (furtherLocSnd I (awayCompletionHom (I.map (algebraMap R B)) f u₁)
          (awayCompletionHom (I.map (algebraMap R B)) f u₂) hI).comp
        (awayCompletionNestedAlgEquivOfLe I hI f u₂ h2).toAlgHom =
      ((awayCongrEquivOfEq I hmul).toAlgHom.comp
          (awayCompletionNestedAlgEquivOfLe I hI f (u₁ * u₂) h12).toAlgHom).comp
        (furtherLocSnd I u₁ u₂ hI) :=
  algHom_eq_of_algebraMap I hI u₂ _ _ _ fun b => by
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom,
      awayCompletionNestedAlgEquivOfLe_algebraMap, furtherLocSnd_algebraMap,
      awayCompletionNestedAlgEquivOfLe_algebraMap,
      IsScalarTower.algebraMap_apply B (awayCompletion (I.map (algebraMap R B)) f)
        (awayCompletion (I.map (algebraMap R (awayCompletion (I.map (algebraMap R B)) f)))
          (awayCompletionHom (I.map (algebraMap R B)) f u₂)),
      IsScalarTower.algebraMap_apply B (awayCompletion (I.map (algebraMap R B)) f)
        (awayCompletion (I.map (algebraMap R (awayCompletion (I.map (algebraMap R B)) f)))
          (awayCompletionHom (I.map (algebraMap R B)) f (u₁ * u₂))),
      furtherLocSnd_algebraMap, awayCongrEquivOfEq_algebraMap]

end NestedOfLeLegs

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
variable {U : Type u} [CommRing U] [Algebra R U]

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

/-- **Base change round the whole cycle is the identity, through a re-presentation of the presenting
element at each corner.** For `σ₁ : S ≃ₐ[R] T`, `σ₂ : T ≃ₐ[R] U`, `σ₃ : U ≃ₐ[R] S` composing to the
identity, and elements `u : S`, `v : T`, `w : U` each cutting out the open the previous one's
transport does, the composite

```
Sᵘ → Tᶴ⁽ᵘ⁾ → Tᵛ → Uᶴ⁽ᵛ⁾ → Uᵂ → Sᶴ⁽ᵂ⁾ → Sᵘ
```

of three base changes and three basic-open re-presentations is `AlgEquiv.refl`.

**This is the statement with content in the refined cocycle**, and it is the three-fold analogue of
`FormalSpectrum.awayCompletionAlgEquivOfBase_congr_trans_eq_refl` in every respect but one: there
the cycle is `σ` and `σ.symm`, so it closes for free, and here the coarse cocycle `hc` has to be
supplied. That is the only place the refined cocycle consumes anything about the coarse datum.

The proof is that lemma's: `FormalSpectrum.awayCompletion_hom_ext` reduces the claim to the
structural image of `S`, where every base change acts as its own `σ` and every re-presentation acts
as the identity, so the composite acts as `σ₃ ∘ σ₂ ∘ σ₁` and `hc` finishes it. Nothing about the
refined overlap is used; as there, the target of each base change is left to unification rather
than named. -/
theorem awayCompletionAlgEquivOfBase_congr_trans₃_eq_refl (hI : I.FG)
    (σ₁ : S ≃ₐ[R] T) (σ₂ : T ≃ₐ[R] U) (σ₃ : U ≃ₐ[R] S) (u : S) (v : T) (w : U)
    (m₁ : basicOpen (I.map (algebraMap R T)) (σ₁ u) = basicOpen (I.map (algebraMap R T)) v)
    (m₂ : basicOpen (I.map (algebraMap R U)) (σ₂ v) = basicOpen (I.map (algebraMap R U)) w)
    (m₃ : basicOpen (I.map (algebraMap R S)) (σ₃ w) = basicOpen (I.map (algebraMap R S)) u)
    (hc : σ₁.trans (σ₂.trans σ₃) = AlgEquiv.refl) :
    ((awayCompletionAlgEquivOfBase I hI σ₁ (rfl : σ₁ u = σ₁ u)).trans
          ((awayCompletionCongrBasicOpenAlg _ _ _ (hI.map _) m₁).restrictScalars R)).trans
        (((awayCompletionAlgEquivOfBase I hI σ₂ (rfl : σ₂ v = σ₂ v)).trans
            ((awayCompletionCongrBasicOpenAlg _ _ _ (hI.map _) m₂).restrictScalars R)).trans
          ((awayCompletionAlgEquivOfBase I hI σ₃ (rfl : σ₃ w = σ₃ w)).trans
            ((awayCompletionCongrBasicOpenAlg _ _ _ (hI.map _) m₃).restrictScalars R)))
      = AlgEquiv.refl := by
  set E := ((awayCompletionAlgEquivOfBase I hI σ₁ (rfl : σ₁ u = σ₁ u)).trans
        ((awayCompletionCongrBasicOpenAlg _ _ _ (hI.map _) m₁).restrictScalars R)).trans
      (((awayCompletionAlgEquivOfBase I hI σ₂ (rfl : σ₂ v = σ₂ v)).trans
          ((awayCompletionCongrBasicOpenAlg _ _ _ (hI.map _) m₂).restrictScalars R)).trans
        ((awayCompletionAlgEquivOfBase I hI σ₃ (rfl : σ₃ w = σ₃ w)).trans
          ((awayCompletionCongrBasicOpenAlg _ _ _ (hI.map _) m₃).restrictScalars R))) with hE
  have key : (E : awayCompletion (I.map (algebraMap R S)) u →ₐ[R] _).toRingHom = RingHom.id _ := by
    refine awayCompletion_hom_ext (I.map (algebraMap R S)) u u (hI.map _)
      (le_comap_awayCompletionIdeal_algHom I u u E.toAlgHom)
      (le_comap_awayCompletionIdeal_algHom I u u (AlgHom.id R _)) ?_
    refine RingHom.ext fun s => ?_
    change E (awayCompletionHom (I.map (algebraMap R S)) u s)
      = awayCompletionHom (I.map (algebraMap R S)) u s
    rw [awayCompletionHom_eq_algebraMap, hE]
    simp only [AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
      awayCompletionAlgEquivOfBase_algebraMap, AlgEquiv.commutes]
    congr 1
    have hs := DFunLike.congr_fun hc s
    simpa only [AlgEquiv.trans_apply, AlgEquiv.coe_refl, id_eq] using hs
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

section TripleOverlap

variable {Ak : Type u} [CommRing Ak] [Algebra R Ak]

/-! ### Two transport steps for a basic open along a map of completed localizations -/

/-- **An algebra map of completed localizations carries equal basic opens to equal basic opens.**
The preimage statement `FormalSpectrum.preimage_basicOpen_awayCompletionAlgHom` read forwards. -/
theorem basicOpen_awayCompletionAlgHom_congr (f : Ai) (g : Aj)
    (φ : awayCompletion (I.map (algebraMap R Ai)) f →ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) g)
    {x y : awayCompletion (I.map (algebraMap R Ai)) f}
    (hxy : basicOpen (awayCompletionIdeal (I.map (algebraMap R Ai)) f) x
      = basicOpen (awayCompletionIdeal (I.map (algebraMap R Ai)) f) y) :
    basicOpen (awayCompletionIdeal (I.map (algebraMap R Aj)) g) (φ x)
      = basicOpen (awayCompletionIdeal (I.map (algebraMap R Aj)) g) (φ y) := by
  rw [← preimage_basicOpen_awayCompletionAlgHom I f g φ x,
    ← preimage_basicOpen_awayCompletionAlgHom I f g φ y, hxy]

/-- **An algebra map of completed localizations carries a basic open written as a meet to the meet
of the images.** The meet is spelled as a product on the way in and back out, which is what
`FormalSpectrum.basicOpen_mul` does at both ends. -/
theorem basicOpen_awayCompletionAlgHom_inf (f : Ai) (g : Aj)
    (φ : awayCompletion (I.map (algebraMap R Ai)) f →ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) g)
    {x a b : awayCompletion (I.map (algebraMap R Ai)) f}
    (hx : basicOpen (awayCompletionIdeal (I.map (algebraMap R Ai)) f) x
      = basicOpen (awayCompletionIdeal (I.map (algebraMap R Ai)) f) a
        ⊓ basicOpen (awayCompletionIdeal (I.map (algebraMap R Ai)) f) b) :
    basicOpen (awayCompletionIdeal (I.map (algebraMap R Aj)) g) (φ x)
      = basicOpen (awayCompletionIdeal (I.map (algebraMap R Aj)) g) (φ a)
        ⊓ basicOpen (awayCompletionIdeal (I.map (algebraMap R Aj)) g) (φ b) := by
  rw [← basicOpen_mul] at hx
  rw [basicOpen_awayCompletionAlgHom_congr I f g φ hx, map_mul, basicOpen_mul]

/-- **The first further-localization leg is the structure map on the nose.** -/
theorem furtherLocFst_awayCompletionHom (hI : I.FG) (d₁ d₂ d : Ai) :
    furtherLocFst I d₁ d₂ hI (awayCompletionHom (I.map (algebraMap R Ai)) d₁ d)
      = awayCompletionHom (I.map (algebraMap R Ai)) (d₁ * d₂) d := by
  rw [awayCompletionHom_eq_algebraMap, awayCompletionHom_eq_algebraMap, furtherLocFst_algebraMap]

/-- **The second further-localization leg is the structure map on the nose.** -/
theorem furtherLocSnd_awayCompletionHom (hI : I.FG) (d₁ d₂ d : Ai) :
    furtherLocSnd I d₁ d₂ hI (awayCompletionHom (I.map (algebraMap R Ai)) d₂ d)
      = awayCompletionHom (I.map (algebraMap R Ai)) (d₁ * d₂) d := by
  rw [awayCompletionHom_eq_algebraMap, awayCompletionHom_eq_algebraMap, furtherLocSnd_algebraMap]

/-! ### The hypothesis, once, at an arbitrary ordered triple -/

/-- **`hστ` at one ordered triple of charts**, in the spelling
`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData` states it: the inverse of the
triple-overlap equivalence `s` intertwines the two further-localization legs with `θ`.

`θ` is taken in the direction it occurs in — *out of* the target chart's double overlap — so that
a datum's field is this predicate on the nose at the unpermuted triple, and one
`AlgEquiv.symm_symm` away from it at the two permuted ones. -/
abbrev SigmaIntertwinesLegs (hI : I.FG) (u₁ u₂ : Ai) (v₁ v₂ : Aj)
    (θ : awayCompletion (I.map (algebraMap R Aj)) v₂ ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ai)) u₁)
    (s : awayCompletion (I.map (algebraMap R Ai)) (u₁ * u₂) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) (v₁ * v₂)) : Prop :=
  s.symm.toAlgHom.comp (furtherLocSnd I v₁ v₂ hI)
    = (furtherLocFst I u₁ u₂ hI).comp θ.toAlgHom

variable (hI : I.FG) (gij gik : Ai) (gji gjk : Aj) (gki gkj : Ak)

/-! ### The two factors of the chart match -/

/-- **`hστ` read forwards**: the triple-overlap equivalence carries the first leg's image of a
section of the *i*-chart overlap to the second leg's image of its transition. -/
theorem sigma_furtherLocFst
    (τij : awayCompletion (I.map (algebraMap R Ai)) gij ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) gji)
    (σijk : awayCompletion (I.map (algebraMap R Ai)) (gij * gik) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) (gjk * gji))
    (hijk : SigmaIntertwinesLegs I hI gij gik gjk gji τij.symm σijk)
    (x : awayCompletion (I.map (algebraMap R Ai)) gij) :
    σijk (furtherLocFst I gij gik hI x) = furtherLocSnd I gjk gji hI (τij x) := by
  have h := AlgHom.congr_fun hijk (τij x)
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] at h
  rw [← h, σijk.apply_symm_apply]

/-- **The *(i, j)* factor of the chart match, and `hστ` at the unpermuted triple answers it.**
Inside `Spf (A_j{1/(g_jk · g_ji)})` the triple-overlap equivalence carries the *i*-side refined
overlap at the pair *⟨i, h⟩*, *⟨j, h'⟩* to the *j*-side one. -/
theorem basicOpen_sigma_refinedOverlapElt_ij
    (τij : awayCompletion (I.map (algebraMap R Ai)) gij ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) gji)
    (σijk : awayCompletion (I.map (algebraMap R Ai)) (gij * gik) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) (gjk * gji))
    (hijk : SigmaIntertwinesLegs I hI gij gik gjk gji τij.symm σijk) (h : Ai) (h' : Aj) :
    basicOpen (awayCompletionIdeal (I.map (algebraMap R Aj)) (gjk * gji))
        (σijk (awayCompletionHom (I.map (algebraMap R Ai)) (gij * gik)
          (h * refinedOverlapElt I hI gij gji τij h h')))
      = basicOpen (awayCompletionIdeal (I.map (algebraMap R Aj)) (gjk * gji))
          (awayCompletionHom (I.map (algebraMap R Aj)) (gjk * gji)
            (h' * refinedOverlapElt I hI gji gij τij.symm h' h)) := by
  rw [← furtherLocFst_awayCompletionHom I hI gij gik,
    sigma_furtherLocFst I hI gij gik gji gjk τij σijk hijk,
    ← furtherLocSnd_awayCompletionHom I hI gjk gji]
  refine basicOpen_awayCompletionAlgHom_congr I gji (gjk * gji) (furtherLocSnd I gjk gji hI) ?_
  rw [basicOpen_awayCompletionHom_mul_refinedOverlapElt I hI gji gij τij.symm h' h,
    AlgEquiv.symm_symm, ← τij.apply_symm_apply (awayCompletionHom
      (I.map (algebraMap R Aj)) gji h'), ← basicOpen_mul, ← map_mul,
    basicOpen_awayCompletionAlgEquiv_eq_iff I gij gji τij, basicOpen_mul,
    basicOpen_awayCompletionHom_mul_refinedOverlapElt I hI gij gji τij h h']
  exact inf_comm _ _

/-! ### The crux: the *k*-chart section read through *i* and through *j* -/

/-- The *k*-chart section pushed into the *i*-side triple overlap, through `hστ` at `(k, i, j)`. -/
theorem furtherLocSnd_transition_symm_awayCompletionHom
    (τik : awayCompletion (I.map (algebraMap R Ai)) gik ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ak)) gki)
    (σkij : awayCompletion (I.map (algebraMap R Ak)) (gki * gkj) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ai)) (gij * gik))
    (hkij : SigmaIntertwinesLegs I hI gki gkj gij gik τik σkij) (c : Ak) :
    furtherLocSnd I gij gik hI (τik.symm (awayCompletionHom (I.map (algebraMap R Ak)) gki c))
      = σkij (awayCompletionHom (I.map (algebraMap R Ak)) (gki * gkj) c) := by
  have h := AlgHom.congr_fun hkij
    (τik.symm (awayCompletionHom (I.map (algebraMap R Ak)) gki c))
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply] at h
  rw [furtherLocFst_awayCompletionHom I hI gki gkj c] at h
  rw [← h, σkij.apply_symm_apply]

/-- The *k*-chart section pushed into the *j*-side triple overlap, through `hστ` at `(j, k, i)`. -/
theorem furtherLocFst_transition_symm_awayCompletionHom
    (τjk : awayCompletion (I.map (algebraMap R Aj)) gjk ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ak)) gkj)
    (σjki : awayCompletion (I.map (algebraMap R Aj)) (gjk * gji) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ak)) (gki * gkj))
    (hjki : SigmaIntertwinesLegs I hI gjk gji gki gkj τjk.symm σjki) (c : Ak) :
    furtherLocFst I gjk gji hI (τjk.symm (awayCompletionHom (I.map (algebraMap R Ak)) gkj c))
      = σjki.symm (awayCompletionHom (I.map (algebraMap R Ak)) (gki * gkj) c) := by
  have h := AlgHom.congr_fun hjki (awayCompletionHom (I.map (algebraMap R Ak)) gkj c)
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] at h
  rw [furtherLocSnd_awayCompletionHom I hI gki gkj c] at h
  exact h.symm

/-- The cocycle, read as a two-step identity out of the *k*-side triple overlap. -/
theorem sigma_sigma_eq_sigma_symm
    (σijk : awayCompletion (I.map (algebraMap R Ai)) (gij * gik) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) (gjk * gji))
    (σjki : awayCompletion (I.map (algebraMap R Aj)) (gjk * gji) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ak)) (gki * gkj))
    (σkij : awayCompletion (I.map (algebraMap R Ak)) (gki * gkj) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ai)) (gij * gik))
    (hc : σijk.trans (σjki.trans σkij) = AlgEquiv.refl)
    (u : awayCompletion (I.map (algebraMap R Ak)) (gki * gkj)) :
    σijk (σkij u) = σjki.symm u := by
  have hx := AlgEquiv.ext_iff.mp hc (σijk.symm (σjki.symm u))
  simp only [AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply, AlgEquiv.coe_refl, id_eq] at hx
  rw [hx, σijk.apply_symm_apply]

/-- **The crux, and it is an equality of *elements*.** The *k*-chart section transported into the
triple overlap through chart *i* and through chart *j* is the same section. It needs `hστ` at the
two **permuted** triples and the cocycle; `hστ` at `(i, j, k)` is not used. -/
theorem sigma_furtherLocSnd_transition_symm
    (τik : awayCompletion (I.map (algebraMap R Ai)) gik ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ak)) gki)
    (τjk : awayCompletion (I.map (algebraMap R Aj)) gjk ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ak)) gkj)
    (σijk : awayCompletion (I.map (algebraMap R Ai)) (gij * gik) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) (gjk * gji))
    (σjki : awayCompletion (I.map (algebraMap R Aj)) (gjk * gji) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ak)) (gki * gkj))
    (σkij : awayCompletion (I.map (algebraMap R Ak)) (gki * gkj) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ai)) (gij * gik))
    (hkij : SigmaIntertwinesLegs I hI gki gkj gij gik τik σkij)
    (hjki : SigmaIntertwinesLegs I hI gjk gji gki gkj τjk.symm σjki)
    (hc : σijk.trans (σjki.trans σkij) = AlgEquiv.refl) (c : Ak) :
    σijk (furtherLocSnd I gij gik hI
        (τik.symm (awayCompletionHom (I.map (algebraMap R Ak)) gki c)))
      = furtherLocFst I gjk gji hI
          (τjk.symm (awayCompletionHom (I.map (algebraMap R Ak)) gkj c)) := by
  rw [furtherLocSnd_transition_symm_awayCompletionHom I hI gij gik gki gkj τik σkij hkij c,
    sigma_sigma_eq_sigma_symm I gij gik gji gjk gki gkj σijk σjki σkij hc,
    furtherLocFst_transition_symm_awayCompletionHom I hI gji gjk gki gkj τjk σjki hjki c]

/-! ### The triple chart-match -/

/-- The triple-overlap equivalence carries the *i*-side reading of a refining element to its
*j*-side reading. -/
theorem sigma_awayCompletionHom
    (τij : awayCompletion (I.map (algebraMap R Ai)) gij ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) gji)
    (σijk : awayCompletion (I.map (algebraMap R Ai)) (gij * gik) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) (gjk * gji))
    (hijk : SigmaIntertwinesLegs I hI gij gik gjk gji τij.symm σijk) (h : Ai) :
    σijk (awayCompletionHom (I.map (algebraMap R Ai)) (gij * gik) h)
      = furtherLocSnd I gjk gji hI (τij (awayCompletionHom (I.map (algebraMap R Ai)) gij h)) := by
  rw [← furtherLocFst_awayCompletionHom I hI gij gik,
    sigma_furtherLocFst I hI gij gik gji gjk τij σijk hijk]

/-- **The *(i, k)* factor of the chart match, resolved into the two refining elements.** -/
theorem basicOpen_sigma_refinedOverlapElt_ik
    (τij : awayCompletion (I.map (algebraMap R Ai)) gij ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) gji)
    (τik : awayCompletion (I.map (algebraMap R Ai)) gik ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ak)) gki)
    (τjk : awayCompletion (I.map (algebraMap R Aj)) gjk ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ak)) gkj)
    (σijk : awayCompletion (I.map (algebraMap R Ai)) (gij * gik) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) (gjk * gji))
    (σjki : awayCompletion (I.map (algebraMap R Aj)) (gjk * gji) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ak)) (gki * gkj))
    (σkij : awayCompletion (I.map (algebraMap R Ak)) (gki * gkj) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ai)) (gij * gik))
    (hijk : SigmaIntertwinesLegs I hI gij gik gjk gji τij.symm σijk)
    (hkij : SigmaIntertwinesLegs I hI gki gkj gij gik τik σkij)
    (hjki : SigmaIntertwinesLegs I hI gjk gji gki gkj τjk.symm σjki)
    (hc : σijk.trans (σjki.trans σkij) = AlgEquiv.refl) (h : Ai) (h'' : Ak) :
    basicOpen (awayCompletionIdeal (I.map (algebraMap R Aj)) (gjk * gji))
        (σijk (awayCompletionHom (I.map (algebraMap R Ai)) (gij * gik)
          (h * refinedOverlapElt I hI gik gki τik h h'')))
      = basicOpen (awayCompletionIdeal (I.map (algebraMap R Aj)) (gjk * gji))
            (furtherLocSnd I gjk gji hI (τij (awayCompletionHom
              (I.map (algebraMap R Ai)) gij h)))
        ⊓ basicOpen (awayCompletionIdeal (I.map (algebraMap R Aj)) (gjk * gji))
            (furtherLocFst I gjk gji hI (τjk.symm (awayCompletionHom
              (I.map (algebraMap R Ak)) gkj h''))) := by
  rw [← furtherLocSnd_awayCompletionHom I hI gij gik]
  have key := basicOpen_awayCompletionAlgHom_inf I (gij * gik) (gjk * gji) σijk.toAlgHom
    (basicOpen_awayCompletionAlgHom_inf I gik (gij * gik) (furtherLocSnd I gij gik hI)
      (basicOpen_awayCompletionHom_mul_refinedOverlapElt I hI gik gki τik h h''))
  simp only [AlgEquiv.coe_toAlgHom] at key
  rw [key, furtherLocSnd_awayCompletionHom I hI gij gik,
    sigma_awayCompletionHom I hI gij gik gji gjk τij σijk hijk,
    sigma_furtherLocSnd_transition_symm I hI gij gik gji gjk gki gkj τik τjk σijk σjki σkij
      hkij hjki hc]

/-- **The *j*-side *(j, k)* factor, resolved into the two refining elements.** -/
theorem basicOpen_refinedOverlapElt_jk
    (τjk : awayCompletion (I.map (algebraMap R Aj)) gjk ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ak)) gkj) (h' : Aj) (h'' : Ak) :
    basicOpen (awayCompletionIdeal (I.map (algebraMap R Aj)) (gjk * gji))
        (awayCompletionHom (I.map (algebraMap R Aj)) (gjk * gji)
          (h' * refinedOverlapElt I hI gjk gkj τjk h' h''))
      = basicOpen (awayCompletionIdeal (I.map (algebraMap R Aj)) (gjk * gji))
            (awayCompletionHom (I.map (algebraMap R Aj)) (gjk * gji) h')
        ⊓ basicOpen (awayCompletionIdeal (I.map (algebraMap R Aj)) (gjk * gji))
            (furtherLocFst I gjk gji hI (τjk.symm (awayCompletionHom
              (I.map (algebraMap R Ak)) gkj h''))) := by
  have key := basicOpen_awayCompletionAlgHom_inf I gjk (gjk * gji) (furtherLocFst I gjk gji hI)
    (basicOpen_awayCompletionHom_mul_refinedOverlapElt I hI gjk gkj τjk h' h'')
  rwa [furtherLocFst_awayCompletionHom I hI gjk gji
      (h' * refinedOverlapElt I hI gjk gkj τjk h' h''),
    furtherLocFst_awayCompletionHom I hI gjk gji h'] at key

/-- **The *j*-side *(j, i)* factor, resolved into the two refining elements.** -/
theorem basicOpen_refinedOverlapElt_ji
    (τij : awayCompletion (I.map (algebraMap R Ai)) gij ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) gji) (h : Ai) (h' : Aj) :
    basicOpen (awayCompletionIdeal (I.map (algebraMap R Aj)) (gjk * gji))
        (awayCompletionHom (I.map (algebraMap R Aj)) (gjk * gji)
          (h' * refinedOverlapElt I hI gji gij τij.symm h' h))
      = basicOpen (awayCompletionIdeal (I.map (algebraMap R Aj)) (gjk * gji))
            (awayCompletionHom (I.map (algebraMap R Aj)) (gjk * gji) h')
        ⊓ basicOpen (awayCompletionIdeal (I.map (algebraMap R Aj)) (gjk * gji))
            (furtherLocSnd I gjk gji hI (τij (awayCompletionHom
              (I.map (algebraMap R Ai)) gij h))) := by
  have key := basicOpen_awayCompletionAlgHom_inf I gji (gjk * gji) (furtherLocSnd I gjk gji hI)
    (basicOpen_awayCompletionHom_mul_refinedOverlapElt I hI gji gij τij.symm h' h)
  rw [AlgEquiv.symm_symm] at key
  rwa [furtherLocSnd_awayCompletionHom I hI gjk gji
      (h' * refinedOverlapElt I hI gji gij τij.symm h' h),
    furtherLocSnd_awayCompletionHom I hI gjk gji h'] at key

/-- **The triple chart-match.** Inside `Spf (A_j{1/(g_jk · g_ji)})` the image under the coarse
triple-overlap equivalence of the *i*-side refined triple overlap is the *j*-side refined triple
overlap.

The two sides do **not** match factor by factor: the *i*-side *(i, k)* factor cuts out
`D(h) ⊓ D(h'')` and the *j*-side *(j, k)* factor cuts out `D(h') ⊓ D(h'')`. Only the two *meets*
agree, and the last step is the lattice identity `(a ⊓ b) ⊓ (b ⊓ c) = (a ⊓ c) ⊓ (a ⊓ b)`.
`FormalSpectrum.basicOpen_eq_top_of_factorwise_match` is the refutation of the factorwise
reading. -/
theorem basicOpen_sigma_refinedTripleOverlap
    (τij : awayCompletion (I.map (algebraMap R Ai)) gij ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) gji)
    (τik : awayCompletion (I.map (algebraMap R Ai)) gik ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ak)) gki)
    (τjk : awayCompletion (I.map (algebraMap R Aj)) gjk ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ak)) gkj)
    (σijk : awayCompletion (I.map (algebraMap R Ai)) (gij * gik) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) (gjk * gji))
    (σjki : awayCompletion (I.map (algebraMap R Aj)) (gjk * gji) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ak)) (gki * gkj))
    (σkij : awayCompletion (I.map (algebraMap R Ak)) (gki * gkj) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ai)) (gij * gik))
    (hijk : SigmaIntertwinesLegs I hI gij gik gjk gji τij.symm σijk)
    (hkij : SigmaIntertwinesLegs I hI gki gkj gij gik τik σkij)
    (hjki : SigmaIntertwinesLegs I hI gjk gji gki gkj τjk.symm σjki)
    (hc : σijk.trans (σjki.trans σkij) = AlgEquiv.refl) (h : Ai) (h' : Aj) (h'' : Ak) :
    basicOpen (awayCompletionIdeal (I.map (algebraMap R Aj)) (gjk * gji))
        (σijk (awayCompletionHom (I.map (algebraMap R Ai)) (gij * gik)
          ((h * refinedOverlapElt I hI gij gji τij h h') *
            (h * refinedOverlapElt I hI gik gki τik h h''))))
      = basicOpen (awayCompletionIdeal (I.map (algebraMap R Aj)) (gjk * gji))
          (awayCompletionHom (I.map (algebraMap R Aj)) (gjk * gji)
            ((h' * refinedOverlapElt I hI gjk gkj τjk h' h'') *
              (h' * refinedOverlapElt I hI gji gij τij.symm h' h))) := by
  rw [map_mul (awayCompletionHom (I.map (algebraMap R Ai)) (gij * gik)), map_mul σijk,
    map_mul (awayCompletionHom (I.map (algebraMap R Aj)) (gjk * gji)),
    basicOpen_mul, basicOpen_mul,
    basicOpen_sigma_refinedOverlapElt_ij I hI gij gik gji gjk τij σijk hijk h h',
    basicOpen_sigma_refinedOverlapElt_ik I hI gij gik gji gjk gki gkj τij τik τjk σijk σjki σkij
      hijk hkij hjki hc h h'',
    basicOpen_refinedOverlapElt_jk I hI gji gjk gkj τjk h' h'',
    basicOpen_refinedOverlapElt_ji I hI gij gji gjk τij h h']
  generalize basicOpen (awayCompletionIdeal (I.map (algebraMap R Aj)) (gjk * gji))
    (awayCompletionHom (I.map (algebraMap R Aj)) (gjk * gji) h') = a
  generalize basicOpen (awayCompletionIdeal (I.map (algebraMap R Aj)) (gjk * gji))
    (furtherLocSnd I gjk gji hI (τij (awayCompletionHom (I.map (algebraMap R Ai)) gij h))) = b
  generalize basicOpen (awayCompletionIdeal (I.map (algebraMap R Aj)) (gjk * gji))
    (furtherLocFst I gjk gji hI (τjk.symm (awayCompletionHom
      (I.map (algebraMap R Ak)) gkj h''))) = c
  -- `(a ⊓ b) ⊓ (b ⊓ c) = (a ⊓ c) ⊓ (a ⊓ b)`, both sides `a ⊓ b ⊓ c`
  rw [inf_assoc, inf_assoc, ← inf_assoc b b c, inf_idem, ← inf_assoc c a b, inf_comm c a,
    inf_assoc a c b, ← inf_assoc a a (c ⊓ b), inf_idem, inf_comm c b]

/-! ### The refined triple overlap, and the equivalence between its two readings -/

/-- The refined triple overlap sits inside the coarse one. -/
theorem basicOpen_refinedTripleOverlap_le
    (τij : awayCompletion (I.map (algebraMap R Ai)) gij ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) gji)
    (τik : awayCompletion (I.map (algebraMap R Ai)) gik ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ak)) gki) (h : Ai) (h' : Aj) (h'' : Ak) :
    basicOpen (I.map (algebraMap R Ai))
        ((h * refinedOverlapElt I hI gij gji τij h h') *
          (h * refinedOverlapElt I hI gik gki τik h h''))
      ≤ basicOpen (I.map (algebraMap R Ai)) (gij * gik) := by
  rw [basicOpen_mul (I.map (algebraMap R Ai)) (h * refinedOverlapElt I hI gij gji τij h h')
      (h * refinedOverlapElt I hI gik gki τik h h''),
    basicOpen_mul (I.map (algebraMap R Ai)) gij gik]
  exact inf_le_inf
    (basicOpen_mul_le_of_basicOpen_le _ h (basicOpen_refinedOverlapElt_le I hI gij gji τij h h'))
    (basicOpen_mul_le_of_basicOpen_le _ h (basicOpen_refinedOverlapElt_le I hI gik gki τik h h''))

/-- **The refined triple-overlap equivalence.** The same four-step composite
`FormalSpectrum.refinedOverlapTransition` takes, with
`FormalSpectrum.basicOpen_sigma_refinedTripleOverlap` in place of the double chart-match at the
third step. -/
def refinedOverlapSigma
    (τij : awayCompletion (I.map (algebraMap R Ai)) gij ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) gji)
    (τik : awayCompletion (I.map (algebraMap R Ai)) gik ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ak)) gki)
    (τjk : awayCompletion (I.map (algebraMap R Aj)) gjk ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ak)) gkj)
    (σijk : awayCompletion (I.map (algebraMap R Ai)) (gij * gik) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) (gjk * gji))
    (σjki : awayCompletion (I.map (algebraMap R Aj)) (gjk * gji) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ak)) (gki * gkj))
    (σkij : awayCompletion (I.map (algebraMap R Ak)) (gki * gkj) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ai)) (gij * gik))
    (hijk : SigmaIntertwinesLegs I hI gij gik gjk gji τij.symm σijk)
    (hkij : SigmaIntertwinesLegs I hI gki gkj gij gik τik σkij)
    (hjki : SigmaIntertwinesLegs I hI gjk gji gki gkj τjk.symm σjki)
    (hc : σijk.trans (σjki.trans σkij) = AlgEquiv.refl) (h : Ai) (h' : Aj) (h'' : Ak) :
    awayCompletion (I.map (algebraMap R Ai))
        ((h * refinedOverlapElt I hI gij gji τij h h') *
          (h * refinedOverlapElt I hI gik gki τik h h'')) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj))
        ((h' * refinedOverlapElt I hI gjk gkj τjk h' h'') *
          (h' * refinedOverlapElt I hI gji gij τij.symm h' h)) :=
  ((awayCompletionNestedAlgEquivOfLe I hI (gij * gik) _
          (basicOpen_refinedTripleOverlap_le I hI gij gik gji gki τij τik h h' h'')).trans
        (awayCompletionAlgEquivOfBase I hI σijk rfl)).trans
    (((awayCompletionCongrBasicOpenAlg _ _ _ (hI.map _) (by
          rw [map_algebraMap_awayCompletion_eq]
          exact basicOpen_sigma_refinedTripleOverlap I hI gij gik gji gjk gki gkj τij τik τjk
            σijk σjki σkij hijk hkij hjki hc h h' h'')).restrictScalars R).trans
      (awayCompletionNestedAlgEquivOfLe I hI (gjk * gji) _
        (basicOpen_refinedTripleOverlap_le I hI gjk gji gkj gij τjk τij.symm h' h'' h)).symm)

/-- **The refined cocycle** — `AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData`'s `hσc`
field at the refined index, read at `FormalSpectrum.refinedOverlapSigma` rather than at a datum.
The three rotations of one ordered triple compose to the identity.

**The three rotated instances are the same data, permuted, and nothing new is supplied.** The
coarse cocycle is rotated by `AlgEquiv.trans₃_eq_refl_rotate`; the three
`FormalSpectrum.SigmaIntertwinesLegs` hypotheses are *closed* under the rotation as a set, which is
why they are named for their triples and not for their positions — the *(j,k,i)* instance wants
`hjki`, `hijk`, `hkij` in that order, and the *(k,i,j)* one wants `hkij`, `hjki`, `hijk`. The only
place a `AlgEquiv.symm_symm` is needed is the third rotation's *τ_ik*, and it is `rfl` at these
completions.

**The whole proof is `AlgEquiv.trans₃_eq_refl_of_middle_eq_refl` at
`FormalSpectrum.awayCompletionAlgEquivOfBase_congr_trans₃_eq_refl`, in one term**, and that is a
measurement worth recording against this module's `## What is *not* proved here`, which predicted
the opposite: the nested identifications *do* pair off across a cycle of three, so the refined
cocycle costs exactly what the refined symmetry law cost and no naturality statement about
`FormalSpectrum.awayCompletionNestedAlgEquivOfLe` is needed for it either.

**It consumes the coarse laws only through the coarse cocycle.** `hστ` at the three rotations is
already inside `FormalSpectrum.refinedOverlapSigma`'s hypotheses, spent on the triple chart-match;
the cocycle asks for nothing beyond the coarse `hc` that the definition already takes, so this
statement adds no obligation to a caller that has the `σ` field. -/
theorem refinedOverlapSigma_trans₃_eq_refl
    (τij : awayCompletion (I.map (algebraMap R Ai)) gij ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) gji)
    (τik : awayCompletion (I.map (algebraMap R Ai)) gik ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ak)) gki)
    (τjk : awayCompletion (I.map (algebraMap R Aj)) gjk ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ak)) gkj)
    (σijk : awayCompletion (I.map (algebraMap R Ai)) (gij * gik) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) (gjk * gji))
    (σjki : awayCompletion (I.map (algebraMap R Aj)) (gjk * gji) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ak)) (gki * gkj))
    (σkij : awayCompletion (I.map (algebraMap R Ak)) (gki * gkj) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ai)) (gij * gik))
    (hijk : SigmaIntertwinesLegs I hI gij gik gjk gji τij.symm σijk)
    (hkij : SigmaIntertwinesLegs I hI gki gkj gij gik τik σkij)
    (hjki : SigmaIntertwinesLegs I hI gjk gji gki gkj τjk.symm σjki)
    (hc : σijk.trans (σjki.trans σkij) = AlgEquiv.refl) (h : Ai) (h' : Aj) (h'' : Ak) :
    (refinedOverlapSigma I hI gij gik gji gjk gki gkj τij τik τjk σijk σjki σkij
          hijk hkij hjki hc h h' h'').trans
        ((refinedOverlapSigma I hI gjk gji gkj gki gij gik τjk τij.symm τik.symm σjki σkij σijk
            hjki hijk hkij (AlgEquiv.trans₃_eq_refl_rotate _ _ _ hc) h' h'' h).trans
          (refinedOverlapSigma I hI gki gkj gik gij gjk gji τik.symm τjk.symm τij σkij σijk σjki
            hkij hjki hijk
            (AlgEquiv.trans₃_eq_refl_rotate _ _ _ (AlgEquiv.trans₃_eq_refl_rotate _ _ _ hc))
            h'' h h'))
      = AlgEquiv.refl :=
  AlgEquiv.trans₃_eq_refl_of_middle_eq_refl _ _ _ _ _ _ _ _ _
    (awayCompletionAlgEquivOfBase_congr_trans₃_eq_refl I hI σijk σjki σkij _ _ _ _ _ _ hc)

/-! ### Why the factorwise reading of the chart match is not a theorem -/

/-- **The factorwise reading of the triple chart-match is refutable.**
`FormalSpectrum.basicOpen_sigma_refinedOverlapElt_ik` and
`FormalSpectrum.basicOpen_refinedOverlapElt_jk` describe the two *(·, k)* factors, and they are
**different** opens: `D(h) ⊓ D(h'')` against `D(h') ⊓ D(h'')`. Asserting them equal — which is
what a factor-by-factor reading asks for — forces, at `h' = 1` and `h'' = 1`, that `D(τ_ij(ĥ))` is
the whole space for **every** refining element `h`. So the chart match is an identity of *meets*
and not of factors. -/
theorem basicOpen_eq_top_of_factorwise_match
    (τij : awayCompletion (I.map (algebraMap R Ai)) gij ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) gji)
    (τik : awayCompletion (I.map (algebraMap R Ai)) gik ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ak)) gki)
    (τjk : awayCompletion (I.map (algebraMap R Aj)) gjk ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ak)) gkj)
    (σijk : awayCompletion (I.map (algebraMap R Ai)) (gij * gik) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) (gjk * gji))
    (σjki : awayCompletion (I.map (algebraMap R Aj)) (gjk * gji) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ak)) (gki * gkj))
    (σkij : awayCompletion (I.map (algebraMap R Ak)) (gki * gkj) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Ai)) (gij * gik))
    (hijk : SigmaIntertwinesLegs I hI gij gik gjk gji τij.symm σijk)
    (hkij : SigmaIntertwinesLegs I hI gki gkj gij gik τik σkij)
    (hjki : SigmaIntertwinesLegs I hI gjk gji gki gkj τjk.symm σjki)
    (hc : σijk.trans (σjki.trans σkij) = AlgEquiv.refl)
    (hfac : ∀ (h : Ai) (h' : Aj) (h'' : Ak),
      basicOpen (awayCompletionIdeal (I.map (algebraMap R Aj)) (gjk * gji))
          (σijk (awayCompletionHom (I.map (algebraMap R Ai)) (gij * gik)
            (h * refinedOverlapElt I hI gik gki τik h h'')))
        = basicOpen (awayCompletionIdeal (I.map (algebraMap R Aj)) (gjk * gji))
            (awayCompletionHom (I.map (algebraMap R Aj)) (gjk * gji)
              (h' * refinedOverlapElt I hI gjk gkj τjk h' h'')))
    (h : Ai) :
    basicOpen (awayCompletionIdeal (I.map (algebraMap R Aj)) (gjk * gji))
      (furtherLocSnd I gjk gji hI (τij (awayCompletionHom
        (I.map (algebraMap R Ai)) gij h))) = ⊤ := by
  have key := hfac h 1 1
  rw [basicOpen_sigma_refinedOverlapElt_ik I hI gij gik gji gjk gki gkj τij τik τjk σijk σjki σkij
      hijk hkij hjki hc h 1,
    basicOpen_refinedOverlapElt_jk I hI gji gjk gkj τjk 1 1] at key
  -- both `D(1)`s are the whole space
  rw [show basicOpen (awayCompletionIdeal (I.map (algebraMap R Aj)) (gjk * gji))
        (furtherLocFst I gjk gji hI (τjk.symm (awayCompletionHom
          (I.map (algebraMap R Ak)) gkj 1))) = ⊤ by
      rw [map_one, map_one, map_one, basicOpen_one],
    show basicOpen (awayCompletionIdeal (I.map (algebraMap R Aj)) (gjk * gji))
        (awayCompletionHom (I.map (algebraMap R Aj)) (gjk * gji) (1 : Aj)) = ⊤ by
      rw [map_one, basicOpen_one]] at key
  simpa using key

end TripleOverlap

end FormalSpectrum

end
