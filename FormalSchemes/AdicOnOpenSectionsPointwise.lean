import FormalSchemes.AdicOnOpenSections

set_option linter.style.header false

/-!
# The structural map, pointwise, in the `locallyRingedSpaceObj` spelling

`FormalSchemes.AdicOnOpenSections` states `FormalSpectrum.comp_sectionsOpenHom` and
`FormalSpectrum.comp_eqToHom_sectionsOpenHom` as equalities of ring homomorphisms. Applying them
at a concrete formal spectrum is not, as one would expect, a matter of `RingHom.congr_fun`: the
section rings of `Spf` have **three** spellings that are definitionally equal and syntactically
different, and which of them an equation happens to be stated in decides whether the next step
costs milliseconds or does not terminate.

The three are

* `↑((structureSheaf I).presheaf.obj (op U))` — what `FormalSpectrum.sectionsOpenHom` lands in,
  because `FormalSpectrum.structureSheaf` is what defines the sections;
* `↑((w.base _* (locallyRingedSpaceObj J).presheaf).obj (op U))` — the **pushforward** spelling,
  which is the type of the equation `FormalSpectrum.comp_sectionsOpenHom` states, because
  `w.c.app (op U)` lands in the pushforward by the definition of a morphism of presheafed spaces;
* `↑((locallyRingedSpaceObj J).presheaf.obj (op ((Opens.map w.base).obj U)))` — what a consumer
  that owns a morphism of *locally ringed spaces* writes, and in particular what an `eqToHom`
  presheaf transport between two opens of `Spf J` has to be applied to.

This file supplies the two statements of `FormalSchemes.AdicOnOpenSections` in the **third**
spelling, pinned there by an explicit type ascription, so that a consumer never has to make the
kernel reconcile them.

## Why the ascription matters, and it is not a matter of taste

A proof that lets the two spellings meet at a concrete formal spectrum **elaborates in under a
second and then does not typecheck**. Measured on the node chart of the Tate quotient, where
`J = FormalSpectrum.awayCompletionIdeal (AlgebraicGeometry.annulusIdealOfDefinition R I q)
(AlgebraicGeometry.overlapX R I q)` and `w` is a composite of the `𝔾m`-inversion transition with a
basic-open chart: `set_option trace.profiler true` with a *lowered* `maxHeartbeats` reports
`0.61 s` for the elaboration and then a failure inside `[Kernel] typechecking declarations`.
Raising `maxHeartbeats` cannot help, because heartbeats do not bound the kernel; a run at
`maxHeartbeats 4000000` was killed after thirty minutes.

The elaborator reconciles the three spellings with unification hints and a cache. The kernel redoes
the work from scratch, and at a concrete `J` and `w` every unfolding step carries those terms
along. Stating the reconciliation **while `I`, `J`, `w` and `U` are still variables** makes the
kernel's check trivial, and a consumer then receives a hypothesis already in the spelling it wants.

The corresponding symptom in tactic mode is a `rw` that reports *"Did not find an occurrence of the
pattern"* against a pattern which is character-for-character present in the pretty-printed goal,
followed by *"the target expression is not type-correct under the `instances` transparency level"*
and an application type mismatch naming `TopCat.Presheaf CommRingCat`. The mismatch is in the
**space index** of `TopCat.Presheaf` — `↑(locallyRingedSpaceObj I).toTopCat` against
`TopCat.of (FormalSpectrum I)` — which is invisible in the goal display.

## Contents

* `FormalSpectrum.locallyRingedSpaceObj_presheaf` — the two sheaves are the same sheaf, by `rfl`.
  **Rewriting with it does not fix the mismatch**, because the difference is inside implicit
  arguments that a rewrite motive cannot abstract; it is stated so that nobody has to rediscover
  that, and because it is the honest way to say what is going on.
* `FormalSpectrum.sectionsOpenHom_c_app` — `FormalSpectrum.comp_sectionsOpenHom`, pointwise, with
  the equation's type pinned to the sections of `(locallyRingedSpaceObj J).presheaf` over
  `(Opens.map w.base).obj U`.
* `FormalSpectrum.eqToHom_sectionsOpenHom_apply` — `FormalSpectrum.comp_eqToHom_sectionsOpenHom`,
  pointwise, with the equation's type pinned to the sections of `(locallyRingedSpaceObj I).presheaf`
  over `U₂`.

Nothing here is new mathematics: each of the three is `rfl`, `RingHom.congr_fun` of a theorem of
`FormalSchemes.AdicOnOpenSections`, or both. What is new is the **type** each statement carries.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat.Presheaf

universe u

namespace FormalSpectrum

variable {R S : Type u} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)
variable [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J]

omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J] in
/-- **`Spf I`'s two presheaves are one presheaf**, by `rfl`: `FormalSpectrum.locallyRingedSpaceObj`
is built on `FormalSpectrum.sheafedSpaceObj`, whose presheaf is `FormalSpectrum.structureSheaf`'s
(`FormalSpectrum.sheafedSpaceObj_presheaf`).

**This does not make the two spellings interchangeable in a `rw`.** The difference a rewrite has to
see is not this equation but the space index of `TopCat.Presheaf` inside the implicit arguments of
`CommRingCat.Hom.hom`, and a rewrite motive cannot abstract those. Use the two pointwise lemmas
below instead; see this file's module docstring. -/
theorem locallyRingedSpaceObj_presheaf :
    (locallyRingedSpaceObj I).presheaf = (structureSheaf I).presheaf :=
  rfl

/-- **The naturality square of `FormalSpectrum.sectionsOpenHom`, pointwise**, with the equation's
type pinned to the sections of `(locallyRingedSpaceObj J).presheaf` over `(Opens.map w.base).obj U`.

This is `FormalSpectrum.comp_sectionsOpenHom` and `RingHom.congr_fun`; the content is entirely in
the type ascription, which is what lets a consumer apply an `eqToHom` presheaf transport of
`locallyRingedSpaceObj J` to the result without the kernel having to reconcile that spelling with
the pushforward one at a concrete `J` and `w`. See this file's module docstring for the
measurement. -/
theorem sectionsOpenHom_c_app (w : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    (U : Opens (FormalSpectrum I)) (r : R) :
    ((w.c.app (op U)).hom (sectionsOpenHom I U r) :
        ((locallyRingedSpaceObj J).presheaf.obj (op ((Opens.map w.base).obj U)) : Type u)) =
      sectionsOpenHom J ((Opens.map w.base).obj U) (globalSectionsMap I J w r) :=
  RingHom.congr_fun (comp_sectionsOpenHom I J w U) r

omit [TopologicalSpace S] [IsAdicRing J] in
/-- **The transport of `FormalSpectrum.sectionsOpenHom` along an equality of opens, pointwise**,
with the presheaf written as `(locallyRingedSpaceObj I).presheaf` and the equation's type pinned to
the sections over `U₂`.

This is `FormalSpectrum.comp_eqToHom_sectionsOpenHom` and `RingHom.congr_fun`. It is the shape a
leg of a chart condition consumes: such a leg is a `.c.app` followed by exactly this transport, so
`sectionsOpenHom_c_app` and this lemma compose to compute the leg on the structural image. -/
theorem eqToHom_sectionsOpenHom_apply {U₁ U₂ : Opens (FormalSpectrum I)} (h : U₁ = U₂) (r : R) :
    ((((locallyRingedSpaceObj I).presheaf.map (eqToHom (congrArg op h))).hom)
        (sectionsOpenHom I U₁ r) :
        ((locallyRingedSpaceObj I).presheaf.obj (op U₂) : Type u)) =
      sectionsOpenHom I U₂ r :=
  RingHom.congr_fun (comp_eqToHom_sectionsOpenHom I h) r

end FormalSpectrum
