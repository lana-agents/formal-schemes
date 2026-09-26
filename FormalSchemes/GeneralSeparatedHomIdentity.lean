import FormalSchemes.GeneralSeparatedHomValues

set_option linter.style.header false

/-!
# The identity of a formal scheme is separated (EGA I §10.15), at an arbitrary target

`FormalScheme.IsSeparatedHom` (`FormalSchemes.GeneralSeparatedHom`) is separatedness of a morphism
`g : X ⟶ Y` of formal schemes at an arbitrary target, and `FormalSchemes.GeneralSeparatedHomValues`
supplies its first two values. **Both of those have target `Spf R`**: they are
`FormalScheme.isSeparatedHom_of_isSeparatedOverSpf` applied to a value of the affine-base predicate,
so neither says anything a statement over an affine base could not already say.

This file supplies the first value at an **arbitrary target**:

```
FormalScheme.isSeparatedHom_id (hX : X.LocallyFG) : FormalScheme.IsSeparatedHom hX hX (𝟙 X)
```

for an arbitrary `X`, together with one concrete instance of it
(`AlgebraicGeometry.BasicOpenCover.coverSubscheme_isSeparatedHom_id`, whose object is a union of
three basic opens of a `Spf` and is not affine in general).

## Why the general statement is the cheap one

`FormalScheme.LocallyFG` (`FormalSchemes.LocallyFG`) says that every point of `X` has an affine
chart `f : Spf I ⟶ X` which is an open immersion **and whose ideal is finitely generated**. That is
exactly the per-chart datum `FormalScheme.IsSeparatedHom` asks of a cover of the target: take the
cover indexed by the points of `X`, take `V x` to be the range of the chart at `x`, and identify
`X|_{V x}` with `Spf I` by `FormalScheme.restrictOpenIso`, whose hypothesis *"the range is the
open"* is `rfl` by construction. So the identity needs no hypothesis beyond the one that makes
`FormalScheme.IsSeparatedHom` statable at all, and the concrete values are corollaries rather than
separate work.

What the per-chart clause then asks is that `Spf I` be separated over `Spf I` along the identity,
which is `AlgebraicGeometry.spf_isSeparatedOverSpf_self` below.

## What this settles, and what it does not

* It settles that `FormalScheme.IsSeparatedHom` is **inhabited at an arbitrary target**. Before it,
  every value in the tree had target `Spf R`, and a predicate about general targets whose only
  values are affine is a definition that elaborates rather than a notion. *Arbitrary* rather than
  *non-affine* is the honest word: nothing on this tree exhibits a formal scheme it knows not to be
  affine, and the concrete instance below is affine in the degenerate case where its three opens
  already cover.
* It does **not** make the predicate non-trivial *over* such a target in the strong sense: the
  cover this proof produces consists of **affine** opens, as every cover a value of this predicate
  can produce must, since the per-chart clause is stated over `Spf I`. A separated morphism between
  two genuinely non-affine formal schemes, neither of them an identity, is still not in the tree.
* It is **not** a composition law and it is **not** conservativity's hard direction; both remain
  open and are recorded in `FormalSchemes.GeneralSeparatedHom`'s not-proved list.

## Placement of the three helpers

Three of the five declarations here are general and would read better earlier. Each is kept, with
its cost measured by walking every `import FormalSchemes.` line transitively over the modules under
`FormalSchemes/` (a module is not counted in its own closure; the aggregator at the repository root
is outside the walk):

* `FormalSpectrum.locallyRingedSpaceObjCongr` and its `_hom_eq_map` belong beside
  `FormalSpectrum.locallyRingedSpaceMap_id` in `FormalSchemes.FormalSpectrum`, whose reverse
  closure is **537** — nine tenths of the tree — against this file's **1**. Declined on that ratio,
  which the second consumer does not change: `FormalSchemes.GeneralSeparatedHomRestrictOpen` uses
  both, and records that it does.
* `FormalScheme.restrictOpenMap_toLRSHom_id` belongs beside `FormalScheme.restrictOpenMap_id` in
  `FormalSchemes.OpenFormalSubscheme`, reverse closure **76**. Declined for now on the same
  disposition `FormalSchemes.StructureSheafStalkPowerSeries` records for
  `AdicCompletion.bijective_mapCompletion`: one consumer, and the move is worth re-costing when a
  second appears.
* `AlgebraicGeometry.spf_isSeparatedOverSpf_self` belongs in `FormalSchemes.AffineSeparatedScheme`
  beside `AlgebraicGeometry.spf_isSeparatedOverSpf`, and that module's reverse closure is only
  **4** — so this one is cheap. It is kept here anyway because its proof consumes
  `FormalSpectrum.locallyRingedSpaceObjCongr`, which is **not** cheap to move, and splitting the
  pair across two modules would put a `FormalSpectrum`-level lemma in a file about affine
  separatedness. The pair moves together or not at all.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
-/

noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry FormalSpectrum

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R]

/-- **Equal ideals have equal formal spectra**, as an isomorphism of locally ringed spaces.

`IsAdicRing` is a `Prop` (`FormalSchemes.AdicRing`), so after `subst` the two sides differ only in
an instance argument, which definitional proof irrelevance identifies; the isomorphism is
`CategoryTheory.Iso.refl`.

It is stated rather than inlined because `rw` cannot do this job: rewriting an ideal inside
`FormalSpectrum.locallyRingedSpaceObj` fails with *"motive is not type correct"*, the instance
argument being the dependency that breaks the motive. Naming the transport is the standard remedy
on this tree — compare the note on `FormalScheme.restrictOpenCongr` in
`FormalSchemes.OpenFormalSubscheme`. -/
def locallyRingedSpaceObjCongr {J K : Ideal R} [IsAdicRing J] [IsAdicRing K] (h : J = K) :
    locallyRingedSpaceObj J ≅ locallyRingedSpaceObj K := by
  subst h
  exact Iso.refl _

/-- **The transport is the functorial map of the identity homomorphism.** This is the half that
makes `FormalSpectrum.locallyRingedSpaceObjCongr` usable over a base: a structural morphism written
as a `FormalSpectrum.locallyRingedSpaceMap` is recognised as the transport, and conversely. -/
theorem locallyRingedSpaceObjCongr_hom_eq_map {J K : Ideal R} [IsAdicRing J] [IsAdicRing K]
    (h : J = K) (hle : K ≤ Ideal.comap (RingHom.id R) J) :
    (locallyRingedSpaceObjCongr h).hom = locallyRingedSpaceMap K J (RingHom.id R) hle := by
  subst h
  rw [locallyRingedSpaceMap_id]
  rfl

end FormalSpectrum

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] [TopologicalSpace R]

/-- **`Spf I` is separated over itself along the identity** (EGA I §10.15).

This is `AlgebraicGeometry.spf_isSeparatedOverSpf` at `A = R`, transported across
`Ideal.map_id` by `FormalSpectrum.locallyRingedSpaceObjCongr` and
`FormalScheme.isSeparatedOverSpf_of_iso`. Two spellings have to be managed and both are recorded
because each costs a round trip to rediscover:

* `rw [Ideal.map_id]` does **not** fire on `Ideal.map (algebraMap R R) I` — `rw` matches
  syntactically and `algebraMap R R` is only definitionally `RingHom.id R` — while the *term*
  `Ideal.map_id I` typechecks at that type. Hence the `show … from` spelling below.
* The final compatibility is closed with `exact` rather than `rw`: `rw` checks type-correctness at
  `instances` transparency, and the two sides agree only at `default`. -/
theorem spf_isSeparatedOverSpf_self {I : Ideal R} [IsAdicRing I] (hI : I.FG) :
    FormalScheme.IsSeparatedOverSpf hI (FormalScheme.Spf I)
      (𝟙 (locallyRingedSpaceObj I)) := by
  haveI : IsAdicRing (I.map (algebraMap R R)) := by
    rw [show I.map (algebraMap R R) = I from Ideal.map_id I]
    infer_instance
  refine FormalScheme.isSeparatedOverSpf_of_iso hI (locallyRingedSpaceObjCongr (Ideal.map_id I)) ?_
    (spf_isSeparatedOverSpf (A := R) hI)
  exact (Category.comp_id _).trans
    (locallyRingedSpaceObjCongr_hom_eq_map (Ideal.map_id I) (le_of_eq (Ideal.map_id I).symm))

namespace FormalScheme

variable {X : FormalScheme.{u}}

/-- **The identity law for `FormalScheme.restrictOpenMap`, at the `FormalScheme.Hom` spelling of the
identity.**

`FormalScheme.restrictOpenMap_id` (`FormalSchemes.OpenFormalSubscheme`) is the same law at
`𝟙 X.toLocallyRingedSpace`, with a `FormalScheme.restrictOpenCongr`-valued right-hand side that
names the transport along `FormalScheme.opensMap_id_base_obj` instead of leaving it to
unification. **This lemma is here for its spelling and not because that one is expensive**:
`FormalScheme.IsSeparatedHom` puts `FormalScheme.Hom.toLRSHom` of its morphism in the goal, and at
the identity that is `(𝟙 X : X ⟶ X).toLRSHom`, which is not the identity the other lemma is
stated at.

The cost is worth stating precisely, because this neighbourhood has carried a wrong account of it.
Once the right-hand side is a bare identity, the proof below — `FormalScheme.restrictOpenMap_uniq`,
a `change`, and `rfl` — goes through at *both* spellings of the identity and *both* spellings of
the open, all four under default heartbeats and none of them slow: 2.79–2.88 s, one scratch file at
a time, two runs each. So the `FormalScheme.restrictOpenCongr` form buys the named transport and not
tractability, and the functor-law note in `FormalSchemes.OpenFormalSubscheme` — reverse closure
**76**, against this file's **1** — attributed it to the heartbeat budget and did not reproduce.
That note has since been repaired and now carries the account above.

The `change` is load-bearing at every one of the four spellings, and its absence is a transparency
failure and not a budget one: without it `rw [Category.id_comp]` reports *"Did not find an
occurrence of the pattern"* along with Lean's own note that the target is not type-correct at
instances transparency, and it does so in 2.8 s rather than by running out of budget.

Note the ascription `(𝟙 X : X ⟶ X)`: `(𝟙 X).toLRSHom` does not elaborate, since `𝟙 X` has type
`CategoryTheory.CategoryStruct.toQuiver.1 X X`, which is not of the form field notation accepts. -/
theorem restrictOpenMap_toLRSHom_id (hX : X.LocallyFG) (V : Opens X) :
    X.restrictOpenMap hX X hX (𝟙 X : X ⟶ X).toLRSHom V
      = 𝟙 (X.restrictOpen hX
          ((Opens.map (𝟙 X : X ⟶ X).toLRSHom.base).obj V)).toLocallyRingedSpace := by
  refine (X.restrictOpenMap_uniq hX X hX (𝟙 X : X ⟶ X).toLRSHom V _ ?_).symm
  change 𝟙 _ ≫ X.restrictOpenι hX V
      = X.restrictOpenι hX
          ((Opens.map (𝟙 X.toLocallyRingedSpace : X.toLocallyRingedSpace ⟶ _).base).obj V)
        ≫ 𝟙 X.toLocallyRingedSpace
  rw [Category.id_comp, Category.comp_id]
  rfl

/-- **The identity morphism of a locally finitely generated formal scheme is separated** (EGA I
§10.15), at an arbitrary — in particular non-affine — target.

The cover is indexed by the points of `X`: at each point `FormalScheme.LocallyFG` supplies an affine
chart which is an open immersion with finitely generated ideal, and the open is its range, so the
range hypothesis of `FormalScheme.restrictOpenIso` is `rfl`. The per-chart clause is then
`AlgebraicGeometry.spf_isSeparatedOverSpf_self` transported along that identification, the induced
morphism on the open subscheme being the identity by
`FormalScheme.restrictOpenMap_toLRSHom_id`.

The chart isomorphism is elaborated first at its own spelling and only then ascribed to the
`FormalScheme.Spf` one: instance search matches at reducible transparency and `FormalScheme.Spf`
is not reducible, so the open-immersion instance for the chart is not found if the ascription is
made up front. -/
theorem isSeparatedHom_id (hX : X.LocallyFG) : IsSeparatedHom hX hX (𝟙 X) := by
  have hX' := hX
  choose R hcr hts I hadic f hIfg hmem hopen using hX'
  refine ⟨X, fun x => ⟨Set.range (f x).base, (hopen x).base_open.isOpen_range⟩, ?_, fun x => ?_⟩
  · exact Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ⟨x, hmem x⟩
  · haveI := hopen x
    have e₀ := X.restrictOpenIso hX
      ((Opens.map (𝟙 X : X ⟶ X).toLRSHom.base).obj
        ⟨Set.range (f x).base, (hopen x).base_open.isOpen_range⟩) (f x) rfl
    have e : (FormalScheme.Spf (I x)).toLocallyRingedSpace
        ≅ (X.restrictOpen hX ((Opens.map (𝟙 X : X ⟶ X).toLRSHom.base).obj
            ⟨Set.range (f x).base, (hopen x).base_open.isOpen_range⟩)).toLocallyRingedSpace := e₀
    refine ⟨R x, hcr x, hts x, I x, hadic x, hIfg x, e.symm, ?_⟩
    refine isSeparatedOverSpf_of_iso (hIfg x) e ?_ (spf_isSeparatedOverSpf_self (hIfg x))
    rw [← Category.assoc, restrictOpenMap_toLRSHom_id hX]
    simp only [Iso.symm_hom]
    exact e.hom_inv_id

end FormalScheme

namespace BasicOpenCover

variable {I : Ideal R} [IsAdicRing I] {A : Type u} [CommRing A] [Algebra R A] [TopologicalSpace A]
variable [IsAdicRing (I.map (algebraMap R A))] (I) (f : ULift.{u} (Fin 3) → A)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The identity of `D(f₀) ∪ D(f₁) ∪ D(f₂) ⊆ Spf A` is separated** (EGA I §10.15), with the
target not affine in general.

This is `FormalScheme.isSeparatedHom_id` at `BasicOpenCover.coverSubscheme_locallyFG`, and it is
the first `FormalScheme.IsSeparatedHom` in the tree whose **target** is not a `FormalScheme.Spf`:
`AlgebraicGeometry.BasicOpenCover.coverSubscheme_isSeparatedHom`
(`FormalSchemes.GeneralSeparatedHomValues`) is about the same object but over `Spf R`.
`FormalSchemes.BasicOpenCoverOpenImmersion` is about the degenerate case where the three opens do
cover and the object is affine after all.

It is the identity, not a general morphism between two non-affine formal schemes; nothing here
supplies one of those. -/
theorem coverSubscheme_isSeparatedHom_id (hI : I.FG) :
    FormalScheme.IsSeparatedHom (coverSubscheme_locallyFG I f hI) (coverSubscheme_locallyFG I f hI)
      (𝟙 (coverSubscheme I f hI)) :=
  FormalScheme.isSeparatedHom_id (coverSubscheme_locallyFG I f hI)

end BasicOpenCover

end AlgebraicGeometry

end
