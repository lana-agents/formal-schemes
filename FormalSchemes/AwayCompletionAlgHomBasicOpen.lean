import FormalSchemes.BasicOpenChart
import FormalSchemes.CofinalCompletionAlg

set_option linter.style.header false

/-!
# An `R`-algebra map of two completed localizations carries basic opens to basic opens

Let `A` and `B` be `R`-algebras, `f : A`, `g : B`, and give `A{1/f}^` and `B{1/g}^` the ideals of
definition they get from the base, `I·A{1/f}^` and `I·B{1/g}^`. An `R`-algebra map
`φ : A{1/f}^ →ₐ[R] B{1/g}^` then matches the two ideals of definition, so it induces a map of
formal spectra `Spf B{1/g}^ → Spf A{1/f}^`, and the preimage of `D(x)` along that map is `D(φ x)`.
When `φ` is an equivalence `τ`, the last statement can be read backwards: `D(τ x) = D(τ y)` holds
exactly when `D(x) = D(y)` does.

That last biconditional is the only theorem here with content. The three before it are the
plumbing it needs, and each is a lemma this tree already has, applied at this map.

## Why the equivalence case is the one worth naming

A transition between two charts of a formal spectrum is an equivalence of `R`-algebras, and what a
transition has to do with a basic open is *transport* it: given `D(x)` cut out in the source chart,
name the open of the target chart that it goes to, and know that two elements cutting out the same
open on one side cut out the same open on the other. The forward half of that is
`FormalSpectrum.preimage_basicOpen_awayCompletionAlgHom` below at `τ`; the half that is not formal
is the converse, and an equivalence gives it by running the forward half at `τ.symm`.

The shape a consumer actually meets is a **meet**, and it is derived rather than declared —
`D(x) = D(y) ⊓ D(z)` on one side gives `D(τ x) = D(τ y) ⊓ D(τ z)` on the other, by
`FormalSpectrum.basicOpen_mul` in both directions around
`FormalSpectrum.basicOpen_awayCompletionAlgEquiv_eq_iff`:

```lean
rw [← basicOpen_mul, ← map_mul, basicOpen_awayCompletionAlgEquiv_eq_iff I f g τ, basicOpen_mul]
```

Three lines, and the reason it is a usage note here rather than a fifth theorem is that a statement
pinning three elements at one special shape has no generality left to reuse; it would have to be
restated at the next shape. There is nothing to state about the meet itself either:
`(Opens.map h).obj (U ⊓ V)` is `(Opens.map h).obj U ⊓ (Opens.map h).obj V` by `rfl`.

## Main results

* `FormalSpectrum.map_awayCompletionIdeal_algHom`: an `R`-algebra map `A{1/f}^ →ₐ[R] B{1/g}^`
  carries `I·A{1/f}^` onto `I·B{1/g}^`, both written as `FormalSpectrum.awayCompletionIdeal`.
* `FormalSpectrum.le_comap_awayCompletionIdeal_algHom`: the `≤ comap` form of the same, which is
  the shape `FormalSpectrum.mapTop` consumes. The same idiom as
  `FormalSpectrum.le_comap_awayCompletionHom` (`FormalSchemes.BasicOpenChart`).
* `FormalSpectrum.preimage_basicOpen_awayCompletionAlgHom`: the preimage of `D(x)` along the
  induced map of formal spectra is `D(φ x)`, at the level of `TopologicalSpace.Opens`.
* `FormalSpectrum.basicOpen_awayCompletionAlgEquiv_eq_iff`: for `τ` an equivalence,
  `D(τ x) = D(τ y) ↔ D(x) = D(y)`.

## Nothing general is introduced here

`FormalSpectrum.map_awayCompletionIdeal_algHom` is the `awayCompletionIdeal` *spelling* of a fact
this tree already states three times, and it adds nothing to any of them:

* `Ideal.map_algebraMap_algHom` (`FormalSchemes.CofinalCompletionAlg`, reverse closure **25**),
  stated for an `AlgHom`. This is the one this file imports and uses.
* `CompletedTensorProduct.algHom_mapIdeal_isAdicHom`, in `FormalSchemes.CompletedTensorMapSpfPr`,
  whose reverse closure is **163**: the same statement for an `AlgHom`, wrapped in `IsAdicHom`.
* `Ideal.map_algEquiv_map_algebraMap` (`FormalSchemes.AwayBaseChangeTopFiniteType`, reverse
  closure **10**), stated for an `AlgEquiv` only.

All three say `(J·A).map φ = J·B`. What is left over is the bookkeeping that
`FormalSpectrum.awayCompletionIdeal (I·A) f` *is* `I.map (algebraMap R (A{1/f}^))`, which is
`FormalSpectrum.map_algebraMap_awayCompletion_eq` (`FormalSchemes.BasicOpenChart`) — and that
bridge, applied at each end, is the whole proof.

`FormalSpectrum.preimage_basicOpen_awayCompletionAlgHom` likewise proves nothing: it is
`FormalSpectrum.map_preimage_basicOpen` (`FormalSchemes.SpfMap`) at this map, as a term, in the
idiom `AlgebraicGeometry.BasicOpenCover.preimage_basicOpen_chartToBase`
(`FormalSchemes.BasicOpenCoverOpenImmersion`) already uses for the same lemma at a chart map.
`FormalSpectrum.le_comap_awayCompletionIdeal_algHom` is `Ideal.map_le_iff_le_comap.mp` of the
first.

## Placement

Over `FormalSchemes.BasicOpenChart` and `FormalSchemes.CofinalCompletionAlg`: this file's forward
closure is **23** project modules besides itself (24 counted with itself), and its reverse closure
is **1** — `FormalSchemes.RefinedOverlapTransition`, which consumes
`FormalSpectrum.basicOpen_awayCompletionAlgEquiv_eq_iff`. **It was a leaf when the paragraphs below
were written and the arithmetic they quote is unaffected by ceasing to be one**: the consumer is
downstream of everything this file imports, so it adds nothing to either closure above, and the two
counts below were taken at the base that added this file and are not re-run. What the consumer does
change is the counterfactual in the next paragraph, which has been re-measured here.

**The `FormalSchemes.CofinalCompletionAlg` edge is the placement decision, and it costs eight
figure repairs, four of them outside this file.** The forward closure of
`FormalSchemes.BasicOpenChart` is **17**, and that of `FormalSchemes.CofinalCompletionAlg` is
**17** as well; the union is the 23 above, so the second parent contributes five modules the first
does not reach: `FormalSchemes.CofinalCompletion`, `FormalSchemes.CofinalCompletionAlg`,
`FormalSchemes.CofinalIdeal`, `FormalSchemes.IdealsOfDefinition` and
`FormalSchemes.LargestIdealOfDefinition`. Four of those five state no reverse closure of their own,
and `FormalSchemes.IdealsOfDefinition` quotes its own in the placement paragraph of
`Ideal.pow_map_le_map`. **But the five are not the whole account**: any sentence anywhere quoting
the reverse closure of one of them also moves, and
`FormalSchemes/AwayBaseChangeTopFiniteType.lean`'s `## Placement` is one, because it prices this
same edge at its own file and quotes `FormalSchemes.CofinalCompletionAlg` to do it. Measured, not
reasoned from the leaf property: `scripts/closure_audit.py --edge` in the deletion direction prices
that edge at **8** figure repairs in **4** files, **4** of them outside this file. Two of the four
are those two sentences. The other two are in `FormalSchemes/RefinedOverlapTransition.lean`, the
consumer above, whose own forward closure of **64** the deletion would move to **59**: that module
reaches the five modules of the previous sentence through this file and through nothing else, so
the edge this paragraph is about is the only reason it reaches them at all. **That pair is the
whole of what gaining a consumer cost this paragraph**, and it is why the count here is not the two
it once was.

**The module itself costs more than its edge does, and the two must not be confused.** Adding any
module downstream of most of the tree falsifies every *reverse*-closure figure quoted about
anything it imports, in files the diff does not otherwise touch — CONTRIBUTING.md's
*What adding a module costs* is the standing account. Here that is **18** numerals in **14** files,
sixteen of them owed to this file existing at all and two, above, to its second parent. Each is a
`+1`, all eighteen are repaired in this diff, and `--tree` is MISMATCH **0** at both ends.

Both counts are measurements of this diff against the base it was taken at, re-measured there
rather than carried over; they are not standing claims about any later tree, and nothing re-runs
them. The first moves whenever a module is added above anything this file imports, the second
whenever a sentence quoting one of the five parents' reverse closures is written or removed.

Compare `FormalSchemes.AwayBaseChangeTopFiniteType`, which met the same edge and declined it. The
reverse closure of `FormalSchemes.AwayBaseChangeTopFiniteType` is **10**, so all ten of its
consumers would inherit those same five modules, and there the edge costs **15** figure repairs in
**9** files against the four outside this file that it costs here — measured the same way, with
`--edge`, and that file's own `## Placement` states the same count and splits off the four of the
fifteen that are its own. That is why that file restates
`Ideal.map_algEquiv_map_algebraMap` locally rather than importing it, and prices the decision in
its own `## Placement`. The restatement that was forced there is **not** forced here, and the three
general forms listed above are imported rather than copied.

Declined: putting the first two results beside `FormalSpectrum.map_algebraMap_awayCompletion_eq`
in `FormalSchemes.BasicOpenChart`, whose reverse closure is **435**. That is the subject-matter
home, and it would push the `FormalSchemes.CofinalCompletionAlg` edge and its five modules onto all
435. Re-cost it if `FormalSchemes.BasicOpenChart` ever comes to import that module anyway.

## What is *not* proved here

**No `def` for the induced map of formal spectra.** Every statement below spells it as
`FormalSpectrum.mapTop … φ.toRingHom …` with the containment argument supplied by
`FormalSpectrum.le_comap_awayCompletionIdeal_algHom`. `FormalSpectrum.basicOpenChartBase`
(`FormalSchemes.BasicOpenChart`) is the precedent for wanting a name, and nothing here consumes
one more than once, so none is introduced; a definition with a single use site is a name to
maintain and not an abbreviation. Introduce it when a second consumer asks.

Nothing about refinements, chart families or separatedness. This file knows two `R`-algebras and a
map between them, and the transition it was written for is assembled elsewhere.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13, §10.15.
-/

noncomputable section

open TopologicalSpace

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {A : Type u} [CommRing A] [Algebra R A]
variable {B : Type u} [CommRing B] [Algebra R B]

/-- **An `R`-algebra map of two completed localizations carries one ideal of definition onto the
other.** Both are the extension of the base ideal `I`, so this is
`Ideal.map_algebraMap_algHom` (`FormalSchemes.CofinalCompletionAlg`) — an `R`-algebra map carries
`I·A` to `I·B` — read through the identification of
`FormalSpectrum.awayCompletionIdeal (I·A) f` with `I.map (algebraMap R (A{1/f}^))`.

That identification is `FormalSpectrum.map_algebraMap_awayCompletion_eq`
(`FormalSchemes.BasicOpenChart`), and applying it at each end is the entire proof. Nothing new is
proved; see this file's `## Nothing general is introduced here`. -/
theorem map_awayCompletionIdeal_algHom (f : A) (g : B)
    (φ : awayCompletion (I.map (algebraMap R A)) f →ₐ[R]
      awayCompletion (I.map (algebraMap R B)) g) :
    (awayCompletionIdeal (I.map (algebraMap R A)) f).map φ.toRingHom =
      awayCompletionIdeal (I.map (algebraMap R B)) g := by
  rw [← map_algebraMap_awayCompletion_eq I f, ← map_algebraMap_awayCompletion_eq I g]
  exact Ideal.map_algebraMap_algHom φ I

/-- **The `≤ comap` form of `FormalSpectrum.map_awayCompletionIdeal_algHom`**, which is the shape
`FormalSpectrum.mapTop` takes as its hypothesis.

Stated separately for the reason `FormalSpectrum.le_comap_awayCompletionHom`
(`FormalSchemes.BasicOpenChart`) is stated separately beside
`FormalSpectrum.map_awayCompletionHom`: the equality is the fact, the containment is the
interface, and `Ideal.map_le_iff_le_comap` is not something a call site should have to spell. -/
theorem le_comap_awayCompletionIdeal_algHom (f : A) (g : B)
    (φ : awayCompletion (I.map (algebraMap R A)) f →ₐ[R]
      awayCompletion (I.map (algebraMap R B)) g) :
    awayCompletionIdeal (I.map (algebraMap R A)) f ≤
      (awayCompletionIdeal (I.map (algebraMap R B)) g).comap φ.toRingHom :=
  Ideal.map_le_iff_le_comap.mp (map_awayCompletionIdeal_algHom I f g φ).le

/-- **The preimage of `D(x)` along the induced map of formal spectra is `D(φ x)`.**

Nothing new is proved here: this is `FormalSpectrum.map_preimage_basicOpen`
(`FormalSchemes.SpfMap`) at `φ.toRingHom`, and it is stated as a term for that reason, in the
idiom `AlgebraicGeometry.BasicOpenCover.preimage_basicOpen_chartToBase`
(`FormalSchemes.BasicOpenCoverOpenImmersion`) uses for the same lemma at a chart map. What it
earns is the spelling: the containment argument is
`FormalSpectrum.le_comap_awayCompletionIdeal_algHom` above, which no call site should have to
supply by hand. -/
theorem preimage_basicOpen_awayCompletionAlgHom (f : A) (g : B)
    (φ : awayCompletion (I.map (algebraMap R A)) f →ₐ[R]
      awayCompletion (I.map (algebraMap R B)) g)
    (x : awayCompletion (I.map (algebraMap R A)) f) :
    (Opens.map (mapTop (awayCompletionIdeal (I.map (algebraMap R A)) f)
        (awayCompletionIdeal (I.map (algebraMap R B)) g) φ.toRingHom
        (le_comap_awayCompletionIdeal_algHom I f g φ))).obj
      (basicOpen (awayCompletionIdeal (I.map (algebraMap R A)) f) x) =
      basicOpen (awayCompletionIdeal (I.map (algebraMap R B)) g) (φ x) :=
  map_preimage_basicOpen _ _ _ _ x

/-- **An equivalence of completed localizations detects equality of basic opens**: for
`τ : A{1/f}^ ≃ₐ[R] B{1/g}^`, the elements `τ x` and `τ y` cut out the same open of
`Spf B{1/g}^` exactly when `x` and `y` cut out the same open of `Spf A{1/f}^`.

This is the one statement in the file with content, and the content is the **converse**
direction. Both directions run `FormalSpectrum.preimage_basicOpen_awayCompletionAlgHom` twice and
then rewrite: forwards at `τ.symm`, where `AlgEquiv.symm_apply_apply` turns the two preimages back
into `D(x)` and `D(y)`; backwards at `τ` itself, where they are already `D(τ x)` and `D(τ y)`. An
`AlgHom` gives only the backwards direction, which is why this one asks for an `AlgEquiv`.

The meet form a chart transition consumes is derived from this rather than stated; the derivation
is in this file's opening section. -/
theorem basicOpen_awayCompletionAlgEquiv_eq_iff (f : A) (g : B)
    (τ : awayCompletion (I.map (algebraMap R A)) f ≃ₐ[R]
      awayCompletion (I.map (algebraMap R B)) g)
    (x y : awayCompletion (I.map (algebraMap R A)) f) :
    basicOpen (awayCompletionIdeal (I.map (algebraMap R B)) g) (τ x) =
        basicOpen (awayCompletionIdeal (I.map (algebraMap R B)) g) (τ y) ↔
      basicOpen (awayCompletionIdeal (I.map (algebraMap R A)) f) x =
        basicOpen (awayCompletionIdeal (I.map (algebraMap R A)) f) y := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hx := preimage_basicOpen_awayCompletionAlgHom I g f τ.symm.toAlgHom (τ x)
    have hy := preimage_basicOpen_awayCompletionAlgHom I g f τ.symm.toAlgHom (τ y)
    rw [AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] at hx hy
    rw [← hx, ← hy, h]
  · have hx := preimage_basicOpen_awayCompletionAlgHom I f g τ.toAlgHom x
    have hy := preimage_basicOpen_awayCompletionAlgHom I f g τ.toAlgHom y
    rw [AlgEquiv.coe_toAlgHom] at hx hy
    rw [← hx, ← hy, h]

end FormalSpectrum
