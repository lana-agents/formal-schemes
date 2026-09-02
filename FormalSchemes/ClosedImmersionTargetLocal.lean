import FormalSchemes.ClosedImmersion
import FormalSchemes.OpenFormalSubscheme

set_option linter.style.header false

/-!
# Closed immersions of formal schemes are local on the target

`FormalSchemes.ClosedImmersion` (issue 492) proves one half of this: the *base* condition of
`FormalScheme.IsClosedImmersion` descends along an open cover of the target. Its stalk condition
did not descend, and was carried as a **global** hypothesis, because the tree had no way to say
"the restriction of `f` over the chart `V`" as a morphism of formal schemes — so there was nothing
whose stalk maps one could hypothesise about. That module's own docstring recorded the gap, before
it was repointed at this file:

> A fully target-local variant, whose per-chart hypothesis is a genuine
> `FormalScheme.IsClosedImmersion` of the restricted morphism (relating `(restricted f).stalkMap` to
> `f.stalkMap` through the open-immersion stalk isomorphism), is left as a documented follow-up.

`FormalScheme.restrictOpenMap` (`FormalSchemes.OpenFormalSubscheme`) is that missing morphism, and
with its base map identified as `Set.restrictPreimage` and its stalk maps identified with those of
`f`, both halves descend. That is `isClosedImmersion_iff_restrictOpen`: an **iff**, with a genuine
`FormalScheme.IsClosedImmersion` on each chart and no global hypothesis left over.

## Why it is stated over an arbitrary family of opens

The criterion is proved for any `V : ι → Opens Y` with `⨆ i, V i = ⊤`, and the `OpenCover` version
is a corollary. This is the shape issue 772 established for the separatedness criteria and for the
same reason: every instance's data already *is* a family of opens (basic opens of an affine, ranges
of chart immersions), and forcing it through a bundled `OpenCover` first costs a construction that
the statement does not need.

## Main results

* `AlgebraicGeometry.FormalScheme.isClosedImmersion_iff_restrictOpen`: `f` is a closed immersion
  **iff** each `X|_{f⁻¹(V i)} ⟶ Y|_{V i}` is, for a family of opens covering `Y`.
* `AlgebraicGeometry.FormalScheme.isClosedImmersion_iff_openCover`: the same over a
  `FormalScheme.OpenCover` of `Y`.
* `AlgebraicGeometry.FormalScheme.isClosedImmersion_of_openCover'`: the hypothesis-per-chart form,
  which shows `FormalSchemes.ClosedImmersion`'s `isClosedImmersion_of_openCover` is now the
  special case in which the stalk half is supplied globally.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.14, §10.15.
* [The Stacks Project, Tag 01JV](https://stacks.math.columbia.edu/tag/01JV).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology

universe u

namespace AlgebraicGeometry.FormalScheme

variable {X Y : FormalScheme.{u}}

/-- **Being a closed immersion is local on the target**, in the full sense: both the base condition
and the stalk condition descend, so the per-chart hypothesis is a genuine
`FormalScheme.IsClosedImmersion` and nothing is left as a global assumption.

The base half is Mathlib's `isClosedEmbedding_iff_restrictPreimage`, reached because
`restrictOpenMap_base` says the induced morphism's base map *is* `Set.restrictPreimage`. The stalk
half is `surjective_stalkMap_restrictOpenMap_iff`, which transports in both directions because the
comparison there is by isomorphisms. -/
theorem isClosedImmersion_iff_restrictOpen (hX : X.LocallyFG) (hY : Y.LocallyFG)
    {ι : Type*} {V : ι → Opens Y} (hV : IsOpenCover V) (f : X ⟶ Y) :
    IsClosedImmersion f ↔
      ∀ i, IsClosedImmersion (restrictOpenSchemeMap X hX Y hY f (V i)) := by
  have hcont : Continuous ⇑f.toLRSHom.base := f.toLRSHom.base.hom.continuous
  constructor
  · intro hf i
    refine ⟨?_, fun x => ?_⟩
    · rw [restrictOpenSchemeMap_toLRSHom, restrictOpenMap_base]
      exact (hV.isClosedEmbedding_iff_restrictPreimage hcont).mp hf.base_closedEmbedding i
    · rw [restrictOpenSchemeMap_toLRSHom, surjective_stalkMap_restrictOpenMap_iff]
      exact hf.surjective_stalkMap _
  · intro h
    refine ⟨(hV.isClosedEmbedding_iff_restrictPreimage hcont).mpr fun i => ?_, fun x => ?_⟩
    · have hi := (h i).base_closedEmbedding
      rwa [restrictOpenSchemeMap_toLRSHom, restrictOpenMap_base] at hi
    · obtain ⟨i, hi⟩ : ∃ i, f.toLRSHom.base x ∈ V i := by
        have hmem : f.toLRSHom.base x ∈ ⋃ i, (V i : Set Y) := by
          rw [hV.iSup_set_eq_univ]; trivial
        simpa using hmem
      have hs := (h i).surjective_stalkMap
        (show (X.restrictOpen hX ((Opens.map f.toLRSHom.base).obj (V i))).toLocallyRingedSpace
          from ⟨x, hi⟩)
      rw [restrictOpenSchemeMap_toLRSHom, surjective_stalkMap_restrictOpenMap_iff] at hs
      have hpt : (X.restrictOpenι hX ((Opens.map f.toLRSHom.base).obj (V i))).base
          (show (X.restrictOpen hX ((Opens.map f.toLRSHom.base).obj (V i))).toLocallyRingedSpace
            from ⟨x, hi⟩) = x := by
        rw [restrictOpenι_base]; rfl
      rwa [hpt] at hs

/-- **The `OpenCover` form.** The charts of an open cover are open immersions, so their ranges are
open and cover `Y`; the criterion applies to that family. -/
theorem isClosedImmersion_iff_openCover (hX : X.LocallyFG) (hY : Y.LocallyFG)
    (𝒰 : OpenCover Y) (f : X ⟶ Y) :
    IsClosedImmersion f ↔ ∀ j, IsClosedImmersion (restrictOpenSchemeMap X hX Y hY f
      (LocallyRingedSpace.IsOpenImmersion.opensRange (𝒰.map j).toLRSHom)) :=
  isClosedImmersion_iff_restrictOpen hX hY
    (IsOpenCover.of_sets (fun j => (𝒰.isOpenImmersion j).base_open.isOpen_range) 𝒰.iUnion_range) f

/-- **`isClosedImmersion_of_openCover` is now the special case with a global stalk hypothesis.**

`FormalSchemes.ClosedImmersion`'s version takes the base condition per chart and the stalk
condition globally; this one takes a genuine `FormalScheme.IsClosedImmersion` per chart, which is
strictly weaker input, and the two are related by `FormalScheme.isClosedImmersion_iff_openCover`.
The old statement is left where it is — it has consumers — but it is no longer the strongest form
available.
-/
theorem isClosedImmersion_of_openCover' (hX : X.LocallyFG) (hY : Y.LocallyFG)
    (𝒰 : OpenCover Y) (f : X ⟶ Y)
    (h : ∀ j, IsClosedImmersion (restrictOpenSchemeMap X hX Y hY f
      (LocallyRingedSpace.IsOpenImmersion.opensRange (𝒰.map j).toLRSHom))) :
    IsClosedImmersion f :=
  (isClosedImmersion_iff_openCover hX hY 𝒰 f).mpr h

end AlgebraicGeometry.FormalScheme

end
