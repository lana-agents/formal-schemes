import FormalSchemes.CompletionBasicOpen
import FormalSchemes.CompletionToSpec

set_option linter.style.header false

/-!
# The basic-open completion immersion is `formalCompletion.map` of the localization (EGA I, 10.8)

`FormalSchemes/CompletionBasicOpen.lean` builds the morphism

```
formalCompletion.basicOpenImmersion I hI f :
  formalCompletion R_f (I·R_f) ⟶ formalCompletion R I
```

*geometrically*, as the completion–localization interchange isomorphism followed by the affine
basic-open chart of `Spf R^`, which is how it acquires `LocallyRingedSpace.IsOpenImmersion` and its
range `D(f̂)`. `FormalSchemes/Completion.lean` builds the *functorial* morphism
`formalCompletion.map`, and `FormalSchemes/CompletionToSpec.lean` proves that `formalCompletion.map`
commutes with the canonical morphism `formalCompletion.toSpec : X_{/Y} ⟶ X`
(`formalCompletion.map_comp_toSpec`).

The two morphisms out of a basic-open completion were built for different purposes and had never
been identified. This file identifies them, and reads off the consequence that motivates it: the
square

```
formalCompletion R_f (I·R_f) ──basicOpenImmersion──→ formalCompletion R I
          │ toSpec                                            │ toSpec
          ↓                                                   ↓
       Spec R_f  ───────────── Spec (R → R_f) ─────────────→ Spec R
```

commutes. That is the compatibility a global `X_{/Y} ⟶ X` has to be glued from: for a separated
scheme the affine charts of the completion glue along common basic opens, and on each of them the
local `toSpec`s must agree.

The identification is a ring computation. Unfolding `awayCompletionHom` and using
`AdicCompletion.locCompletionLift_comp_algebraMap`, the composite of the interchange with the chart
map is `AdicCompletion.completionToLocCompletion`, which is *by definition*
`AdicCompletion.mapCompletion` of the localization `R → R_f` — the very ring map
`formalCompletion.map` is built from. The geometric side is then a single
`FormalSpectrum.locallyRingedSpaceMap` by `locallyRingedSpaceMap_comp`, and the two agree by
`locallyRingedSpaceMap_congr`.

## Main definitions and results

* `AdicCompletion.interchangeBackward_comp_algebraMap`: the backward interchange map precomposed
  with the completion structure map of `B̂_{t̂}` is `locCompletionLift`.
* `AdicCompletion.interchangeBackward_comp_awayCompletionHom`: the backward interchange map
  precomposed with the chart map `awayCompletionHom` is `completionToLocCompletion`, i.e.
  `mapCompletion` of the localization.
* `formalCompletion.basicOpenImmersion_eq_map`: the geometric basic-open immersion **is** the
  functorial `formalCompletion.map` of `R → R_f`.
* `formalCompletion.basicOpenImmersion_comp_toSpec`: the `toSpec` square over a basic open
  commutes.
* `formalCompletion.mem_range_basicOpenImmersion_iff`: a point of `Spf R^` is in the range of the
  basic-open immersion **iff** it lies over a prime of `Spec R` avoiding `f`, together with its
  two directional corollaries `formalCompletion.mem_range_basicOpenImmersion` and
  `formalCompletion.notMem_range_basicOpenImmersion`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AdicCompletion

variable {B : Type u} [CommRing B] (K : Ideal B) (t : B)

/-- **The backward interchange map on the image of the completion structure map** is
`locCompletionLift`: `interchangeBackward` is the continuous extension of `locCompletionLift`
along `B̂_{t̂} → (B̂_{t̂})^`, so it agrees with it on the dense image of the structure map.

This is `interchangeBackward_of` with `AdicCompletion.of` traded for `algebraMap`; the two differ
only by `AdicCompletion.algebraMap_apply` over the trivial `B̂_{t̂}`-algebra structure. The
statement was previously derived inline inside the proof of
`AdicCompletion.map_interchangeBackward`; it is given a name here because it is the step every
identification of `interchangeBackward` with a completion functoriality map goes through. -/
theorem interchangeBackward_comp_algebraMap (hK : K.FG) :
    (interchangeBackward K t hK).comp
        (algebraMap (awayCompletionLoc K t)
          (AdicCompletion (completionLocIdeal K t) (awayCompletionLoc K t))) =
      locCompletionLift K t hK := by
  ext y
  rw [RingHom.comp_apply, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, interchangeBackward_of]

/-- **The geometric chart map of a basic-open completion is `mapCompletion` of the localization.**
The affine basic-open chart of `Spf B̂` at `t̂` is `Spf` of `awayCompletionHom (idealOfDefinition K)
(awayPoint K t) : B̂ → (B̂_{t̂})^`, and the completion–localization interchange identifies its
target with `(B_t)^`. This says the resulting ring map `B̂ → (B_t)^` is `completionToLocCompletion`,
which is `AdicCompletion.mapCompletion (algebraMap B B_t)` by definition.

No continuity extension is needed: `awayCompletionHom` is by construction the two-step
`algebraMap B̂ → B̂_{t̂} → (B̂_{t̂})^`, so `interchangeBackward_comp_algebraMap` reduces the claim
to `locCompletionLift_comp_algebraMap`, which is the universal property of `B̂_{t̂}` as a
localization of `B̂`. -/
theorem interchangeBackward_comp_awayCompletionHom (hK : K.FG) :
    (interchangeBackward K t hK).comp
        (FormalSpectrum.awayCompletionHom (idealOfDefinition K) (awayPoint K t)) =
      completionToLocCompletion K t hK := by
  rw [FormalSpectrum.awayCompletionHom, ← RingHom.comp_assoc,
    interchangeBackward_comp_algebraMap, locCompletionLift_comp_algebraMap]

end AdicCompletion

namespace formalCompletion

open FormalSpectrum AdicCompletion

variable {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) (f : R)

/-- **The basic-open completion immersion is the functoriality morphism of the localization**
(EGA I, 10.8). `formalCompletion.basicOpenImmersion` is built geometrically — the interchange
isomorphism followed by the affine basic-open chart of `Spf R^` — because that is what exhibits it
as an open immersion with range `D(f̂)`. `formalCompletion.map` is built functorially, as `Spf` of
`AdicCompletion.mapCompletion` of the localization `R → R_f`. They are the same morphism.

Everything on the geometric side is a `FormalSpectrum.locallyRingedSpaceMap`, so
`locallyRingedSpaceMap_comp` collapses the composite to a single one, and
`AdicCompletion.interchangeBackward_comp_awayCompletionHom` identifies its ring map with
`mapCompletion (algebraMap R R_f)`; `locallyRingedSpaceMap_congr` then closes the goal, the
continuity witnesses being irrelevant. -/
theorem basicOpenImmersion_eq_map :
    basicOpenImmersion I hI f =
      formalCompletion.map hI (hI.map (algebraMap R (Localization.Away f)))
        (algebraMap R (Localization.Away f)) (le_of_eq rfl) := by
  haveI := AdicCompletion.isAdicRing_map I hI
  haveI := FormalSpectrum.isAdicRing_awayCompletionIdeal I f hI
  apply FormalScheme.Hom.ext'
  have hcomp := interchangeBackward_comp_awayCompletionHom I f hI
  have hIK : idealOfDefinition I ≤
      (idealOfDefinition (I.map (algebraMap R (Localization.Away f)))).comap
        ((interchangeBackward I f hI).comp
          (awayCompletionHom (idealOfDefinition I) (awayPoint I f))) := by
    rw [hcomp]
    exact Ideal.map_le_iff_le_comap.mp
      (idealOfDefinition_map_le (algebraMap R (Localization.Away f)) (le_of_eq rfl) (hI.map _))
  change (locCompletionChartIso I hI f).hom ≫
      basicOpenChart (idealOfDefinition I) (awayPoint I f) = _
  rw [show (locCompletionChartIso I hI f).hom ≫
        basicOpenChart (idealOfDefinition I) (awayPoint I f) =
      locallyRingedSpaceMap (idealOfDefinition I)
        (idealOfDefinition (I.map (algebraMap R (Localization.Away f))))
        ((interchangeBackward I f hI).comp
          (awayCompletionHom (idealOfDefinition I) (awayPoint I f))) hIK from
    (locallyRingedSpaceMap_comp _ _ _ _ _ _ _ _).symm]
  exact locallyRingedSpaceMap_congr _ _ _ _ _ _ hcomp

/-- **The `toSpec` square over a basic open** (EGA I, 10.8): completing `Spec R_f = D(f)` along
`V(I·R_f)` and mapping to `Spec R_f`, then to `Spec R`, is the same as including the completion of
`D(f)` into the completion of `Spec R` and then mapping to `Spec R`.

This is the pairwise-chart form of the compatibility that a global morphism `X_{/Y} ⟶ X` glues
from: on a separated scheme the affine charts of the completion glue along common basic opens, and
this says the canonical morphisms of the two affine completions agree over such an overlap.

Given `basicOpenImmersion_eq_map` it is exactly `formalCompletion.map_comp_toSpec`, the naturality
of `toSpec` in the pair `(Spec R, V(I))`. -/
theorem basicOpenImmersion_comp_toSpec :
    (basicOpenImmersion I hI f).toLRSHom ≫ toSpec R I hI =
      toSpec (Localization.Away f) (I.map (algebraMap R (Localization.Away f)))
          (hI.map (algebraMap R (Localization.Away f))) ≫
        Spec.locallyRingedSpaceMap (CommRingCat.ofHom (algebraMap R (Localization.Away f))) := by
  rw [basicOpenImmersion_eq_map]
  exact map_comp_toSpec hI (hI.map (algebraMap R (Localization.Away f)))
    (algebraMap R (Localization.Away f)) (le_of_eq rfl)

/-! ### The range of the immersion, read through `formalCompletion.toSpec`

`formalCompletion.range_basicOpenImmersion` (`FormalSchemes.CompletionBasicOpen`) computes the
range of the basic-open completion immersion as the basic open `D(f̂)` of `Spf R^`; the
`formalCompletion.toSpec` square above is what turns that into a statement about the ambient
`Spec R`, and the two directions of it are what a gluing argument needs on either side of a chart
boundary. -/

/-- **A point of `Spf R^` is in `D(f̂)` exactly when it lies over a prime avoiding `f`.**

The range of the basic-open completion immersion is `D(f̂)`
(`formalCompletion.range_basicOpenImmersion`), and the base map of `formalCompletion.toSpec` is
`Spec` of the residue map `R →+* R^ ⧸ I·R^` (`formalCompletion.toSpec_base_eq_comap`), which
sends `f` to the residue of `f̂`. So the two conditions are the same condition, and the
membership statement is `FormalSpectrum.mem_basicOpen` read at `f̂`. -/
theorem mem_range_basicOpenImmersion_iff
    (x : FormalSpectrum (AdicCompletion.idealOfDefinition I)) :
    x ∈ Set.range (basicOpenImmersion I hI f).toLRSHom.base ↔
      f ∉ ((toSpec R I hI).base x).asIdeal := by
  rw [range_basicOpenImmersion, toSpec_base_eq_comap]
  exact FormalSpectrum.mem_basicOpen _ _ _

/-- **A point of `Spf R^` lying over a prime not containing `f` is in `D(f̂)`.** The direction of
`formalCompletion.mem_range_basicOpenImmersion_iff` that carries a point of one chart into an
overlap. -/
theorem mem_range_basicOpenImmersion
    (x : FormalSpectrum (AdicCompletion.idealOfDefinition I))
    (hx : f ∉ ((toSpec R I hI).base x).asIdeal) :
    x ∈ Set.range (basicOpenImmersion I hI f).toLRSHom.base :=
  (mem_range_basicOpenImmersion_iff I hI f x).mpr hx

/-- **A point of `Spf R^` lying over a prime containing `f` is outside `D(f̂)`.** The direction of
`formalCompletion.mem_range_basicOpenImmersion_iff` that keeps a point out of an overlap, and
hence exhibits it as doubled by a gluing along that overlap. -/
theorem notMem_range_basicOpenImmersion
    (x : FormalSpectrum (AdicCompletion.idealOfDefinition I))
    (hx : f ∈ ((toSpec R I hI).base x).asIdeal) :
    x ∉ Set.range (basicOpenImmersion I hI f).toLRSHom.base :=
  fun hmem => (mem_range_basicOpenImmersion_iff I hI f x).mp hmem hx

end formalCompletion
