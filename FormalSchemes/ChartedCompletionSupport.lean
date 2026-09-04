import FormalSchemes.ChartedCompletionRange
import FormalSchemes.ChartedSchemeDatumChartOverlap
import FormalSchemes.CompletionTwoPatchSupport

set_option linter.style.header false

/-!
# `X_{/Y}` is supported on `Y`, chart by chart, at an arbitrary index (EGA I, 10.8)

`FormalSchemes.ChartedCompletionRange` computes the image of `X_{/Y} ⟶ X` for a
`AlgebraicGeometry.ChartedCompletionDatum` as a union over the charts,

```
range (D.toScheme).base = ⋃ i, (specι i) '' V (K i)
```

and stops there, on the ground that a union over the whole index type says nothing about what any
**single** chart sees. This file supplies that:

```
(specι i)⁻¹ (range (D.toScheme).base) = V (K i)
```

which is EGA I 10.8 — *the completion of `X` along `Y` is supported on `Y`* — read on each chart of
`X`. At two patches it is `AlgebraicGeometry.preimage_range_completionTwoPatchToScheme_base_ι₀`
and its `ι₁` twin (`FormalSchemes.CompletionTwoPatchSupport`); this is those two, at an arbitrary
index and in one statement.

## Where `hθ` is spent, and why it could not have been spent earlier

`FormalSchemes.CompletionTwoPatchSupport`'s "Why `hθ` had to appear here and nowhere earlier"
section is the map, and it survives the generalisation verbatim: every glued-completion statement
before this file — `completionGlued`, `toScheme`, `range_toScheme_base` — is equally true of an
*incompatible* gluing, and the chart preimage above is the first one that is not. The `j ≠ i` terms
of the union reach the `i`-th chart only inside `D (g i j)`, and **where** inside is exactly what
`hθ` decides.

Concretely the work splits as it does two patches down, and the first two layers are reused rather
than restated, since they were already stated for an arbitrary `(A, I, a)` and `(B, J, b)`:

* **Localization** — `AlgebraicGeometry.zeroLocus_map_away_eq_preimage` and
  `AlgebraicGeometry.image_zeroLocus_map_away`.
* **Transport** — `AlgebraicGeometry.comap_θ_symm_preimage_zeroLocus`, which turns `hθ` from an
  equality of ideals into an equality of sets of primes.
* **Glue** — `AlgebraicGeometry.ChartedSchemeDatum.preimage_image_specι`
  (`FormalSchemes.ChartedSchemeDatumChartOverlap`), the brick this file was waiting on: it says not
  merely that the charts of the glued scheme meet *exactly* over `D (g i j)`
  (`..preimage_range_specι`, the `U = Set.univ` case) but **which** part of the `i`-th chart the
  image of a given subset of the `j`-th chart is. That refinement is what leaves this file with
  nothing to do but rewrite: the localization and transport layers above turn the middle preimage
  into `V (K i · (C i)_{g i j})` and its image into `V (K i) ∩ D (g i j)`.

## Properness, which the range computation alone could not give

`FormalSchemes.ChartedCompletionRange` records that an equality of sets is compatible with the
image being everything, and that the arbitrary-index datum had no analogue of
`AlgebraicGeometry.notMem_range_completionTwoPatchToScheme_base`. The chart preimage supplies one
immediately: a point of the `i`-th chart outside `V (K i)` is not in the image
(`..notMem_range_toScheme_base`). At `AlgebraicGeometry.projectiveLineDatum` this is sharp — the
second chart's ideal is `⊤`, so the **whole** second chart misses the image, and the image is not
all of the projective line as soon as `R` is nontrivial.

## What is *not* proved

* **Closedness is not proved *here*.** It is the last step of the chain and it is downstream of
  this file rather than in it: `FormalSchemes.ChartedCompletionClosed` runs
  `FormalSchemes.CompletionTwoPatchClosed`'s complement argument at an arbitrary index off the
  statement below. Nothing else is needed from the mathematics; that file is topology.
* **`Topology.IsClosedEmbedding` is not proved here, and is no longer out of reach at either
  index.** It needs injectivity of the base map, whose mixed-chart case needs the converse of
  `FormalSchemes.CompletionTwoPatchDoubled`'s overlap analysis; that converse is
  `formalCompletion.mem_range_basicOpenImmersion` (`FormalSchemes.CompletionBasicOpenMap`). Two
  patches down the statement is
  `AlgebraicGeometry.isClosedEmbedding_completionTwoPatchToScheme_base`
  (`FormalSchemes.CompletionTwoPatchEmbedding`), and at an arbitrary index it is
  `AlgebraicGeometry.ChartedCompletionDatum.isClosedEmbedding_toScheme_base`
  (`FormalSchemes.ChartedCompletionEmbedding`), a leaf downstream of this file.

## Main results

* `AlgebraicGeometry.ChartedCompletionDatum.preimage_range_specι` and `..preimage_image_specι`:
  the `Spec`-side bricks, read at a completion datum.
* `AlgebraicGeometry.ChartedCompletionDatum.preimage_image_zeroLocus_specι`: **where `hθ` is
  spent** — the `j`-th chart's zero locus meets the `i`-th chart in `V (K i) ∩ D (g i j)`.
* `AlgebraicGeometry.ChartedCompletionDatum.preimage_range_toScheme_base`: **the support
  statement.**
* `AlgebraicGeometry.ChartedCompletionDatum.notMem_range_toScheme_base`: properness, chart by
  chart.
* `AlgebraicGeometry.preimage_range_projectiveLineCompletionToScheme_base_true` and
  `AlgebraicGeometry.range_projectiveLineCompletionToScheme_base_ne_univ`: the witness — the
  completion of the projective line at the origin of its first chart misses the second chart
  entirely.
* `AlgebraicGeometry.preimage_range_projectiveLine_specι` and
  `AlgebraicGeometry.projectiveLine_specι_false_base_notMem_range`: the same picture one layer
  down, at the **ambient** projective line — its two charts meet exactly over `D(X)`, so a prime
  containing `X` is outside the second chart altogether.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

namespace ChartedCompletionDatum

variable (D : ChartedCompletionDatum.{u})

/-! ### The `Spec`-side brick, at a completion datum -/

/-- **The charts of the glued ambient scheme meet exactly over `D (g i j)`**, read at this datum. -/
theorem preimage_range_specι (i j : D.J) (h : i ≠ j) :
    ⇑(D.specι i).base ⁻¹' Set.range ⇑(D.specι j).base =
      (PrimeSpectrum.basicOpen (D.g i j) : Set (PrimeSpectrum (D.C i))) :=
  D.toChartedSchemeDatum.preimage_range_specι i j h

/-- **The part of the `i`-th chart that lands in a given subset of the `j`-th**, read at this
datum. -/
theorem preimage_image_specι (i j : D.J) (h : i ≠ j) (U : Set (PrimeSpectrum (D.C j))) :
    ⇑(D.specι i).base ⁻¹' (⇑(D.specι j).base '' U) =
      PrimeSpectrum.comap (algebraMap (D.C i) (Localization.Away (D.g i j))) ''
        (PrimeSpectrum.comap (D.θ i j h).symm.toRingHom ⁻¹'
          (PrimeSpectrum.comap (algebraMap (D.C j) (Localization.Away (D.g j i))) ⁻¹' U)) :=
  D.toChartedSchemeDatum.preimage_image_specι i j h U

/-- The chart inclusions of the glued ambient scheme are injective on points. -/
theorem specι_base_injective (i : D.J) : Function.Injective ⇑(D.specι i).base :=
  (D.toChartedSchemeDatum.specι_isOpenImmersion i).base_open.injective

/-! ### Where `hθ` is spent -/

/-- **The part of the `i`-th chart lying over the `j`-th chart's zero locus is
`V (K i) ∩ D (g i j)`.**

`preimage_image_specι` already says that the left-hand side is the image, under the chart of
`D (g i j)`, of the `θ i j`-translate of the overlap's preimage of `V (K j)` — a statement about the
glued **scheme**, with no ideal in it. Three rewrites finish: the innermost preimage is
`V (K j · (C j)_{g j i})` (`zeroLocus_map_away_eq_preimage`); `hθ` turns its `θ i j`-translate into
`V (K i · (C i)_{g i j})` (`comap_θ_symm_preimage_zeroLocus`); and the image of that is
`V (K i) ∩ D (g i j)` (`image_zeroLocus_map_away`).

**The middle step is where the compatibility hypothesis does its work**, exactly as
`AlgebraicGeometry.preimage_image_zeroLocus_specTwoPatchι₁` does two patches down, and rerouting the
set-theoretic bookkeeping around it through the topological gluing does not move it: `hθ` is still
the only reason a prime of `D (g i j)` lands where it does. -/
theorem preimage_image_zeroLocus_specι (i j : D.J) (h : i ≠ j) :
    ⇑(D.specι i).base ⁻¹'
        (⇑(D.specι j).base '' PrimeSpectrum.zeroLocus ((D.K j : Ideal (D.C j)) : Set (D.C j))) =
      PrimeSpectrum.zeroLocus ((D.K i : Ideal (D.C i)) : Set (D.C i)) ∩
        PrimeSpectrum.basicOpen (D.g i j) := by
  rw [D.preimage_image_specι i j h, ← zeroLocus_map_away_eq_preimage (D.K j) (D.g j i),
    comap_θ_symm_preimage_zeroLocus (D.K i) (D.g i j) (D.K j) (D.g j i) (D.θ i j h) (D.hθ i j h),
    image_zeroLocus_map_away (D.K i) (D.g i j)]

/-! ### The support statement -/

/-- **The glued completion is supported on `V (K i)`, seen on the `i`-th chart** (EGA I, 10.8).

The image of `X_{/Y} ⟶ X` meets the `i`-th chart of `X` exactly in the closed set `V (K i)`: the
`i`-th term of `ChartedCompletionDatum.range_toScheme_base` contributes `V (K i)` by injectivity of
the chart, and every other term contributes `V (K i) ∩ D (g i j)`, which is already inside it. -/
theorem preimage_range_toScheme_base (i : D.J) :
    ⇑(D.specι i).base ⁻¹' Set.range ⇑D.toScheme.base =
      PrimeSpectrum.zeroLocus ((D.K i : Ideal (D.C i)) : Set (D.C i)) := by
  rw [D.range_toScheme_base, Set.preimage_iUnion]
  refine subset_antisymm (Set.iUnion_subset fun j => ?_) fun p hp =>
    Set.mem_iUnion.mpr ⟨i, Set.mem_preimage.mpr ⟨p, hp, rfl⟩⟩
  by_cases hj : i = j
  · subst hj
    rw [Set.preimage_image_eq _ (D.specι_base_injective i)]
  · rw [D.preimage_image_zeroLocus_specι i j hj]
    exact Set.inter_subset_left

/-- **Properness, chart by chart**: a point of the `i`-th chart outside `V (K i)` is not in the
image of `X_{/Y} ⟶ X`. This is what an equality of sets does *not* give on its own, and it is the
arbitrary-index form of `AlgebraicGeometry.notMem_range_completionTwoPatchToScheme_base`. -/
theorem notMem_range_toScheme_base (i : D.J) {p : PrimeSpectrum (D.C i)}
    (hp : p ∉ PrimeSpectrum.zeroLocus ((D.K i : Ideal (D.C i)) : Set (D.C i))) :
    (D.specι i).base p ∉ Set.range ⇑D.toScheme.base := by
  intro hmem
  exact hp ((D.preimage_range_toScheme_base i).subset hmem)

/-- **A `⊤`-chart is missed entirely.** If the `i`-th ideal is the unit ideal then the image of
`X_{/Y} ⟶ X` meets the `i`-th chart nowhere. -/
theorem preimage_range_toScheme_base_eq_empty {i : D.J} (hi : D.K i = ⊤) :
    ⇑(D.specι i).base ⁻¹' Set.range ⇑D.toScheme.base = ∅ := by
  rw [D.preimage_range_toScheme_base i, hi, Submodule.top_coe, PrimeSpectrum.zeroLocus_univ]
  rfl

end ChartedCompletionDatum

/-! ### The witness: the projective line completed at the origin of its first chart -/

section Witness

open Polynomial

variable (R : Type u) [CommRing R]

/-- **The completion of the projective line at the origin of its first chart misses the second
chart entirely.** The second chart's ideal is `⊤`, so its preimage of the image is `V (⊤) = ∅`.

This is the statement `FormalSchemes.ChartedCompletionRange` could not make: there the `⊤`-chart
merely fails to *contribute* a term to the union, which is compatible with its being covered by the
other term; here it is genuinely disjoint from the image. -/
theorem preimage_range_projectiveLineCompletionToScheme_base_true :
    ⇑((projectiveLineDatum R).specι ⟨true⟩).base ⁻¹'
        Set.range ⇑(projectiveLineCompletionToScheme R).base = ∅ :=
  (projectiveLineDatum R).preimage_range_toScheme_base_eq_empty (projectiveLineDatum_K_true R)

/-- **The completion of the projective line at the origin of its first chart is supported on the
origin**, seen on the first chart: `V (X)` and nothing more. -/
theorem preimage_range_projectiveLineCompletionToScheme_base_false :
    ⇑((projectiveLineDatum R).specι ⟨false⟩).base ⁻¹'
        Set.range ⇑(projectiveLineCompletionToScheme R).base =
      PrimeSpectrum.zeroLocus ((Ideal.span {(X : R[X])} : Ideal R[X]) : Set R[X]) :=
  (projectiveLineDatum R).preimage_range_toScheme_base ⟨false⟩

/-! #### The ambient scheme, one layer below the completion -/

/-- **The two charts of the projective line meet exactly over `D(X)`.** The part of the first chart
`Spec R[X]` that lands in the second is the complement of the origin, which is what the projective
line is glued along.

This is `AlgebraicGeometry.ChartedSchemeDatum.preimage_range_specι` at the sharpest datum on the
tree, with `AlgebraicGeometry.projectiveLineDatum_g_false_true` naming the away element, and it is
a statement about the **ambient** scheme rather than about its completion — one
layer below the rest of this section. It lives here because this is the first file that imports
both `FormalSchemes.ChartedSchemeDatumChartOverlap` and
`FormalSchemes.ProjectiveLineCompletion`; putting it in either of those would drag the other into
its import closure for two witnesses. -/
theorem preimage_range_projectiveLine_specι :
    ⇑((projectiveLineDatum R).specι ⟨false⟩).base ⁻¹'
        Set.range ⇑((projectiveLineDatum R).specι ⟨true⟩).base =
      (PrimeSpectrum.basicOpen (X : R[X]) : Set (PrimeSpectrum R[X])) := by
  rw [← projectiveLineDatum_g_false_true R]
  exact (projectiveLineDatum R).preimage_range_specι ⟨false⟩ ⟨true⟩ cgcNe

/-- **The origin of the first chart of the projective line is not in the second chart.** A prime of
`R[X]` containing `X` lies outside `D(X)`, hence outside the overlap, hence its image in
`projectiveLine R` is not reached by the second chart at all.

The point it produces is the one the completion is supported at — `K ⟨false⟩` is
`Ideal.span {X}` — so this is the ambient-scheme reason the support statement above cannot leak
into the second chart. -/
theorem projectiveLine_specι_false_base_notMem_range (p : PrimeSpectrum R[X])
    (hp : (X : R[X]) ∈ p.asIdeal) :
    ((projectiveLineDatum R).specι ⟨false⟩).base p ∉
      Set.range ⇑((projectiveLineDatum R).specι ⟨true⟩).base := by
  intro hmem
  refine (PrimeSpectrum.mem_basicOpen (X : R[X]) p).mp ?_ hp
  exact (preimage_range_projectiveLine_specι R).subset hmem

/-- **The image is proper.** As soon as `R` is nontrivial the second chart of the projective line
has points, and by `preimage_range_projectiveLineCompletionToScheme_base_true` none of them is in
the image of `X_{/Y} ⟶ X`. -/
theorem range_projectiveLineCompletionToScheme_base_ne_univ [Nontrivial R] :
    Set.range ⇑(projectiveLineCompletionToScheme R).base ≠ Set.univ := by
  intro huniv
  obtain ⟨q⟩ : Nonempty (PrimeSpectrum R[X]) := inferInstance
  have hmem : ((projectiveLineDatum R).specι ⟨true⟩).base q ∈
      Set.range ⇑(projectiveLineCompletionToScheme R).base := by
    rw [huniv]
    exact Set.mem_univ _
  have hempty := preimage_range_projectiveLineCompletionToScheme_base_true R
  rw [Set.eq_empty_iff_forall_notMem] at hempty
  exact hempty q hmem

end Witness

end AlgebraicGeometry

end
