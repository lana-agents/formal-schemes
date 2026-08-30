import FormalSchemes.TateInvGlobalProperness
import FormalSchemes.TateInvPatchSaturateCharts

set_option linter.style.header false

/-!
# The node chart's domain: `D(x + y − 1)` on the model patch

`AlgebraicGeometry.tateInvPeriodQuotientFormalSchemeOfNodeChart`
(`FormalSchemes.TateInvPeriodQuotientCharts`) reduced "is `T_inv/⟨σ⟩` a formal scheme?" to a chart
at the node locus of one patch, and `FormalSchemes.TateInvChartAnnulusRing` computed
`Γ (T_inv/⟨σ⟩, π V)` for `V` the saturation of an **arbitrary** open `S ⊆ Spf A`. Every statement
in that chain leaves `S` a variable. This file chooses one.

The choice is the basic open

```
S = D(x + y − 1) ⊆ Spf A,      A = R{x, y}/(x·y − q)
```

and the two facts that make it a candidate node chart are that it **contains the whole node
locus** and that it is **its own saturation**, so the open of the chain it generates is proper.

## Why this `S`, and why the saturation matters

The naive choice, "delete a closed subset of the patch that misses the nodes", is not enough: the
saturation of `S` is read on the model patch as `AlgebraicGeometry.tateInvChartSaturate`
(`FormalSchemes.TateInvPatchSaturateCharts`), which adds to `S` what the two neighbouring patches
see of their own copies of `S` through the `𝔾m`-inversion transition.

The naive choice `D(x − 1)` — delete one point of the special fibre's `x`-branch and nothing on
the `y`-branch — **fails, and that is proved here, not asserted**:
`AlgebraicGeometry.tateInvChartSaturate_tateInvNaiveChartLocus` says its saturation is all of
`Spf A`. The mechanism is that `legYX (x − 1) = q·legX x − 1` is congruent to `−1` modulo the
ideal of definition, so the neighbouring patch pulls the whole chart back
(`AlgebraicGeometry.basicOpen_tateInvGlobalLegYX_overlapX_sub_one`), contributing `D(x)`; and
`D(x − 1) ∪ D(x)` is everything, since a prime containing both `x` and `x − 1` contains `1`. So
`π V` would be the whole quotient, which cannot be an affine chart because the Néron 1-gon is
proper. Note `D(x − 1)` contains the node locus just as `D(x + y − 1)` does
(`AlgebraicGeometry.tateInvNodeLocus_subset_tateInvNaiveChartLocus`), so containing the nodes is
**not** what separates the two candidates.

The geometric picture behind the choice — **not proved here**, see "What is *not* proved"
below — is that `x + y − 1` deletes a point of each branch, and that the transition exchanges
the two. What *is* proved is that the two witnesses `AlgebraicGeometry.annulusUnitPointX` and
`AlgebraicGeometry.annulusUnitPointY` lie outside the domain, which is all the properness
statements consume. Concretely, in the `Ĝm` coordinates of
`FormalSchemes.TateInvGlobalProperness` the two legs out of `A` into `A{1/x}` send

```
x + y − 1  ↦  X + q·X⁻¹ − 1        (the x-chart leg)
x + y − 1  ↦  q·X + X⁻¹ − 1        (the transition-then-y-chart leg)
```

and modulo the ideal of definition, where `q = 0`, the second is `−X⁻¹` times the first. So the
two cut out the **same** basic open of `Spf A{1/x}`, and the extra pieces of the saturation
collapse into `S`.

That last step is proved here without dividing by anything: the two exact identities

```
legX x  · legYX g + legX g  = q · (legX x ^ 2  + legYX y)
legYX y · legX g  + legYX g = q · (legYX y ^ 2 + legX x)
```

for `g = x + y − 1` hold in `A{1/x}`, and each of them turns membership of one residue in a prime
into membership of the other (`AlgebraicGeometry.basicOpen_eq_of_mul_add_mem`). Both are instances
of one commutative-ring identity, `AlgebraicGeometry.nodeChartCoord_crux`, from `x·y = q`,
`legYX x = q · legX x` (`AlgebraicGeometry.tateInvGlobalLegYX_overlapX`) and
`legYX y · legX x = 1` (`AlgebraicGeometry.tateInvGlobalLegYX_overlapY_mul_legX_overlapX`, the
one new coordinate computation in this file, proved by the route of
`tateInvGlobalLegYX_overlapX`).

## Main definitions and results

* `AlgebraicGeometry.annulusNodeChartCoord`, `AlgebraicGeometry.tateInvNodeChartLocus`: the
  coordinate `x + y − 1` and the basic open it cuts out, with `isOpen_tateInvNodeChartLocus` and
  `mem_tateInvNodeChartLocus_iff`.
* **`AlgebraicGeometry.tateInvNodeLocus_subset_tateInvNodeChartLocus`**: it contains every node.
  At a node both `x` and `y` lie in the prime, so `x + y − 1` cannot.
* `AlgebraicGeometry.annulusUnitEvalX`, `annulusUnitEvalY` and the two points
  `AlgebraicGeometry.annulusUnitPointX`, `annulusUnitPointY`: evaluation of the special fibre at
  `x = 1, y = 0` and at `x = 0, y = 1`. Neither is in the domain
  (`annulusUnitPointX_notMem_tateInvNodeChartLocus` and its mirror) and each is in the
  corresponding overlap chart, so the deleted points are **charted** points, not nodes.
* **`AlgebraicGeometry.tateInvNodeChartLocus_ne_univ`** and
  `AlgebraicGeometry.tateInvNodeChartLocus_nonempty`: for `I ≠ ⊤` the domain is a proper nonempty
  open — the same standing hypothesis, for the same reason, as
  `AlgebraicGeometry.tateInvNodeLocus_nonempty`.
* **`AlgebraicGeometry.tateInvChartSaturate_tateInvNodeChartLocus`**: the domain is its own
  saturation. Hence `AlgebraicGeometry.tateInvPatchSaturate_tateInvNodeChartLocus` and its `Opens`
  form: the chart ring's ambient open is `D(x + y − 1)` itself. It is the first *proper nonempty*
  `S` on this tree for which the ambient open is the `S` one started from; the two trivial ones,
  `AlgebraicGeometry.tateInvPatchSaturate_univ` (`FormalSchemes.TateInvNodeChartRing`) and
  `AlgebraicGeometry.tateInvPatchSaturate_empty` (`FormalSchemes.TateInvChartAnnulusRing`), were
  already on the tree.
* **`AlgebraicGeometry.tateInvSaturate_tateInvNodeChartLocus_ne_univ`** and
  **`AlgebraicGeometry.image_base_tateInvSaturate_tateInvNodeChartLocus_ne_univ`**: the
  `σ`-invariant open of the chain, and its image in the quotient, are **proper**. This is what a
  whole patch fails and is why the choice of `S` is not cosmetic.
* **`AlgebraicGeometry.tateInvPeriodQuotientFormalSchemeOfNodeChartLocus`**: the reduction, at the
  chosen domain — `T_inv/⟨σ⟩` is a formal scheme as soon as every point of
  `π '' tateInvSaturate D(x + y − 1)` has an affine formal chart.
* **`AlgebraicGeometry.tateInvNaiveChartLocus`** and
  **`AlgebraicGeometry.tateInvChartSaturate_tateInvNaiveChartLocus`**: the competing choice
  `D(x − 1)`, and the theorem that its saturation is everything —
  while `AlgebraicGeometry.tateInvNaiveChartLocus_ne_univ` says it is itself a proper open, so the
  contrast is not vacuous. Two general lemmas are used and stated for an arbitrary ideal:
  `AlgebraicGeometry.basicOpen_eq_of_sub_mem` and `AlgebraicGeometry.basicOpen_neg_one`.
* `AlgebraicGeometry.tateInvNodeChartSubring` and
  `AlgebraicGeometry.exists_tateInvNodeChartRingEquiv`: the candidate ring, named at this `S`.
  These two are instantiations of `AlgebraicGeometry.tateInvChartAnnulusSubring` and
  `AlgebraicGeometry.exists_tateInvChartAnnulusRingEquiv` and contain no new content; they exist so
  that the object the remaining work is about has a name.

Two general lemmas are proved on the way and are stated for an arbitrary commutative ring:
`AlgebraicGeometry.nodeChartCoord_crux` and `AlgebraicGeometry.basicOpen_eq_of_mul_add_mem` (two
elements each of which is a multiple of the other modulo the ideal of definition, up to sign, cut
out the same basic open — no primality and no unit is used).

## What is *not* proved

**`hnode` is still undecided, and nothing here is a chart.** No adic structure is put on
`tateInvNodeChartSubring` and no morphism of locally ringed spaces out of its formal spectrum is
constructed. What this file does is fix the `S` that every previous statement left variable, and
show that the resulting candidate domain has the two properties a node chart must have: it covers
the uncharted locus, and it is not the whole quotient.

**Nothing here says the ring is nonzero, proper, or bigger than `R`.** Issue 1223's goal 3 is
untouched. `AlgebraicGeometry.tateInvChartAnnulusSubring_univ_ne_top`
(`FormalSchemes.TateInvGlobalProperness`) is a statement at `S = Set.univ` and says nothing here.

**The complement of the domain is not identified, and is not shown to be a single `σ`-orbit.**
What is proved is that two specific points lie outside it
(`AlgebraicGeometry.annulusUnitPointX_notMem_tateInvNodeChartLocus` and its mirror), which is
what the properness statements consume. That the complement is exactly
`V(x − 1, y) ∪ V(x, y − 1)`, that those are one point of each branch, that the transition
exchanges them, and that they form one orbit of one point of the quotient are all the geometric
reading and none of them is formalised. The first of them is true and short — from `x·y = 0` in
the special fibre, `x + y − 1 ∈ 𝔭` gives `x·(x − 1) ∈ 𝔭` — and a successor wanting an explicit
description of the uncharted part of this domain should land it as a theorem rather than cite
this paragraph.

Nothing here weakens `LocallyRingedSpace.IsProperlyDiscontinuousOn`,
`LocallyRingedSpace.IsFreeProperlyDiscontinuous` or
`LocallyRingedSpace.freeActionQuotientFormalScheme`, and no chart is produced by any route.

## References

* [Deligne–Rapoport, *Les schémas de modules de courbes elliptiques*], II.1 — the Néron `n`-gon;
  the affine chart at the node of the 1-gon is the complement of one point of the component.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
-/
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum TopologicalSpace
open Opposite TopCat.Presheaf RestrictedLaurentSeries

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)

/-- The coordinate `x + y − 1` of the model patch `A = R{x, y}/(x·y − q)`. -/
def annulusNodeChartCoord : annulusAlgebra R I q :=
  overlapX R I q + overlapY R I q - 1

/-- The node chart's domain on the model patch: the basic open `D(x + y − 1) ⊆ Spf A`. -/
def tateInvNodeChartLocus : Set (FormalSpectrum.locallyRingedSpaceObj
    (annulusIdealOfDefinition R I q)) :=
  (basicOpen (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) :
    Set (FormalSpectrum (annulusIdealOfDefinition R I q)))

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
theorem isOpen_tateInvNodeChartLocus : IsOpen (tateInvNodeChartLocus R I q) :=
  (basicOpen (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)).2

variable {R I q}

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
theorem mem_tateInvNodeChartLocus_iff {z : FormalSpectrum.locallyRingedSpaceObj
    (annulusIdealOfDefinition R I q)} :
    z ∈ tateInvNodeChartLocus R I q ↔
      fibreX R I q + fibreY R I q - 1 ∉ (z : PrimeSpectrum (annulusFibre R I q)).asIdeal := by
  rw [tateInvNodeChartLocus]
  rw [show (fibreX R I q + fibreY R I q - 1) =
    Ideal.Quotient.mk (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) by
      simp [annulusNodeChartCoord, fibreX, fibreY]]
  exact mem_basicOpen _ _ _

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
theorem tateInvNodeLocus_subset_tateInvNodeChartLocus (hI : I.FG) :
    tateInvNodeLocus R I q ⊆ tateInvNodeChartLocus R I q := by
  intro z hz
  rw [mem_tateInvNodeLocus_iff] at hz
  obtain ⟨hx, hy⟩ := hz
  have hxmem : fibreX R I q ∈ (z : PrimeSpectrum (annulusFibre R I q)).asIdeal := by
    by_contra hc
    refine hx ?_
    rw [range_annulusOverlapChart_base R I q hI]
    exact (mem_basicOpen _ _ _).mpr hc
  have hymem : fibreY R I q ∈ (z : PrimeSpectrum (annulusFibre R I q)).asIdeal := by
    by_contra hc
    refine hy ?_
    rw [show annulusOverlapChartY R I q =
        FormalSpectrum.basicOpenChart _ (overlapY R I q) from rfl,
      range_basicOpenChart_base _ (overlapY R I q) (annulusIdealOfDefinition_fg R I q hI)]
    exact (mem_basicOpen _ _ _).mpr hc
  rw [mem_tateInvNodeChartLocus_iff]
  intro hc
  have hone : (1 : annulusFibre R I q) ∈ (z : PrimeSpectrum (annulusFibre R I q)).asIdeal := by
    have := sub_mem (add_mem hxmem hymem) hc
    simpa using this
  exact (z : PrimeSpectrum (annulusFibre R I q)).isPrime.ne_top
    (Ideal.eq_top_iff_one _ |>.mpr hone)

section UnitPoint

variable (R I q)
variable (𝔭 : Ideal R) [𝔭.IsPrime] (h𝔭 : I ≤ 𝔭)

include h𝔭 hq in
/-- **Evaluation of the special fibre at `x = 1`, `y = 0`**, with values in the domain `R ⧸ 𝔭`.
The relation `x·y = q` holds because `q ∈ I` dies in `R ⧸ 𝔭`. -/
def annulusUnitEvalX : annulusFibre R I q →+* R ⧸ 𝔭 :=
  annulusFibreEval R I q (map_algebraMap_le_bot_quotient R I 𝔭 h𝔭) ![1, 0] <| by
    rw [algebraMap_q_eq_zero_quotient R I q 𝔭 h𝔭 hq]
    simp

include h𝔭 hq in
/-- **Evaluation of the special fibre at `x = 0`, `y = 1`** — the mirror of
`AlgebraicGeometry.annulusUnitEvalX`. -/
def annulusUnitEvalY : annulusFibre R I q →+* R ⧸ 𝔭 :=
  annulusFibreEval R I q (map_algebraMap_le_bot_quotient R I 𝔭 h𝔭) ![0, 1] <| by
    rw [algebraMap_q_eq_zero_quotient R I q 𝔭 h𝔭 hq]
    simp

/-- The point `x = 1, y = 0` of `Spf A` over `𝔭`. -/
def annulusUnitPointX :
    FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q) :=
  PrimeSpectrum.comap (annulusUnitEvalX R I q hq 𝔭 h𝔭) ⟨⊥, Ideal.isPrime_bot⟩

/-- The point `x = 0, y = 1` of `Spf A` over `𝔭`. -/
def annulusUnitPointY :
    FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q) :=
  PrimeSpectrum.comap (annulusUnitEvalY R I q hq 𝔭 h𝔭) ⟨⊥, Ideal.isPrime_bot⟩

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
theorem annulusUnitPointX_notMem_tateInvNodeChartLocus :
    annulusUnitPointX R I q hq 𝔭 h𝔭 ∉ tateInvNodeChartLocus R I q := by
  rw [mem_tateInvNodeChartLocus_iff, not_not]
  change _ ∈ Ideal.comap _ _
  rw [Ideal.mem_comap, Ideal.mem_bot, map_sub, map_add, map_one, annulusUnitEvalX,
    annulusFibreEval_fibreX, annulusFibreEval_fibreY]
  simp

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
theorem annulusUnitPointY_notMem_tateInvNodeChartLocus :
    annulusUnitPointY R I q hq 𝔭 h𝔭 ∉ tateInvNodeChartLocus R I q := by
  rw [mem_tateInvNodeChartLocus_iff, not_not]
  change _ ∈ Ideal.comap _ _
  rw [Ideal.mem_comap, Ideal.mem_bot, map_sub, map_add, map_one, annulusUnitEvalY,
    annulusFibreEval_fibreX, annulusFibreEval_fibreY]
  simp

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
theorem annulusUnitPointX_mem_range_annulusOverlapChart (hI : I.FG) :
    annulusUnitPointX R I q hq 𝔭 h𝔭 ∈ Set.range (annulusOverlapChart R I q).base := by
  rw [range_annulusOverlapChart_base R I q hI]
  refine (mem_basicOpen _ _ _).mpr ?_
  change fibreX R I q ∉ Ideal.comap _ _
  rw [Ideal.mem_comap, Ideal.mem_bot, annulusUnitEvalX, annulusFibreEval_fibreX]
  simp

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
theorem annulusUnitPointY_mem_range_annulusOverlapChartY (hI : I.FG) :
    annulusUnitPointY R I q hq 𝔭 h𝔭 ∈ Set.range (annulusOverlapChartY R I q).base := by
  rw [show annulusOverlapChartY R I q = FormalSpectrum.basicOpenChart _ (overlapY R I q) from rfl,
    range_basicOpenChart_base _ (overlapY R I q) (annulusIdealOfDefinition_fg R I q hI)]
  refine (mem_basicOpen _ _ _).mpr ?_
  change fibreY R I q ∉ Ideal.comap _ _
  rw [Ideal.mem_comap, Ideal.mem_bot, annulusUnitEvalY, annulusFibreEval_fibreY]
  simp

end UnitPoint

variable (R I q)

include hq in
omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
theorem tateInvNodeChartLocus_ne_univ (hItop : I ≠ ⊤) :
    tateInvNodeChartLocus R I q ≠ Set.univ := by
  obtain ⟨𝔪, h𝔪, h𝔪le⟩ := Ideal.exists_le_maximal I hItop
  haveI : 𝔪.IsPrime := h𝔪.isPrime
  intro hc
  exact annulusUnitPointX_notMem_tateInvNodeChartLocus R I q hq 𝔪 h𝔪le (by rw [hc]; trivial)

include hq in
omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
theorem tateInvNodeChartLocus_nonempty (hI : I.FG) (hItop : I ≠ ⊤) :
    (tateInvNodeChartLocus R I q).Nonempty :=
  (tateInvNodeLocus_nonempty R I q hq hI hItop).mono
    (tateInvNodeLocus_subset_tateInvNodeChartLocus hI)

section Quotient

variable {Q : LocallyRingedSpace.{u}}
variable {π : (tateChainInv R I q hq hI).toLocallyRingedSpace ⟶ Q}

/-- **The reduction, at the chosen domain.** -/
def tateInvPeriodQuotientFormalSchemeOfNodeChartLocus
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π)
    (hchart : ∀ z ∈ ⇑π.base '' tateInvSaturate R I q hq hI (tateInvNodeChartLocus R I q),
      LocallyRingedSpace.HasAffineChartAt Q z) :
    FormalScheme.{u} :=
  tateInvPeriodQuotientFormalSchemeOfNodeChart R I q hq hI h fun _ hx hy =>
    hchart _ (Set.mem_image_of_mem _ (image_ι_subset_tateInvSaturate hq hI
      (tateInvNodeChartLocus R I q) ⟨0⟩ (Set.mem_image_of_mem _
        (tateInvNodeLocus_subset_tateInvNodeChartLocus hI
          (mem_tateInvNodeLocus_iff.mpr ⟨hx, hy⟩)))))

@[simp]
theorem tateInvPeriodQuotientFormalSchemeOfNodeChartLocus_toLocallyRingedSpace
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π)
    (hchart : ∀ z ∈ ⇑π.base '' tateInvSaturate R I q hq hI (tateInvNodeChartLocus R I q),
      LocallyRingedSpace.HasAffineChartAt Q z) :
    (tateInvPeriodQuotientFormalSchemeOfNodeChartLocus R I q hq hI h
      hchart).toLocallyRingedSpace = Q := rfl

end Quotient

/-! ### The chosen domain is saturated -/

section Crux

/-- **The algebraic identity behind the saturation of `D(x + y − 1)`**, isolated from the two
rings it will be used in. Read `a = x`, `b = y` in one chart, `c`, `d` their images under the
`𝔾m`-inversion transition, and `q'` the Tate parameter: the three hypotheses are `x·y = q`,
`c = q·a` and `d·a = 1`, and the conclusions say that the transition's value on `x + y − 1` and
the chart's own value on it are unit multiples of each other **up to a multiple of `q`**. -/
theorem nodeChartCoord_crux {T : Type*} [CommRing T] {a b c d q' : T}
    (h1 : a * b = q') (h2 : c = q' * a) (h3 : d * a = 1) :
    a * (c + d - 1) + (a + b - 1) = q' * (a ^ 2 + d) ∧
      d * (a + b - 1) + (c + d - 1) = q' * (d ^ 2 + a) :=
  ⟨by linear_combination a * h2 + (1 - b) * h3 + d * h1,
    by linear_combination h2 + (1 - b * d) * h3 + d ^ 2 * h1⟩

/-- **Two elements whose two `mul`-combinations lie in the ideal of definition cut out the same
basic open.** Each hypothesis turns membership of one residue in a prime into membership of the
other; no primality and no unit is needed. -/
theorem basicOpen_eq_of_mul_add_mem {T : Type u} [CommRing T] (K : Ideal T) {a b : T} (u v : T)
    (h₁ : u * a + b ∈ K) (h₂ : v * b + a ∈ K) :
    basicOpen K a = basicOpen K b := by
  have e₁ : (Ideal.Quotient.mk K) b =
      -((Ideal.Quotient.mk K) u * (Ideal.Quotient.mk K) a) := by
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr h₁
    rw [map_add, map_mul] at h
    linear_combination h
  have e₂ : (Ideal.Quotient.mk K) a =
      -((Ideal.Quotient.mk K) v * (Ideal.Quotient.mk K) b) := by
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr h₂
    rw [map_add, map_mul] at h
    linear_combination h
  refine Opens.ext (Set.ext fun w => ?_)
  rw [SetLike.mem_coe, SetLike.mem_coe, mem_basicOpen, mem_basicOpen]
  refine not_congr ⟨fun ha => ?_, fun hb => ?_⟩
  · rw [e₁]; exact neg_mem (Ideal.mul_mem_left _ _ ha)
  · rw [e₂]; exact neg_mem (Ideal.mul_mem_left _ _ hb)

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- **The transition sends `y` to the inverse of the `x`-chart's `x`.** In `Ĝm` coordinates the
`x`-chart leg sends `x` to `X` and the transition-then-`y`-chart leg sends `y` to
`rlsInv X = X⁻¹`, so their product is `X⁰ = 1`. The mirror, on the other coordinate, of
`AlgebraicGeometry.tateInvGlobalLegYX_overlapX`
(`FormalSchemes.TateInvGlobalProperness`), and proved by that theorem's own route. -/
theorem tateInvGlobalLegYX_overlapY_mul_legX_overlapX (hI : I.FG) :
    tateInvGlobalLegYX (R := R) (I := I) (q := q) hI (overlapY R I q) *
        tateInvGlobalLegX (R := R) (I := I) (q := q) (overlapX R I q) = 1 := by
  refine (annulusChartOverlapAlgX R I q).injective ((overlapEquiv R I q hI).injective ?_)
  rw [map_mul, map_mul, map_one, map_one, annulusChartOverlapAlgX_tateInvGlobalLegYX,
    overlapEquiv_annulusOverlapInversion_symm_algebraMap, annulusFlip_symm_overlapY,
    overlapEquiv_overlapX, rlsInv_X_one, annulusChartOverlapAlgX_tateInvGlobalLegX,
    overlapEquiv_overlapX, X_add]
  norm_num [X_zero]

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- The `x`-chart leg on the chosen coordinate. -/
theorem tateInvGlobalLegX_annulusNodeChartCoord :
    tateInvGlobalLegX (R := R) (I := I) (q := q) (annulusNodeChartCoord R I q) =
      tateInvGlobalLegX (R := R) (I := I) (q := q) (overlapX R I q) +
        tateInvGlobalLegX (R := R) (I := I) (q := q) (overlapY R I q) - 1 := by
  rw [annulusNodeChartCoord, map_sub, map_add, map_one]

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- The transition-then-`y`-chart leg on the chosen coordinate. -/
theorem tateInvGlobalLegYX_annulusNodeChartCoord (hI : I.FG) :
    tateInvGlobalLegYX (R := R) (I := I) (q := q) hI (annulusNodeChartCoord R I q) =
      tateInvGlobalLegYX (R := R) (I := I) (q := q) hI (overlapX R I q) +
        tateInvGlobalLegYX (R := R) (I := I) (q := q) hI (overlapY R I q) - 1 := by
  rw [annulusNodeChartCoord, map_sub, map_add, map_one]

include hq in
omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- The Tate parameter dies in the special fibre of the `x`-chart's coordinate ring. -/
theorem tateInvGlobalLegX_algebraMap_q_mem :
    tateInvGlobalLegX (R := R) (I := I) (q := q)
        (algebraMap R (annulusAlgebra R I q) q) ∈
      awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q) := by
  refine le_comap_awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q) ?_
  rw [← annulus_map_eq]
  exact Ideal.mem_map_of_mem _ hq

include hq in
omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- **The two legs cut out the same basic open of `Spf A{1/x}`.** -/
theorem basicOpen_tateInvGlobalLegYX_annulusNodeChartCoord (hI : I.FG) :
    basicOpen (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
        (tateInvGlobalLegYX (R := R) (I := I) (q := q) hI (annulusNodeChartCoord R I q)) =
      basicOpen (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
        (tateInvGlobalLegX (R := R) (I := I) (q := q) (annulusNodeChartCoord R I q)) := by
  obtain ⟨e₁, e₂⟩ := nodeChartCoord_crux
    (a := tateInvGlobalLegX (R := R) (I := I) (q := q) (overlapX R I q))
    (b := tateInvGlobalLegX (R := R) (I := I) (q := q) (overlapY R I q))
    (c := tateInvGlobalLegYX (R := R) (I := I) (q := q) hI (overlapX R I q))
    (d := tateInvGlobalLegYX (R := R) (I := I) (q := q) hI (overlapY R I q))
    (q' := tateInvGlobalLegX (R := R) (I := I) (q := q)
      (algebraMap R (annulusAlgebra R I q) q))
    (by rw [← map_mul, overlapX_mul_overlapY])
    (by rw [tateInvGlobalLegYX_overlapX, map_mul])
    (tateInvGlobalLegYX_overlapY_mul_legX_overlapX R I q hI)
  refine basicOpen_eq_of_mul_add_mem _
    (tateInvGlobalLegX (R := R) (I := I) (q := q) (overlapX R I q))
    (tateInvGlobalLegYX (R := R) (I := I) (q := q) hI (overlapY R I q)) ?_ ?_
  · rw [tateInvGlobalLegX_annulusNodeChartCoord, tateInvGlobalLegYX_annulusNodeChartCoord, e₁]
    exact Ideal.mul_mem_right _ _ (tateInvGlobalLegX_algebraMap_q_mem R I q hq)
  · rw [tateInvGlobalLegX_annulusNodeChartCoord, tateInvGlobalLegYX_annulusNodeChartCoord, e₂]
    exact Ideal.mul_mem_right _ _ (tateInvGlobalLegX_algebraMap_q_mem R I q hq)

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- The mirror of `AlgebraicGeometry.tateInvGlobalLegYX_overlapY_mul_legX_overlapX` on the
`y`-side chart, proved by the route of
`AlgebraicGeometry.tateInvGlobalLegXY_overlapY`. -/
theorem tateInvGlobalLegXY_overlapX_mul_legY_overlapY (hI : I.FG) :
    tateInvGlobalLegXY (R := R) (I := I) (q := q) hI (overlapX R I q) *
        tateInvGlobalLegY (R := R) (I := I) (q := q) (overlapY R I q) = 1 := by
  refine (annulusChartOverlapAlgY R I q).injective ((annulusOverlapEquivY R I q hI).injective ?_)
  rw [map_mul, map_mul, map_one, map_one, tateInvGlobalLegXY_apply,
    annulusChartOverlapAlgY_annulusChartTransitionInvAlg,
    annulusChartOverlapAlgX_tateInvGlobalLegX, annulusOverlapEquivY_annulusOverlapInversion,
    overlapEquiv_overlapX, rlsInv_X_one, annulusChartOverlapAlgY_tateInvGlobalLegY,
    annulusOverlapEquivY_algebraMap_overlapY, X_add]
  norm_num [X_zero]

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- The `y`-chart leg on the chosen coordinate, with the two coordinates in the order that
`AlgebraicGeometry.nodeChartCoord_crux` wants them. -/
theorem tateInvGlobalLegY_annulusNodeChartCoord :
    tateInvGlobalLegY (R := R) (I := I) (q := q) (annulusNodeChartCoord R I q) =
      tateInvGlobalLegY (R := R) (I := I) (q := q) (overlapY R I q) +
        tateInvGlobalLegY (R := R) (I := I) (q := q) (overlapX R I q) - 1 := by
  rw [annulusNodeChartCoord, map_sub, map_add, map_one, add_comm]

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- The inverse-transition-then-`x`-chart leg on the chosen coordinate. -/
theorem tateInvGlobalLegXY_annulusNodeChartCoord (hI : I.FG) :
    tateInvGlobalLegXY (R := R) (I := I) (q := q) hI (annulusNodeChartCoord R I q) =
      tateInvGlobalLegXY (R := R) (I := I) (q := q) hI (overlapY R I q) +
        tateInvGlobalLegXY (R := R) (I := I) (q := q) hI (overlapX R I q) - 1 := by
  rw [annulusNodeChartCoord, map_sub, map_add, map_one, add_comm]

include hq in
omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- The Tate parameter dies in the special fibre of the `y`-chart's coordinate ring. -/
theorem tateInvGlobalLegY_algebraMap_q_mem :
    tateInvGlobalLegY (R := R) (I := I) (q := q)
        (algebraMap R (annulusAlgebra R I q) q) ∈
      awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q) := by
  refine le_comap_awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q) ?_
  rw [← annulus_map_eq]
  exact Ideal.mem_map_of_mem _ hq

include hq in
omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- **The two backward legs cut out the same basic open of `Spf A{1/y}`** — the mirror of
`AlgebraicGeometry.basicOpen_tateInvGlobalLegYX_annulusNodeChartCoord`. -/
theorem basicOpen_tateInvGlobalLegXY_annulusNodeChartCoord (hI : I.FG) :
    basicOpen (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))
        (tateInvGlobalLegXY (R := R) (I := I) (q := q) hI (annulusNodeChartCoord R I q)) =
      basicOpen (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))
        (tateInvGlobalLegY (R := R) (I := I) (q := q) (annulusNodeChartCoord R I q)) := by
  obtain ⟨e₁, e₂⟩ := nodeChartCoord_crux
    (a := tateInvGlobalLegY (R := R) (I := I) (q := q) (overlapY R I q))
    (b := tateInvGlobalLegY (R := R) (I := I) (q := q) (overlapX R I q))
    (c := tateInvGlobalLegXY (R := R) (I := I) (q := q) hI (overlapY R I q))
    (d := tateInvGlobalLegXY (R := R) (I := I) (q := q) hI (overlapX R I q))
    (q' := tateInvGlobalLegY (R := R) (I := I) (q := q)
      (algebraMap R (annulusAlgebra R I q) q))
    (by rw [← map_mul, mul_comm, overlapX_mul_overlapY])
    (by rw [tateInvGlobalLegXY_overlapY, map_mul])
    (tateInvGlobalLegXY_overlapX_mul_legY_overlapY R I q hI)
  refine basicOpen_eq_of_mul_add_mem _
    (tateInvGlobalLegY (R := R) (I := I) (q := q) (overlapY R I q))
    (tateInvGlobalLegXY (R := R) (I := I) (q := q) hI (overlapX R I q)) ?_ ?_
  · rw [tateInvGlobalLegY_annulusNodeChartCoord, tateInvGlobalLegXY_annulusNodeChartCoord, e₁]
    exact Ideal.mul_mem_right _ _ (tateInvGlobalLegY_algebraMap_q_mem R I q hq)
  · rw [tateInvGlobalLegY_annulusNodeChartCoord, tateInvGlobalLegXY_annulusNodeChartCoord, e₂]
    exact Ideal.mul_mem_right _ _ (tateInvGlobalLegY_algebraMap_q_mem R I q hq)

end Crux

/-! ### The saturation of the chosen domain is itself -/

include hq in
omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The forward leg of the saturation sees exactly what the `x`-chart sees.** -/
theorem preimage_transitionHom_comp_chartY_tateInvNodeChartLocus (hI : I.FG) :
    ⇑((annulusChartTransitionInvSpf R I q hI).hom ≫ annulusOverlapChartY R I q).base ⁻¹'
        (tateInvNodeChartLocus R I q) =
      ⇑(annulusOverlapChart R I q).base ⁻¹' (tateInvNodeChartLocus R I q) := by
  haveI _hann : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI _hax : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  haveI _hay : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  have h1 := base_preimage_basicOpen (annulusIdealOfDefinition R I q)
    (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
    ((annulusChartTransitionInvSpf R I q hI).hom ≫ annulusOverlapChartY R I q)
    (annulusNodeChartCoord R I q)
  have h2 := base_preimage_basicOpen (annulusIdealOfDefinition R I q)
    (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
    (annulusOverlapChart R I q) (annulusNodeChartCoord R I q)
  rw [globalSectionsMap_transitionInv_comp_chartY] at h1
  rw [globalSectionsMap_annulusOverlapChart] at h2
  rw [tateInvNodeChartLocus]
  exact SetLike.coe_set_eq.mpr
    (h1.trans ((basicOpen_tateInvGlobalLegYX_annulusNodeChartCoord R I q hq hI).trans h2.symm))

include hq in
omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The backward leg of the saturation sees exactly what the `y`-chart sees.** -/
theorem preimage_transitionInv_comp_chart_tateInvNodeChartLocus (hI : I.FG) :
    ⇑((annulusChartTransitionInvSpf R I q hI).inv ≫ annulusOverlapChart R I q).base ⁻¹'
        (tateInvNodeChartLocus R I q) =
      ⇑(annulusOverlapChartY R I q).base ⁻¹' (tateInvNodeChartLocus R I q) := by
  haveI _hann : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI _hax : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  haveI _hay : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  have h1 := base_preimage_basicOpen (annulusIdealOfDefinition R I q)
    (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))
    ((annulusChartTransitionInvSpf R I q hI).inv ≫ annulusOverlapChart R I q)
    (annulusNodeChartCoord R I q)
  have h2 := base_preimage_basicOpen (annulusIdealOfDefinition R I q)
    (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))
    (annulusOverlapChartY R I q) (annulusNodeChartCoord R I q)
  rw [globalSectionsMap_transitionInv_inv_comp_chart] at h1
  rw [globalSectionsMap_annulusOverlapChartY] at h2
  rw [tateInvNodeChartLocus]
  exact SetLike.coe_set_eq.mpr
    (h1.trans ((basicOpen_tateInvGlobalLegXY_annulusNodeChartCoord R I q hq hI).trans h2.symm))

include hq in
omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The chosen domain is saturated.** -/
theorem tateInvChartSaturate_tateInvNodeChartLocus (hI : I.FG) :
    tateInvChartSaturate (R := R) (I := I) (q := q) hI (tateInvNodeChartLocus R I q) =
      tateInvNodeChartLocus R I q := by
  rw [tateInvChartSaturate, preimage_transitionHom_comp_chartY_tateInvNodeChartLocus R I q hq hI,
    preimage_transitionInv_comp_chart_tateInvNodeChartLocus R I q hq hI]
  refine Set.Subset.antisymm (Set.union_subset (Set.union_subset Set.Subset.rfl ?_) ?_)
    (Set.subset_union_left.trans Set.subset_union_left)
  · exact Set.image_preimage_subset _ _
  · exact Set.image_preimage_subset _ _

include hq in
omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The saturation is read on the chosen domain itself.** -/
theorem tateInvPatchSaturate_tateInvNodeChartLocus (hI : I.FG) :
    tateInvPatchSaturate hq hI (tateInvNodeChartLocus R I q) = tateInvNodeChartLocus R I q :=
  (tateInvPatchSaturate_eq_tateInvChartSaturate (hq := hq) (hI := hI) _).trans
    (tateInvChartSaturate_tateInvNodeChartLocus R I q hq hI)

include hq in
omit [TopologicalSpace R] [IsAdicRing I] in
/-- The `Opens` form. -/
theorem tateInvPatchSaturateOpens_tateInvNodeChartLocus (hI : I.FG) :
    tateInvPatchSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q) =
      ⟨tateInvNodeChartLocus R I q, isOpen_tateInvNodeChartLocus R I q⟩ :=
  Opens.ext (tateInvPatchSaturate_tateInvNodeChartLocus R I q hq hI)

include hq in
omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The saturated open of the chain is proper.** -/
theorem tateInvSaturate_tateInvNodeChartLocus_ne_univ (hI : I.FG) (hItop : I ≠ ⊤) :
    tateInvSaturate R I q hq hI (tateInvNodeChartLocus R I q) ≠ Set.univ := by
  intro hc
  refine tateInvNodeChartLocus_ne_univ R I q hq hItop ?_
  rw [← tateInvPatchSaturate_tateInvNodeChartLocus R I q hq hI, tateInvPatchSaturate, hc]
  exact Set.preimage_univ

section Quotient'

variable {Q : LocallyRingedSpace.{u}}
variable {π : (tateChainInv R I q hq hI).toLocallyRingedSpace ⟶ Q}

include hq in
/-- **The candidate node chart is a proper open of the quotient.** -/
theorem image_base_tateInvSaturate_tateInvNodeChartLocus_ne_univ (hItop : I ≠ ⊤)
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) :
    ⇑π.base '' tateInvSaturate R I q hq hI (tateInvNodeChartLocus R I q) ≠ Set.univ := by
  intro hc
  refine tateInvSaturate_tateInvNodeChartLocus_ne_univ R I q hq hI hItop ?_
  rw [← preimage_image_base_tateInvSaturate (hq := hq) (hI := hI) h
    (tateInvNodeChartLocus R I q), hc]
  exact Set.preimage_univ

end Quotient'

/-! ### The naive domain `D(x − 1)` fails, and this is why the coordinate is `x + y − 1` -/

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- Two elements congruent modulo the ideal of definition cut out the same basic open. -/
theorem basicOpen_eq_of_sub_mem {T : Type u} [CommRing T] (K : Ideal T) {a b : T}
    (h : a - b ∈ K) : basicOpen K a = basicOpen K b := by
  refine Opens.ext (Set.ext fun w => ?_)
  rw [SetLike.mem_coe, SetLike.mem_coe, mem_basicOpen, mem_basicOpen,
    show (Ideal.Quotient.mk K) a = (Ideal.Quotient.mk K) b from
      sub_eq_zero.mp (by rw [← map_sub]; exact Ideal.Quotient.eq_zero_iff_mem.mpr h)]

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- `D(−1)` is everything: `(−1)·(−1) = 1`, so `FormalSpectrum.basicOpen_mul` and
`FormalSpectrum.basicOpen_one` give it. -/
theorem basicOpen_neg_one {T : Type u} [CommRing T] (K : Ideal T) :
    basicOpen K (-1 : T) = ⊤ := by
  have h := basicOpen_mul K (-1 : T) (-1 : T)
  rw [neg_mul_neg, one_mul, basicOpen_one, inf_idem] at h
  exact h.symm

/-- **The naive candidate domain** `D(x − 1) ⊆ Spf A`: delete one point of the `x`-branch of the
special fibre and nothing on the `y`-branch. It contains the node locus for the same reason
`AlgebraicGeometry.tateInvNodeChartLocus` does, so it is a genuine competitor — and
`tateInvChartSaturate_tateInvNaiveChartLocus` is why it is not the right choice. -/
def tateInvNaiveChartLocus : Set (FormalSpectrum.locallyRingedSpaceObj
    (annulusIdealOfDefinition R I q)) :=
  (basicOpen (annulusIdealOfDefinition R I q) (overlapX R I q - 1) :
    Set (FormalSpectrum (annulusIdealOfDefinition R I q)))

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
theorem mem_tateInvNaiveChartLocus_iff {z : FormalSpectrum.locallyRingedSpaceObj
    (annulusIdealOfDefinition R I q)} :
    z ∈ tateInvNaiveChartLocus R I q ↔
      fibreX R I q - 1 ∉ (z : PrimeSpectrum (annulusFibre R I q)).asIdeal := by
  rw [tateInvNaiveChartLocus,
    show (fibreX R I q - 1) =
      Ideal.Quotient.mk (annulusIdealOfDefinition R I q) (overlapX R I q - 1) by
        simp [fibreX]]
  exact mem_basicOpen _ _ _

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- Wherever `x` lies in the prime, `x − 1` does not. -/
theorem mem_tateInvNaiveChartLocus_of_fibreX_mem {z : FormalSpectrum.locallyRingedSpaceObj
    (annulusIdealOfDefinition R I q)}
    (h : fibreX R I q ∈ (z : PrimeSpectrum (annulusFibre R I q)).asIdeal) :
    z ∈ tateInvNaiveChartLocus R I q := by
  refine (mem_tateInvNaiveChartLocus_iff R I q).mpr fun hc => ?_
  exact (z : PrimeSpectrum (annulusFibre R I q)).isPrime.ne_top
    ((Ideal.eq_top_iff_one _).mpr (by
      have := sub_mem h hc
      simpa using this))

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- The naive domain also contains the whole node locus. -/
theorem tateInvNodeLocus_subset_tateInvNaiveChartLocus (hI : I.FG) :
    tateInvNodeLocus R I q ⊆ tateInvNaiveChartLocus R I q := by
  intro z hz
  refine mem_tateInvNaiveChartLocus_of_fibreX_mem R I q ?_
  by_contra hc
  exact (mem_tateInvNodeLocus_iff.mp hz).1
    (by rw [range_annulusOverlapChart_base R I q hI]; exact (mem_basicOpen _ _ _).mpr hc)

include hq in
omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- **On `x − 1` the transition leg is a unit**: `legYX (x − 1) = q·legX x − 1 ≡ −1` modulo the
ideal of definition, so the open the neighbouring patch pulls back is all of `Spf A{1/x}`. -/
theorem basicOpen_tateInvGlobalLegYX_overlapX_sub_one (hI : I.FG) :
    basicOpen (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
        (tateInvGlobalLegYX (R := R) (I := I) (q := q) hI (overlapX R I q - 1)) = ⊤ := by
  refine Eq.trans (basicOpen_eq_of_sub_mem _ (b := -1) ?_) (basicOpen_neg_one _)
  rw [map_sub, map_one, tateInvGlobalLegYX_overlapX, map_mul, sub_neg_eq_add, sub_add_cancel]
  exact Ideal.mul_mem_right _ _ (tateInvGlobalLegX_algebraMap_q_mem R I q hq)

include hq in
omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The naive domain saturates to everything.** Its forward piece is the whole `x`-chart, and
`D(x − 1) ∪ D(x) = Spf A` because a prime containing both `x` and `x − 1` contains `1`. So
`π` of the saturation is the whole quotient, which cannot be an affine chart — the Néron 1-gon is
proper. **This is the reason the coordinate is `x + y − 1` and not `x − 1`.** -/
theorem tateInvChartSaturate_tateInvNaiveChartLocus (hI : I.FG) :
    tateInvChartSaturate (R := R) (I := I) (q := q) hI (tateInvNaiveChartLocus R I q) =
      Set.univ := by
  haveI _hann : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI _hax : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  haveI _hay : IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)
  have hpre : ⇑((annulusChartTransitionInvSpf R I q hI).hom ≫
      annulusOverlapChartY R I q).base ⁻¹' (tateInvNaiveChartLocus R I q) = Set.univ := by
    have h1 := base_preimage_basicOpen (annulusIdealOfDefinition R I q)
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
      ((annulusChartTransitionInvSpf R I q hI).hom ≫ annulusOverlapChartY R I q)
      (overlapX R I q - 1)
    rw [globalSectionsMap_transitionInv_comp_chartY,
      basicOpen_tateInvGlobalLegYX_overlapX_sub_one R I q hq hI] at h1
    exact (SetLike.coe_set_eq.mpr h1).trans Opens.coe_top
  refine Set.eq_univ_of_forall fun z => ?_
  by_cases h : fibreX R I q ∈ (z : PrimeSpectrum (annulusFibre R I q)).asIdeal
  · exact Or.inl (Or.inl (mem_tateInvNaiveChartLocus_of_fibreX_mem R I q h))
  · refine Or.inl (Or.inr ?_)
    have hz : z ∈ Set.range (annulusOverlapChart R I q).base := by
      rw [range_annulusOverlapChart_base R I q hI]
      exact (mem_basicOpen _ _ _).mpr h
    obtain ⟨w, rfl⟩ := hz
    exact ⟨w, by rw [hpre]; trivial, rfl⟩

section NaiveProper

variable (𝔭 : Ideal R) [𝔭.IsPrime] (h𝔭 : I ≤ 𝔭)

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- The point `x = 1, y = 0` is not in the naive domain either. -/
theorem annulusUnitPointX_notMem_tateInvNaiveChartLocus :
    annulusUnitPointX R I q hq 𝔭 h𝔭 ∉ tateInvNaiveChartLocus R I q := by
  rw [mem_tateInvNaiveChartLocus_iff, not_not]
  change _ ∈ Ideal.comap _ _
  rw [Ideal.mem_comap, Ideal.mem_bot, map_sub, map_one, annulusUnitEvalX,
    annulusFibreEval_fibreX]
  simp

end NaiveProper

include hq in
omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- **The naive domain is a proper open too**, so the contrast with
`AlgebraicGeometry.tateInvChartSaturate_tateInvNodeChartLocus` is not vacuous: `D(x − 1)` is a
proper open containing every node whose saturation is nevertheless everything. -/
theorem tateInvNaiveChartLocus_ne_univ (hItop : I ≠ ⊤) :
    tateInvNaiveChartLocus R I q ≠ Set.univ := by
  obtain ⟨𝔪, h𝔪, h𝔪le⟩ := Ideal.exists_le_maximal I hItop
  haveI : 𝔪.IsPrime := h𝔪.isPrime
  intro hc
  exact annulusUnitPointX_notMem_tateInvNaiveChartLocus R I q hq 𝔪 h𝔪le (by rw [hc]; trivial)

/-- **The node chart's candidate ring**: `AlgebraicGeometry.tateInvChartAnnulusSubring` at the
chosen domain. By `tateInvPatchSaturateOpens_tateInvNodeChartLocus` the ambient ring is
`Γ (Spf A, D(x + y − 1))` itself — the first *proper nonempty* `S` on this tree at which the chart
ring's ambient open is the `S` one started from (`AlgebraicGeometry.tateInvPatchSaturate_univ` and
`AlgebraicGeometry.tateInvPatchSaturate_empty` are the two trivial ones that were already there).
`AlgebraicGeometry.tateInvNodeChartAwaySubring` (`FormalSchemes.TateInvNodeChartAmbient`) is this
same ring displayed inside `A{1/(x + y − 1)}`. -/
def tateInvNodeChartSubring :
    Subring ((FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q)))) :=
  tateInvChartAnnulusSubring (hq := hq) (hI := hI) (isOpen_tateInvNodeChartLocus R I q)

/-- **`Γ` of the candidate node chart is that ring**, at an open of the quotient produced for it.
This is `AlgebraicGeometry.exists_tateInvChartAnnulusRingEquiv`
(`FormalSchemes.TateInvChartAnnulusRing`) at the chosen `S`; there is no new content in the proof
and the point is that the `S` is now a specific one. -/
theorem exists_tateInvNodeChartRingEquiv :
    ∃ (V : Opens (actionQuotient (tateInvPeriodAction R I q hq hI)).toTopCat)
      (_ : (Opens.map (actionQuotientπ
        (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V =
          tateInvSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q)),
      Nonempty (((actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj (op V)) ≃+*
        tateInvNodeChartSubring R I q hq hI) :=
  exists_tateInvChartAnnulusRingEquiv (isOpen_tateInvNodeChartLocus R I q)

end AlgebraicGeometry
