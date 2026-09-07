import FormalSchemes.AdicOnOpenSections
import FormalSchemes.TateInvNodeChartDomain

set_option linter.style.header false

/-!
# The node chart's ambient ring is `A{1/(x + y − 1)}`

`FormalSchemes.TateInvNodeChartDomain` chose the node chart's domain on the model patch,
`S = D(x + y − 1) ⊆ Spf A` for `A = R{x, y}/(x·y − q)`, and proved it is its own saturation, so
that the chart ring's ambient open is `S` itself
(`AlgebraicGeometry.tateInvPatchSaturateOpens_tateInvNodeChartLocus`). The candidate chart ring
`AlgebraicGeometry.tateInvNodeChartSubring` is therefore a `Subring` of the sections of
`O_{Spf A}` over a **basic** open — and sections over a basic open are a ring this tree already
knows well.

This file makes that identification and draws the two consequences that are free once it is made.

## What is here

* **`AlgebraicGeometry.tateInvNodeChartAmbientEquiv`**: the ambient ring is
  `FormalSpectrum.awayCompletion (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)`,
  the completed localization `A{1/(x + y − 1)}`. It is
  `FormalSpectrum.sectionsEquivOfEqBasicOpen` — itself
  `FormalSpectrum.sectionsBasicOpenEquiv` conjugated by a transport — at
  `AlgebraicGeometry.tateInvNodeChartOpens_eq_basicOpen`. That equivalence and the three general
  lemmas around it used to be declared here, in a `namespace FormalSpectrum` block mentioning no
  Tate object; issue 1473 moved them to `FormalSchemes.AdicOnOpenSections`, beside
  `FormalSpectrum.sectionsOpenHom`, which is what they are about. The `import` of that module
  stays, and this line is what justifies it.
* **`AlgebraicGeometry.tateInvNodeChartAwaySubring`**: the candidate chart ring, carried across
  that equivalence, as a `Subring` of `A{1/(x + y − 1)}` — with
  `AlgebraicGeometry.tateInvNodeChartSubringEquivAway` and
  `AlgebraicGeometry.exists_tateInvNodeChartAwayRingEquiv`, which is
  `AlgebraicGeometry.exists_tateInvNodeChartRingEquiv` restated at the explicit ring.
* **`AlgebraicGeometry.isAdicRing_tateInvNodeChartAmbient`**: the ambient ring is a complete adic
  ring, with `FormalSpectrum.awayCompletionIdeal` as ideal of definition. This is
  `FormalSpectrum.isAdicRing_awayCompletionIdeal` at the chosen coordinate, and it is the reason
  the identification is worth making: it is an adic structure on the ring the chart's ring sits
  inside, which the presheaf-section spelling does not display.
* **`AlgebraicGeometry.tateInvNodeChartAwayIdeal`**: the candidate ideal of definition on the
  chart ring — the contraction of `awayCompletionIdeal` along the inclusion, i.e. the subspace
  topology — together with
  **`AlgebraicGeometry.isHausdorff_tateInvNodeChartAwayIdeal`**: it is Hausdorff. The general
  lemma behind it, `AlgebraicGeometry.isHausdorff_comap_subtype`, is stated for an arbitrary
  subring of an arbitrary Hausdorff adic ring.
* **`AlgebraicGeometry.tateInvNodeChartAwaySpfMap`**: `Spf` of the inclusion, the map of formal
  spectra `Spf A{1/(x + y − 1)} → Spf` of the chart ring, with
  `AlgebraicGeometry.continuous_tateInvNodeChartAwaySpfMap` and — the reason it is worth naming —
  **`AlgebraicGeometry.tateInvNodeChartAwaySpfMap_eq_iff`**: two primes have the same image under
  it exactly when they have the same trace on the chart ring. That pointwise condition is what the
  node-chart cluster's residue is stated in, and this says it is a fibre of one map.
* **`AlgebraicGeometry.injective_quotientMap_tateInvNodeChartAwaySubring`**: the chart ring
  **embeds** in the ambient ring modulo the ideal of definition. Both of these are `le_rfl` at
  the side condition, because the ideal above is by definition the contraction of the one below,
  so neither asks for anything beyond the data that names the two rings — no completeness of
  either, no finite generation of `FormalSpectrum.awayCompletionIdeal`, and nothing adic about
  `AlgebraicGeometry.tateInvNodeChartAwayIdeal`. (Both do carry `hq`, `hI` and this file's
  ambient instances, which is what `AlgebraicGeometry.tateInvNodeChartAwaySubring` itself needs
  to be written down.)
* **`AlgebraicGeometry.tateInvNodeChartAmbientHom`** and
  **`AlgebraicGeometry.range_tateInvNodeChartAmbientHom`**: the morphism
  `Spf A{1/(x + y − 1)} ⟶ Q` obtained by composing the basic-open chart with the patch inclusion
  `ι ⟨0⟩` and the quotient projection, and the computation that its range is **exactly** the
  candidate chart domain `π '' tateInvSaturate D(x + y − 1)`.

## What is *not* proved

**`hnode` is still undecided and nothing here is a chart.**

* **`tateInvNodeChartAwayIdeal` is not shown to be an ideal of *definition*.** Hausdorffness is
  proved; **completeness is not**, and neither is finite generation, and neither is the statement
  that the subring is closed in `A{1/(x + y − 1)}`. Those three are the residue of item (i) of
  this cluster's standing residue, and the reason they are not free is that a subring of a
  complete ring is complete only when it is closed.
* **`tateInvNodeChartAmbientHom` is not *shown* to be an open immersion, and must not be read as
  one.** Its range is the right set and nothing more: nothing here says the morphism factors
  through `Spf` of the subring, and no such factorisation is constructed. It is moreover
  **expected to fail injectivity**, which is why the chart must be built from the invariant
  subring rather than from this morphism — `π` should identify a point of `D(x)` in the model
  patch with its partner in `D(y)` under the `𝔾m`-inversion transition, both of which lie in
  `D(x + y − 1)` because
  `AlgebraicGeometry.preimage_transitionHom_comp_chartY_tateInvNodeChartLocus` and
  `AlgebraicGeometry.preimage_transitionInv_comp_chart_tateInvNodeChartLocus`
  (`FormalSchemes.TateInvNodeChartDomain`) say the transition matches the part of the domain the
  `x`-chart sees with the part the `y`-chart sees; that failure would be the Néron 1-gon's two
  glued points. **None of that is proved here.** It is proved downstream, and by a different
  route: `AlgebraicGeometry.not_isOpenImmersion_tateInvNodeChartAmbientHom_of_ne_top`
  (`FormalSchemes.TateInvNodeChartAmbientNotInjective`) exhibits two distinct points of
  `D(x + y − 1)` with one image in the quotient — the generic points of the two branches through a
  node, taken from `FormalSchemes.TateInvPeriodNodePoint` rather than from the two preimage lemmas
  above — so this morphism is not injective, hence not an open immersion, whenever `I ≠ ⊤`. That
  refutes the candidate for the open immersion
  `AlgebraicGeometry.exists_formalScheme_of_openImmersion_spf_quotientIdeal_of_isLeftRegular_base`
  asks for whose range is *equal* to the required set; it says nothing about `hnode`, which asks
  only for *some* open immersion with a range containing it.
* **Nothing here says the subring is nonzero, proper, or larger than the image of `R`.** This
  file adds no element of it. The image of the base ring is in it, at every open `S`
  (`AlgebraicGeometry.sectionsOpenHom_algebraMap_mem_tateInvChartAnnulusSubring`,
  `FormalSchemes.TateInvChartBaseImage`) and in this file's own spelling
  (`AlgebraicGeometry.algebraMap_mem_tateInvNodeChartAwaySubring`, same module) — but that is a
  lower bound and says nothing about the three questions above.
* **`tateInvNodeChartAwaySpfMap` is not shown injective here, and it is not injective.**
  `AlgebraicGeometry.not_injective_tateInvNodeChartAwaySpfMap`
  (`FormalSchemes.TateInvNodeChartOrbitSeparation`) refutes its injectivity for `I ≠ ⊤`, inside
  the regime that file's clause section fixes — finite generation of
  `AlgebraicGeometry.tateInvNodeChartQuotientIdeal` and an
  `AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG` witness — and contraposing that through
  `PrimeSpectrum.comap_injective_of_surjective` gives there both
  `AlgebraicGeometry.not_surjective_quotientMap_tateInvNodeChartAwaySubring` and
  `AlgebraicGeometry.tateInvNodeChartAwaySubring_ne_top`. **So properness, which the bullet above
  leaves open, is decided downstream in that regime — and only there.** Outside it, `I = ⊤`
  included, nothing decides it; and no element of `A{1/(x + y − 1)}` is shown to lie outside the
  chart ring anywhere on the tree, the refutation being a contraposition that produces no witness.
  (`AlgebraicGeometry.notMem_tateInvGlobalSubring_overlapX`,
  `FormalSchemes.TateInvGlobalProperness`, exhibits one for the **global** subring inside `A`,
  which is a different subring of a different ring.)

Nothing here weakens `LocallyRingedSpace.IsProperlyDiscontinuousOn`,
`LocallyRingedSpace.IsFreeProperlyDiscontinuous` or
`LocallyRingedSpace.freeActionQuotientFormalScheme`.

## Placement

Over `FormalSchemes.AdicOnOpenSections` and `FormalSchemes.TateInvNodeChartDomain`: forward
closure **202** project modules besides itself, reverse closure **34**, counted by walking every
`^import FormalSchemes.` line over the files under `FormalSchemes/` (a module is not counted in
its own closure; the aggregator at the repository root is outside the walk).

`Spf` of the inclusion is here rather than beside the statements that use it because it needs
this file and nothing else: the two rings, the contraction and `FormalSpectrum.map` are all in
scope by the line above. `FormalSchemes.TateInvNodeChartOrbitSeparation`, where the criterion it
feeds is stated, has forward closure **269**, so a reader who wants only the map imports this file
and pays sixty-seven modules less for it.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1.4 — sections of
  `O_{Spf A}` on a basic open are the completed localization.
* [Deligne–Rapoport, *Les schémas de modules de courbes elliptiques*], II.1 — the Néron `n`-gon.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum TopologicalSpace
open Opposite TopCat.Presheaf

universe u

namespace AlgebraicGeometry

/-- **A subring of a Hausdorff adic ring is Hausdorff for the contracted ideal.** The contraction
`K.comap S.subtype` is the subspace topology's ideal, and `(K.comap S.subtype) ^ n` maps into
`K ^ n`, so an element of every power of the contraction has image in every power of `K`. No
completeness is involved and none is obtained: a subring of a complete ring is complete only when
it is closed. -/
theorem isHausdorff_comap_subtype {A : Type u} [CommRing A] (K : Ideal A) (S : Subring A)
    (hK : IsHausdorff K A) : IsHausdorff (K.comap S.subtype) S where
  haus' x hx := by
    have hval : ∀ n : ℕ, (x : A) ∈ K ^ n := by
      intro n
      have h1 : x ∈ (K.comap S.subtype) ^ n := by
        have h := hx n
        rwa [SModEq.zero, Ideal.mem_smul_top_self_iff] at h
      have hle : ((K.comap S.subtype) ^ n).map S.subtype ≤ K ^ n := by
        rw [Ideal.map_pow]
        exact pow_le_pow_left' Ideal.map_comap_le n
      exact hle (Ideal.mem_map_of_mem _ h1)
    exact Subtype.ext (hK.haus (x : A) fun n => by
      rw [SModEq.zero, Ideal.mem_smul_top_self_iff]; exact hval n)

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The node chart's ambient open is a basic open of the model patch.** The saturation theorem
`AlgebraicGeometry.tateInvPatchSaturateOpens_tateInvNodeChartLocus` says the ambient open is
`tateInvNodeChartLocus`, and that set is by definition the basic open of
`AlgebraicGeometry.annulusNodeChartCoord`. -/
theorem tateInvNodeChartOpens_eq_basicOpen :
    tateInvPatchSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q) =
      basicOpen (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) :=
  (tateInvPatchSaturateOpens_tateInvNodeChartLocus R I q hq hI).trans (Opens.ext rfl)

/-- **The node chart's ambient ring is `A{1/(x + y − 1)}`.** The `Subring` that
`AlgebraicGeometry.tateInvNodeChartSubring` cuts out lives in the sections of `O_{Spf A}` over the
chosen domain; by `tateInvNodeChartOpens_eq_basicOpen` that domain is a basic open, so those
sections are the completed localization (EGA I, 10.1.4). -/
def tateInvNodeChartAmbientEquiv :
    ((FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
        (op (tateInvPatchSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q))) : Type u) ≃+*
      awayCompletion (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) :=
  haveI _hann : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  FormalSpectrum.sectionsEquivOfEqBasicOpen _ (tateInvNodeChartOpens_eq_basicOpen R I q hq hI)

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- **The ambient ring is a complete adic ring**, with `FormalSpectrum.awayCompletionIdeal` as
ideal of definition. This is what the identification buys: an adic structure on the ring the
chart's ring sits inside, which the presheaf-section spelling does not display. -/
theorem isAdicRing_tateInvNodeChartAmbient (hI : I.FG) :
    IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q)) :=
  FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)

/-- **The candidate chart ring as a subring of `A{1/(x + y − 1)}`.** The image of
`AlgebraicGeometry.tateInvNodeChartSubring` under `tateInvNodeChartAmbientEquiv`. -/
def tateInvNodeChartAwaySubring : Subring
    (awayCompletion (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)) :=
  Subring.map (tateInvNodeChartAmbientEquiv R I q hq hI).toRingHom
    (tateInvNodeChartSubring R I q hq hI)

/-- The two spellings of the candidate chart ring agree. -/
def tateInvNodeChartSubringEquivAway :
    tateInvNodeChartSubring R I q hq hI ≃+* tateInvNodeChartAwaySubring R I q hq hI :=
  RingEquiv.subringMap _

/-- **`Γ` of the candidate node chart is a subring of `A{1/(x + y − 1)}`.** This is
`AlgebraicGeometry.exists_tateInvNodeChartRingEquiv` restated at the explicit ring; the `V` and
its defining property are unchanged. -/
theorem exists_tateInvNodeChartAwayRingEquiv :
    ∃ (V : Opens (actionQuotient (tateInvPeriodAction R I q hq hI)).toTopCat)
      (_ : (Opens.map (actionQuotientπ
        (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V =
          tateInvSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q)),
      Nonempty (((actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj (op V)) ≃+*
        tateInvNodeChartAwaySubring R I q hq hI) := by
  obtain ⟨V, hV, ⟨e⟩⟩ := exists_tateInvNodeChartRingEquiv R I q hq hI
  exact ⟨V, hV, ⟨e.trans (tateInvNodeChartSubringEquivAway R I q hq hI)⟩⟩

/-- **The candidate ideal of definition on the chart ring**: the contraction of the ambient ring's
ideal of definition along the inclusion — that is, the subspace topology.

`isHausdorff_tateInvNodeChartAwayIdeal` is what is proved about it. **It is not shown to be an
ideal of definition**: neither completeness nor finite generation is proved here. -/
def tateInvNodeChartAwayIdeal : Ideal (tateInvNodeChartAwaySubring R I q hq hI) :=
  (awayCompletionIdeal (annulusIdealOfDefinition R I q)
    (annulusNodeChartCoord R I q)).comap (tateInvNodeChartAwaySubring R I q hq hI).subtype

/-- **The candidate ideal of definition is Hausdorff.** `isHausdorff_comap_subtype` at the
ambient ring, which is Hausdorff by `FormalSpectrum.isHausdorff_awayCompletionIdeal`.

This is the separation half of "ideal of definition" and **not** the completeness half; see this
file's module docstring. -/
theorem isHausdorff_tateInvNodeChartAwayIdeal :
    IsHausdorff (tateInvNodeChartAwayIdeal R I q hq hI)
      (tateInvNodeChartAwaySubring R I q hq hI) :=
  isHausdorff_comap_subtype _ _
    (FormalSpectrum.isHausdorff_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI))

/-! ### `Spf` of the inclusion -/

/-- **`Spf` of the inclusion of the chart ring**: the map of formal spectra
`Spf A{1/(x + y − 1)} → Spf (tateInvNodeChartAwaySubring …)` induced by
`(AlgebraicGeometry.tateInvNodeChartAwaySubring R I q hq hI).subtype`.

**The side condition is `le_rfl`**, and that it is is the reason this definition asks for nothing
beyond the data naming the two rings: `AlgebraicGeometry.tateInvNodeChartAwayIdeal` is *defined* as
the contraction of `FormalSpectrum.awayCompletionIdeal` along the inclusion, so the containment
`FormalSpectrum.map` asks for is the containment of an ideal in itself. `FormalSpectrum.map`
moreover carries `omit [TopologicalSpace R] [IsAdicRing I]`, so nothing but the two `CommRing`
structures enters *it*. What remains in the signature here — `hq`, `hI` and this file's ambient
instances — is what `AlgebraicGeometry.tateInvNodeChartAwaySubring` needs in order to be named at
all, and none of it is consumed by the construction.

**This is not a claim that `AlgebraicGeometry.tateInvNodeChartAwayIdeal` is an ideal of
definition.** Neither completeness of the away completion nor finite generation of
`FormalSpectrum.awayCompletionIdeal` is used or obtained; the target is the formal spectrum of a
pair (ring, ideal) and that is all `FormalSpectrum` is. See this file's module docstring. -/
def tateInvNodeChartAwaySpfMap :
    FormalSpectrum (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q)) →
    FormalSpectrum (tateInvNodeChartAwayIdeal R I q hq hI) :=
  FormalSpectrum.map (tateInvNodeChartAwayIdeal R I q hq hI)
    (awayCompletionIdeal (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q))
    (tateInvNodeChartAwaySubring R I q hq hI).subtype le_rfl

/-- **It is continuous**, so *map of formal spectra* is the right noun for it and not just
*function*: `FormalSpectrum.continuous_map` at the same side condition. Nothing below uses this;
it is here so that the noun the docstrings use is one the file has earned. -/
theorem continuous_tateInvNodeChartAwaySpfMap :
    Continuous (tateInvNodeChartAwaySpfMap R I q hq hI) :=
  FormalSpectrum.continuous_map _ _ _ _

/-- **Two primes have the same image under `Spf` of the inclusion exactly when they have the same
trace on the chart ring.** The right-hand side is the pointwise condition the node-chart cluster
carries — a prime of `A{1/(x + y − 1)}` modulo `FormalSpectrum.awayCompletionIdeal` contains the
class of an element of the chart ring iff the other one does — and this says it is a fibre of one
map, with no scheme, no action and no chart in it.

The proof is written around a hazard worth naming: `FormalSpectrum I` is a `def` for
`PrimeSpectrum (R ⧸ I)` and **not** an `abbrev`, so `PrimeSpectrum.ext` and `PrimeSpectrum.asIdeal`
reach a point of `FormalSpectrum _` only through that unfolding. The forward direction therefore
transports the equality with `congrArg` at the `PrimeSpectrum` spelling rather than rewriting, and
the backward direction produces the element with `Ideal.Quotient.mk_surjective` before comparing
membership. -/
theorem tateInvNodeChartAwaySpfMap_eq_iff
    (w w' : FormalSpectrum (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q))) :
    tateInvNodeChartAwaySpfMap R I q hq hI w = tateInvNodeChartAwaySpfMap R I q hq hI w' ↔
      ∀ a : tateInvNodeChartAwaySubring R I q hq hI,
        (Ideal.Quotient.mk (awayCompletionIdeal (annulusIdealOfDefinition R I q)
            (annulusNodeChartCoord R I q))
            (a : awayCompletion (annulusIdealOfDefinition R I q)
              (annulusNodeChartCoord R I q)) ∈ w.asIdeal ↔
          Ideal.Quotient.mk (awayCompletionIdeal (annulusIdealOfDefinition R I q)
            (annulusNodeChartCoord R I q))
            (a : awayCompletion (annulusIdealOfDefinition R I q)
              (annulusNodeChartCoord R I q)) ∈ w'.asIdeal) := by
  constructor
  · intro h a
    have := congrArg PrimeSpectrum.asIdeal h
    have h2 : ∀ b, b ∈ (PrimeSpectrum.comap (Ideal.quotientMap _
        (tateInvNodeChartAwaySubring R I q hq hI).subtype
        (le_rfl : tateInvNodeChartAwayIdeal R I q hq hI ≤ _)) w).asIdeal ↔
        b ∈ (PrimeSpectrum.comap (Ideal.quotientMap _
        (tateInvNodeChartAwaySubring R I q hq hI).subtype
        (le_rfl : tateInvNodeChartAwayIdeal R I q hq hI ≤ _)) w').asIdeal := fun b =>
      Iff.of_eq (congrArg (b ∈ ·) this)
    have := h2 (Ideal.Quotient.mk (tateInvNodeChartAwayIdeal R I q hq hI) a)
    simpa [Ideal.quotientMap_mk] using this
  · intro h
    apply PrimeSpectrum.ext
    apply Ideal.ext
    intro b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    simpa [tateInvNodeChartAwaySpfMap, FormalSpectrum.map, Ideal.quotientMap_mk] using h a

/-- **The chart ring embeds in the ambient ring modulo the ideal of definition.**
`Ideal.quotientMap_injective'` at `le_rfl`, which applies for the same reason the map above needs
no hypothesis: the ideal upstairs is the contraction of the one downstairs, so a chart-ring element
lying in `FormalSpectrum.awayCompletionIdeal` already lies in
`AlgebraicGeometry.tateInvNodeChartAwayIdeal`.

Nothing here says the embedding is onto, and it is not: see
`AlgebraicGeometry.not_surjective_quotientMap_tateInvNodeChartAwaySubring`
(`FormalSchemes.TateInvNodeChartOrbitSeparation`), which refutes surjectivity for `I ≠ ⊤` in the
regime that file's section fixes. -/
theorem injective_quotientMap_tateInvNodeChartAwaySubring :
    Function.Injective (Ideal.quotientMap
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q))
      (tateInvNodeChartAwaySubring R I q hq hI).subtype
      (le_rfl : tateInvNodeChartAwayIdeal R I q hq hI ≤ _)) :=
  Ideal.quotientMap_injective' le_rfl

section Quotient

variable {Q : LocallyRingedSpace.{u}}
variable {π : (tateChainInv R I q hq hI).toLocallyRingedSpace ⟶ Q}

/-- **The morphism `Spf A{1/(x + y − 1)} ⟶ Q`**: the basic-open chart of the chosen domain,
followed by the patch inclusion `ι ⟨0⟩` and the quotient projection.

**This is not shown to be an open immersion and must not be read as one** — its range is
computed and nothing else is; see `range_tateInvNodeChartAmbientHom` and this file's module
docstring. -/
def tateInvNodeChartAmbientHom :
    (FormalSpectrum.locallyRingedSpaceObj (awayCompletionIdeal
      (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q))) ⟶ Q :=
  haveI _hann : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  FormalSpectrum.basicOpenChart _ _ ≫
    (tateChainInvFormalGlueData R I q hq hI).ι ⟨0⟩ ≫ π

/-- **Its range is exactly the candidate chart domain.** The basic-open chart's range is
`D(x + y − 1)` (`FormalSpectrum.range_basicOpenChart_base`), and the image of a saturation is the
image of a single patch's copy of the set
(`AlgebraicGeometry.image_base_tateInvSaturate_eq_image_base_ι`).

So the set a node chart has to cover is the range of one morphism out of an affine formal scheme.
It is **not** the claim that that morphism is a chart. -/
theorem range_tateInvNodeChartAmbientHom
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) :
    Set.range (tateInvNodeChartAmbientHom R I q hq hI (π := π)).base =
      ⇑π.base '' tateInvSaturate R I q hq hI (tateInvNodeChartLocus R I q) := by
  haveI _hann : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  rw [image_base_tateInvSaturate_eq_image_base_ι R I q hq hI h _ ⟨0⟩]
  have hcomp : ⇑(tateInvNodeChartAmbientHom R I q hq hI (π := π)).base =
      ⇑π.base ∘ ⇑((tateChainInvFormalGlueData R I q hq hI).ι ⟨0⟩).base ∘
        ⇑(FormalSpectrum.basicOpenChart (annulusIdealOfDefinition R I q)
          (annulusNodeChartCoord R I q)).base := rfl
  rw [hcomp, Set.range_comp, Set.range_comp]
  refine congrArg (Set.image _) (congrArg (Set.image _) ?_)
  exact range_basicOpenChart_base _ _ (annulusIdealOfDefinition_fg R I q hI)

end Quotient

end AlgebraicGeometry
