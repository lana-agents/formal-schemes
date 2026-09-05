import FormalSchemes.BasicOpenImmersionLRS
import FormalSchemes.OpenCover

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Locally finitely-generated formal schemes and the affine-chart neighborhood basis

`IsAdicRing I` does not force `I` to be finitely generated (`FormalSchemes/AdicRing.lean`), yet the
only supply of *small* affine open subschemes of `Spf I` is the basic-open chart
`FormalSpectrum.basicOpenChart I g`, which is an open immersion only when `I.FG`
(`isOpenImmersion_basicOpenChart`). We therefore isolate the class of formal schemes that are
locally the formal spectrum of a **finitely generated** adic ideal, and prove that for such a
scheme every point has affine charts contained in an arbitrarily small open neighborhood — the
"affine opens form a neighborhood basis" fact that source-side descent (EGA I §10.7, the general
fibre-product universal property) consumes.

## Main definitions and results

* `FormalScheme.LocallyFG`: every point has an affine open-immersion chart whose ideal of
  definition is finitely generated.
* `FormalScheme.locallyFG_Spf`: `Spf I` is `LocallyFG` when `I.FG`.
* `FormalScheme.AffineChart.basicOpenRefine` and `FormalScheme.exists_basicOpenRefine_subset`:
  **the shrinking step**, named and stated once — every affine chart has a basic-open refinement
  inside any given open neighbourhood of its point. It mentions no `FormalScheme.LocallyFG`
  hypothesis, no ideal of definition on a base and no homomorphism on sections, and every
  neighbourhood-basis lemma on this tree is that step plus what it transports:
  `FormalScheme.exists_affineChart_subset` below,
  `FormalScheme.exists_affineChart_subset_adicOverBase` (`FormalSchemes.AdicOverBaseChart`) and
  the two `ψ`-relative lemmas of `FormalSchemes.AdicSectionsChart`.
* `FormalScheme.exists_affineChart_subset`: on a `LocallyFG` scheme, every point `x` in an open
  `U` admits a finitely-generated affine chart whose range is contained in `U`.
* `FormalScheme.GlueData.gluedFormalScheme_locallyFG`: a scheme glued from `LocallyFG` pieces is
  `LocallyFG`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4.
-/

noncomputable section

open CategoryTheory TopologicalSpace Topology FormalSpectrum

universe u

namespace AlgebraicGeometry.FormalScheme

/-- A formal scheme is **locally finitely generated** if every point is in the range of an open
immersion from the formal spectrum of an adic ring whose ideal of definition is finitely
generated. This is the class on which basic-open charts are available, so affine opens form a
neighborhood basis. -/
def LocallyFG (X : FormalScheme.{u}) : Prop :=
  ∀ x : X, ∃ (R : Type u) (_ : CommRing R) (_ : TopologicalSpace R) (I : Ideal R)
    (_ : IsAdicRing I) (f : FormalSpectrum.locallyRingedSpaceObj I ⟶ X.toLocallyRingedSpace),
    I.FG ∧ x ∈ Set.range f.base ∧ LocallyRingedSpace.IsOpenImmersion f

/-- The affine formal scheme `Spf I` is locally finitely generated when `I` is finitely
generated: the identity chart works at every point. -/
theorem locallyFG_Spf {R : Type u} [CommRing R] [TopologicalSpace R] {I : Ideal R} [IsAdicRing I]
    (hI : I.FG) : (FormalScheme.Spf I).LocallyFG := by
  intro x
  refine ⟨R, inferInstance, inferInstance, I, inferInstance,
    𝟙 (FormalSpectrum.locallyRingedSpaceObj I), hI, ⟨x, rfl⟩,
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
      (𝟙 (FormalSpectrum.locallyRingedSpaceObj I)))⟩

section Refinement

variable {Y : FormalScheme.{u}}

/-- **The basic-open refinement of an affine chart, as an affine chart.** Composing a chart's open
immersion with `FormalSpectrum.basicOpenChart` at some `g` of its ring gives a smaller chart
around the same point: its ring is `FormalSpectrum.awayCompletion` and its ideal of definition is
`FormalSpectrum.awayCompletionIdeal`, both at that `g`.

This is the shrinking step every neighbourhood-basis lemma on this tree performs, named so that
each of them can say *which* chart it produces rather than only that one exists:
`AlgebraicGeometry.FormalScheme.exists_affineChart_subset` below,
`AlgebraicGeometry.FormalScheme.exists_affineChart_subset_adicOverBase`
(`FormalSchemes.AdicOverBaseChart`) and the two `ψ`-relative lemmas of
`FormalSchemes.AdicSectionsChart`. The two instance arguments are not automatic —
`FormalSpectrum.isOpenImmersion_basicOpenChart` needs the chart's ideal to be finitely
generated — so a caller supplies them, normally from
`AlgebraicGeometry.FormalScheme.exists_basicOpenRefine_subset` below. -/
def AffineChart.basicOpenRefine {y : Y} (c : AffineChart Y y) (g : c.R)
    [IsAdicRing (awayCompletionIdeal c.I g)]
    [LocallyRingedSpace.IsOpenImmersion (basicOpenChart c.I g ≫ c.map)]
    (hmem : y ∈ Set.range (basicOpenChart c.I g ≫ c.map).base) : AffineChart Y y where
  R := awayCompletion c.I g
  I := awayCompletionIdeal c.I g
  map := basicOpenChart c.I g ≫ c.map
  mem := hmem

/-- **Every chart can be shrunk into a given open**, with the refinement named. This is the whole
topological content of the neighbourhood-basis lemmas of this tree, separated from what each of
them transports along it: the basic opens of the chart's own formal spectrum are a basis
(`FormalSpectrum.isTopologicalBasis_basicOpen`), so one of them lands inside the preimage of the
target open, and `FormalSpectrum.range_basicOpenChart_base` identifies its image.

Nothing here mentions a locally-finitely-generated hypothesis, an ideal of definition on a base or
a homomorphism on sections. That is the point: the lemmas that use it differ only in what they
carry across this step, and each carries it across the *same* `FormalSpectrum.basicOpenChart`. -/
theorem exists_basicOpenRefine_subset {y : Y} (c : AffineChart Y y) (hfg : c.I.FG)
    (U : Set Y) (hU : IsOpen U) (hyU : y ∈ U) :
    ∃ (g : c.R) (_ : IsAdicRing (awayCompletionIdeal c.I g))
      (_ : LocallyRingedSpace.IsOpenImmersion (basicOpenChart c.I g ≫ c.map))
      (hmem : y ∈ Set.range (basicOpenChart c.I g ≫ c.map).base),
      Set.range (c.basicOpenRefine g hmem).map.base ⊆ U := by
  obtain ⟨y₀, hy₀⟩ := c.mem
  have hopen : IsOpen (c.map.base ⁻¹' U) := hU.preimage c.map.base.hom.continuous
  have hmem₀ : y₀ ∈ c.map.base ⁻¹' U := by
    simp only [Set.mem_preimage, hy₀]; exact hyU
  obtain ⟨v, ⟨g, rfl⟩, hy₀v, hvsub⟩ :=
    (isTopologicalBasis_basicOpen c.I).exists_subset_of_mem_open hmem₀ hopen
  haveI : IsAdicRing (awayCompletionIdeal c.I g) := isAdicRing_awayCompletionIdeal c.I g hfg
  haveI : LocallyRingedSpace.IsOpenImmersion (basicOpenChart c.I g) :=
    isOpenImmersion_basicOpenChart c.I g hfg
  haveI : LocallyRingedSpace.IsOpenImmersion (basicOpenChart c.I g ≫ c.map) :=
    LocallyRingedSpace.IsOpenImmersion.comp _ _
  have hrange : Set.range (basicOpenChart c.I g).base =
      (basicOpen c.I g : Set (FormalSpectrum c.I)) := range_basicOpenChart_base c.I g hfg
  obtain ⟨w₀, hw₀⟩ : y₀ ∈ Set.range (basicOpenChart c.I g).base := by
    rw [hrange]; exact hy₀v
  have hmem : y ∈ Set.range (basicOpenChart c.I g ≫ c.map).base := by
    refine ⟨w₀, ?_⟩
    simp only [LocallyRingedSpace.comp_base, TopCat.comp_app]
    rw [hw₀]; exact hy₀
  refine ⟨g, ‹_›, ‹_›, hmem, ?_⟩
  change Set.range (basicOpenChart c.I g ≫ c.map).base ⊆ U
  rw [LocallyRingedSpace.comp_base]
  intro z hz
  simp only [TopCat.comp_app, Set.mem_range] at hz
  obtain ⟨w, rfl⟩ := hz
  have hw : (basicOpenChart c.I g).base w ∈ (basicOpen c.I g : Set (FormalSpectrum c.I)) := by
    rw [← hrange]; exact ⟨w, rfl⟩
  exact hvsub hw

end Refinement

/-- **Affine charts form a neighborhood basis.** On a locally finitely-generated formal scheme,
every point `x` lying in an open set `U` has a finitely-generated affine open-immersion chart whose
range is contained in `U`.

The chart is the basic-open refinement of the witness `hX` supplies at `x`: bundle that witness as
an `AlgebraicGeometry.FormalScheme.AffineChart` and apply
`AlgebraicGeometry.FormalScheme.exists_basicOpenRefine_subset`. The unbundled existential here is
what callers already consume, which is why it is kept in this shape rather than replaced. -/
theorem exists_affineChart_subset (X : FormalScheme.{u}) (hX : X.LocallyFG) (x : X)
    (U : Set X) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ (R : Type u) (_ : CommRing R) (_ : TopologicalSpace R) (J : Ideal R) (_ : IsAdicRing J)
      (f : FormalSpectrum.locallyRingedSpaceObj J ⟶ X.toLocallyRingedSpace),
      J.FG ∧ x ∈ Set.range f.base ∧ Set.range f.base ⊆ U ∧
        LocallyRingedSpace.IsOpenImmersion f := by
  obtain ⟨R, _, _, I, _, m, hIfg, hmem, hm⟩ := hX x
  -- bundle the witness as an affine chart, then shrink it into `U`
  let c : AffineChart X x := { R := R, I := I, map := m, mem := hmem, isOpenImmersion := hm }
  obtain ⟨g, hadic, hoi, hmem', hsub⟩ := exists_basicOpenRefine_subset c hIfg U hU hxU
  exact ⟨awayCompletion c.I g, inferInstance, inferInstance, awayCompletionIdeal c.I g, hadic,
    (c.basicOpenRefine g hmem').map, awayCompletionIdeal_fg c.I g hIfg,
    (c.basicOpenRefine g hmem').mem, hsub, hoi⟩

set_option backward.isDefEq.respectTransparency false in
/-- A formal scheme glued from locally finitely-generated pieces is itself locally finitely
generated. In particular the glued factors `xGlued`/`yGlued` of a `BothChartedFibreDatumXY` are
`LocallyFG`, since each chart `Spf(I·A_i)` has the finitely generated ideal `I·A_i`. -/
theorem GlueData.gluedFormalScheme_locallyFG (D : GlueData.{u})
    (h : ∀ i : D.toLocallyRingedSpaceGlueData.J, ∃ Y : FormalScheme.{u},
      Y.LocallyFG ∧ Nonempty (Y.toLocallyRingedSpace ≅ D.toLocallyRingedSpaceGlueData.U i)) :
    D.gluedFormalScheme.LocallyFG := by
  intro x
  obtain ⟨i, y, rfl⟩ := D.toLocallyRingedSpaceGlueData.ι_jointly_surjective x
  obtain ⟨Y, hY, ⟨e⟩⟩ := h i
  obtain ⟨R, hR, hTR, I, hI, f, hIfg, ⟨z, hz⟩, hf⟩ := hY (e.inv.base y)
  haveI := hf
  refine ⟨R, hR, hTR, I, hI,
    f ≫ e.hom ≫ D.toLocallyRingedSpaceGlueData.toGlueData.ι i, hIfg, ⟨z, ?_⟩,
    inferInstance⟩
  simp only [LocallyRingedSpace.comp_toHom, PresheafedSpace.comp_base, TopCat.hom_comp,
    ContinuousMap.coe_comp, Function.comp_apply]
  rw [hz]
  have hy : e.hom.base (e.inv.base y) = y := by simp
  rw [hy]
  rfl

end AlgebraicGeometry.FormalScheme

end
