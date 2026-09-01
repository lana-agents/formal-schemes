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

/-- **Affine charts form a neighborhood basis.** On a locally finitely-generated formal scheme,
every point `x` lying in an open set `U` has a finitely-generated affine open-immersion chart whose
range is contained in `U`. -/
theorem exists_affineChart_subset (X : FormalScheme.{u}) (hX : X.LocallyFG) (x : X)
    (U : Set X) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ (R : Type u) (_ : CommRing R) (_ : TopologicalSpace R) (J : Ideal R) (_ : IsAdicRing J)
      (f : FormalSpectrum.locallyRingedSpaceObj J ⟶ X.toLocallyRingedSpace),
      J.FG ∧ x ∈ Set.range f.base ∧ Set.range f.base ⊆ U ∧
        LocallyRingedSpace.IsOpenImmersion f := by
  obtain ⟨R, _, _, I, _, m, hIfg, ⟨x₀, hx₀⟩, hm⟩ := hX x
  -- the preimage of `U` under the chart base map is an open set containing `x₀`
  have hcont : Continuous m.base := m.base.hom.continuous
  have hopen : IsOpen (m.base ⁻¹' U) := hU.preimage hcont
  have hmem : x₀ ∈ m.base ⁻¹' U := by
    simp only [Set.mem_preimage, hx₀]; exact hxU
  obtain ⟨v, ⟨g, rfl⟩, hx₀v, hvsub⟩ :=
    (isTopologicalBasis_basicOpen I).exists_subset_of_mem_open hmem hopen
  -- the away completion `R{1/g}` is a finitely-generated adic ring
  haveI hJadic : IsAdicRing (FormalSpectrum.awayCompletionIdeal I g) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal I g hIfg
  haveI hoi : LocallyRingedSpace.IsOpenImmersion (FormalSpectrum.basicOpenChart I g) :=
    FormalSpectrum.isOpenImmersion_basicOpenChart I g hIfg
  have hJfg : (FormalSpectrum.awayCompletionIdeal I g).FG :=
    FormalSpectrum.awayCompletionIdeal_fg I g hIfg
  have hrange : Set.range (FormalSpectrum.basicOpenChart I g).base =
      (FormalSpectrum.basicOpen I g : Set (FormalSpectrum I)) :=
    FormalSpectrum.range_basicOpenChart_base I g hIfg
  refine ⟨FormalSpectrum.awayCompletion I g, inferInstance, inferInstance,
    FormalSpectrum.awayCompletionIdeal I g, hJadic,
    FormalSpectrum.basicOpenChart I g ≫ m, hJfg, ?_, ?_,
    LocallyRingedSpace.IsOpenImmersion.comp _ _⟩
  · -- `x` lies in the range of the composite: pick the preimage `y` of `x₀`
    have hx₀mem : x₀ ∈ Set.range (FormalSpectrum.basicOpenChart I g).base := by
      rw [hrange]; exact hx₀v
    obtain ⟨y, hy⟩ := hx₀mem
    refine ⟨y, ?_⟩
    simp only [LocallyRingedSpace.comp_base, TopCat.comp_app]
    rw [hy]; exact hx₀
  · -- the range of the composite is contained in `U`
    rw [LocallyRingedSpace.comp_base]
    intro z hz
    simp only [TopCat.comp_app, Set.mem_range] at hz
    obtain ⟨w, rfl⟩ := hz
    -- `basicOpenChart.base w ∈ basicOpen I g ⊆ m ⁻¹' U`
    have hw : (FormalSpectrum.basicOpenChart I g).base w ∈
        (FormalSpectrum.basicOpen I g : Set (FormalSpectrum I)) := by
      rw [← hrange]; exact ⟨w, rfl⟩
    exact hvsub hw

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
