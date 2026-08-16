import FormalSchemes.LocallyFG
import FormalSchemes.AdicOnSections

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Adic-over-base affine charts and the adic-over-base neighborhood basis

The general `fibreLift` (issue 464) and the general diagonal (issue 467) carry a standing continuity
hypothesis `hs c : I ≤ (bothRefinedChart a b hZ c).J.comap (refinedStructHom a b hZ c)` — the
"adic on global sections" obligation on each refined-cover piece's structure map into the base
`Spf I`. For the diagonal (`a = b = 𝟙`), `refinedStructHom c` collapses (via
`map_comp_a_xStructMap_eq` and `globalSectionsMap_xStructMapChart`) to
`globalSectionsMap (xFactor c) ∘ algebraMap R (A_i)`, so `hs` reduces to the refined-chart X-leg
`xFactor c` being **adic on global sections**.

That adicity is *not* free: the general statement "an open immersion is adic on global sections" is
FALSE (issue 460 — even a full LRS iso can be non-adic, the `cofinalSpfIso` counterexample). The
refined charts of `xGlued` are adic over the base only because they inherit the R-adic structure of
`xGlued`'s gluing charts `ι i`, whose structure map is `xStructMapChart i = algebraMap R (A_i)`.

This file isolates that inheritance as reusable, base-relative infrastructure:

* `FormalScheme.AdicOverBaseLocallyFG X s`: every point of `X` has a finitely generated affine
  open-immersion chart `f` that is *adic on global sections over the base* `s : X ⟶ Spf I`, i.e.
  `I ≤ J.comap (Γ (f ≫ s))`.
* `FormalScheme.AdicOverBaseLocallyFG.locallyFG`: it refines `LocallyFG`.
* `FormalScheme.exists_affineChart_subset_adicOverBase`: on such an `X`, adic-over-base affine
  charts form a neighborhood basis — every point in an open `U` has a finitely generated affine
  chart contained in `U` that is adic on global sections over `s`. The basic-open refinement
  preserves adicity-over-base (`AdicOnSections.le_comap_globalSectionsMap_basicOpenChart_comp`),
  which is the whole content.

This is the base-relative strengthening of `LocallyFG.exists_affineChart_subset`; a datum-level
witness `AdicOverBaseLocallyFG D.xGlued D.xStructMap` (`BothDatumAdicOverBase.lean`) then supplies
the diagonal's refined charts with their missing adic-over-base bound.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4.6, §10.7, §10.12.
-/

noncomputable section

open CategoryTheory TopologicalSpace Topology FormalSpectrum

universe u

namespace AlgebraicGeometry.FormalScheme

variable {R : Type u} [CommRing R] [TopologicalSpace R] {I : Ideal R} [IsAdicRing I]

/-- A formal scheme `X` with a base morphism `s : X ⟶ Spf I` is **adic over the base on a
neighborhood basis** if every point has a finitely generated affine open-immersion chart `f` whose
composite `f ≫ s` into the base is adic on global sections (carries the base ideal of definition `I`
into the chart's ideal of definition `J`). This is the base-relative refinement of `LocallyFG`. -/
def AdicOverBaseLocallyFG (X : FormalScheme.{u})
    (s : X.toLocallyRingedSpace ⟶ FormalSpectrum.locallyRingedSpaceObj I) : Prop :=
  ∀ x : X, ∃ (S : Type u) (_ : CommRing S) (_ : TopologicalSpace S) (J : Ideal S)
    (_ : IsAdicRing J) (f : FormalSpectrum.locallyRingedSpaceObj J ⟶ X.toLocallyRingedSpace),
    J.FG ∧ x ∈ Set.range f.base ∧ LocallyRingedSpace.IsOpenImmersion f ∧
      I ≤ J.comap (FormalSpectrum.globalSectionsMap I J (f ≫ s))

/-- An adic-over-base scheme is in particular locally finitely generated: drop the adic-over-base
conjunct. -/
theorem AdicOverBaseLocallyFG.locallyFG {X : FormalScheme.{u}}
    {s : X.toLocallyRingedSpace ⟶ FormalSpectrum.locallyRingedSpaceObj I}
    (hX : AdicOverBaseLocallyFG X s) : X.LocallyFG := by
  intro x
  obtain ⟨S, hS, hT, J, hJadic, f, hJfg, hmem, hoi, -⟩ := hX x
  exact ⟨S, hS, hT, J, hJadic, f, hJfg, hmem, hoi⟩

/-- **Adic-over-base affine charts form a neighborhood basis.** On a scheme that is adic over the
base `s : X ⟶ Spf I`, every point `x` in an open set `U` has a finitely generated affine
open-immersion chart whose range is contained in `U` *and* which is adic on global sections over
`s`. The chart is `basicOpenChart I₀ g ≫ m` for the adic-over-base witness `m` at `x`; the
basic-open refinement preserves adicity-over-base by
`le_comap_globalSectionsMap_basicOpenChart_comp`. -/
theorem exists_affineChart_subset_adicOverBase (X : FormalScheme.{u})
    (s : X.toLocallyRingedSpace ⟶ FormalSpectrum.locallyRingedSpaceObj I)
    (hX : AdicOverBaseLocallyFG X s) (x : X) (U : Set X) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ (S : Type u) (_ : CommRing S) (_ : TopologicalSpace S) (J : Ideal S) (_ : IsAdicRing J)
      (f : FormalSpectrum.locallyRingedSpaceObj J ⟶ X.toLocallyRingedSpace),
      J.FG ∧ x ∈ Set.range f.base ∧ Set.range f.base ⊆ U ∧
        LocallyRingedSpace.IsOpenImmersion f ∧
        I ≤ J.comap (FormalSpectrum.globalSectionsMap I J (f ≫ s)) := by
  obtain ⟨S₀, _, _, I₀, _, m, hI₀fg, ⟨x₀, hx₀⟩, hm, hadic⟩ := hX x
  -- the preimage of `U` under the witness chart is an open set containing `x₀`
  have hcont : Continuous m.base := m.base.hom.continuous
  have hopen : IsOpen (m.base ⁻¹' U) := hU.preimage hcont
  have hmem : x₀ ∈ m.base ⁻¹' U := by
    simp only [Set.mem_preimage, hx₀]; exact hxU
  obtain ⟨v, ⟨g, rfl⟩, hx₀v, hvsub⟩ :=
    (isTopologicalBasis_basicOpen I₀).exists_subset_of_mem_open hmem hopen
  haveI hJadic : IsAdicRing (FormalSpectrum.awayCompletionIdeal I₀ g) :=
    AdicCompletion.isAdicRing_map (I₀.map (algebraMap S₀ (Localization.Away g))) (hI₀fg.map _)
  haveI hoi : LocallyRingedSpace.IsOpenImmersion (FormalSpectrum.basicOpenChart I₀ g) :=
    FormalSpectrum.isOpenImmersion_basicOpenChart I₀ g hI₀fg
  have hJfg : (FormalSpectrum.awayCompletionIdeal I₀ g).FG := by
    rw [← FormalSpectrum.map_awayCompletionHom I₀ g]
    exact hI₀fg.map _
  have hrange : Set.range (FormalSpectrum.basicOpenChart I₀ g).base =
      (FormalSpectrum.basicOpen I₀ g : Set (FormalSpectrum I₀)) :=
    FormalSpectrum.range_basicOpenChart_base I₀ g hI₀fg
  refine ⟨FormalSpectrum.awayCompletion I₀ g, inferInstance, inferInstance,
    FormalSpectrum.awayCompletionIdeal I₀ g, hJadic,
    FormalSpectrum.basicOpenChart I₀ g ≫ m, hJfg, ?_, ?_,
    LocallyRingedSpace.IsOpenImmersion.comp _ _, ?_⟩
  · -- `x` lies in the range of the composite: pick the preimage `y` of `x₀`
    have hx₀mem : x₀ ∈ Set.range (FormalSpectrum.basicOpenChart I₀ g).base := by
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
    have hw : (FormalSpectrum.basicOpenChart I₀ g).base w ∈
        (FormalSpectrum.basicOpen I₀ g : Set (FormalSpectrum I₀)) := by
      rw [← hrange]; exact ⟨w, rfl⟩
    exact hvsub hw
  · -- adic over the base: the basic-open refinement preserves adicity-over-`s`
    have hassoc : (FormalSpectrum.basicOpenChart I₀ g ≫ m) ≫ s =
        FormalSpectrum.basicOpenChart I₀ g ≫ (m ≫ s) := Category.assoc _ _ _
    rw [hassoc]
    exact FormalSpectrum.le_comap_globalSectionsMap_basicOpenChart_comp I I₀ g (m ≫ s) hadic

end AlgebraicGeometry.FormalScheme

end
