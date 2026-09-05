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
  which is the whole content: the shrinking itself is
  `AlgebraicGeometry.FormalScheme.exists_basicOpenRefine_subset` (`FormalSchemes.LocallyFG`),
  shared with every other neighbourhood-basis lemma on the tree, and this file adds only the
  transport.

This is the base-relative strengthening of
`AlgebraicGeometry.FormalScheme.exists_affineChart_subset` (`FormalSchemes.LocallyFG`), which takes
its `AlgebraicGeometry.FormalScheme.LocallyFG` witness as an explicit argument rather than living in
that predicate's namespace; a datum-level witness `AdicOverBaseLocallyFG D.xGlued D.xStructMap`
(`FormalSchemes.BothDatumAdicOverBase`) then supplies the diagonal's refined charts with their
missing adic-over-base bound.

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
`s`. The chart is `AlgebraicGeometry.FormalScheme.AffineChart.basicOpenRefine` of the
adic-over-base witness at `x`; the shrinking step itself is
`AlgebraicGeometry.FormalScheme.exists_basicOpenRefine_subset` (`FormalSchemes.LocallyFG`), shared
with `AlgebraicGeometry.FormalScheme.exists_affineChart_subset` and with the `ψ`-relative lemmas of
`FormalSchemes.AdicSectionsChart`, and the only step proper to this lemma is the transport
`FormalSpectrum.le_comap_globalSectionsMap_basicOpenChart_comp`, which is what makes the refinement
preserve adicity-over-base. -/
theorem exists_affineChart_subset_adicOverBase (X : FormalScheme.{u})
    (s : X.toLocallyRingedSpace ⟶ FormalSpectrum.locallyRingedSpaceObj I)
    (hX : AdicOverBaseLocallyFG X s) (x : X) (U : Set X) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ (S : Type u) (_ : CommRing S) (_ : TopologicalSpace S) (J : Ideal S) (_ : IsAdicRing J)
      (f : FormalSpectrum.locallyRingedSpaceObj J ⟶ X.toLocallyRingedSpace),
      J.FG ∧ x ∈ Set.range f.base ∧ Set.range f.base ⊆ U ∧
        LocallyRingedSpace.IsOpenImmersion f ∧
        I ≤ J.comap (FormalSpectrum.globalSectionsMap I J (f ≫ s)) := by
  obtain ⟨S₀, _, _, I₀, _, m, hI₀fg, hmem₀, hm, hadic⟩ := hX x
  -- bundle the adic-over-base witness as an `AffineChart` and shrink it into `U`
  let c : AffineChart X x := { R := S₀, I := I₀, map := m, mem := hmem₀, isOpenImmersion := hm }
  obtain ⟨g, hadicg, hoi, hmem', hsub⟩ :=
    exists_basicOpenRefine_subset c hI₀fg U hU hxU
  refine ⟨FormalSpectrum.awayCompletion c.I g, inferInstance, inferInstance,
    FormalSpectrum.awayCompletionIdeal c.I g, hadicg, (c.basicOpenRefine g hmem').map,
    FormalSpectrum.awayCompletionIdeal_fg c.I g hI₀fg, (c.basicOpenRefine g hmem').mem, hsub,
    hoi, ?_⟩
  -- adic over the base: the basic-open refinement preserves adicity-over-`s`
  have hassoc : (FormalSpectrum.basicOpenChart c.I g ≫ m) ≫ s =
      FormalSpectrum.basicOpenChart c.I g ≫ (m ≫ s) := Category.assoc _ _ _
  change I ≤ (FormalSpectrum.awayCompletionIdeal c.I g).comap
    (FormalSpectrum.globalSectionsMap I (FormalSpectrum.awayCompletionIdeal c.I g)
      ((FormalSpectrum.basicOpenChart c.I g ≫ m) ≫ s))
  rw [hassoc]
  exact FormalSpectrum.le_comap_globalSectionsMap_basicOpenChart_comp I c.I g (m ≫ s) hadic

end AlgebraicGeometry.FormalScheme

end
