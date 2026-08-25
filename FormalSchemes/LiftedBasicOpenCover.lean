import FormalSchemes.OpenImmersionSourceFormalScheme
import FormalSchemes.AdicOnSections
import FormalSchemes.OpenCoverHomExt

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Covering the source of an open immersion into `Spf J` by lifted basic-open charts

Let `pf : W ⟶ Spf J` be an open immersion of locally ringed spaces whose target is the formal
spectrum of a finitely generated adic ring, with `W` underlying a formal scheme `V`. The basic-open
charts `FormalSpectrum.basicOpenChart J g` form a neighbourhood basis of `Spf J`, so those contained
in the open `range pf` can be lifted back through `pf` to an open cover of `V`. Crucially each cover
map `wᵥ` satisfies `wᵥ ≫ pf = basicOpenChart J gᵥ` (`lift_fac`), so `wᵥ ≫ pf` is *adic on global
sections* (issue 460a / `FormalSchemes.AdicOnSections`). This is exactly the cover the general
fibre-product overlap obligation (issue 234c) needs to discharge its continuity requirement without
appealing to the false general "open immersions are adic" statement (issue 460).

## Main definitions and results

* `FormalScheme.LiftedBasicChart` / `nonempty_liftedBasicChart` / `liftedBasicChart`: the per-point
  chart — a basic-open chart of `Spf J` contained in `range pf`, lifted through `pf`.
* `FormalScheme.liftedBasicCover`: the resulting open cover of `V`.
* `FormalScheme.liftedBasicCover_map_comp_pf`: each cover map composed with `pf` is the underlying
  basic-open chart (the adicity witness).

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §§10.4, 10.7.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology FormalSpectrum

universe u

namespace FormalSpectrum

/-- **Basic-open charts form a neighbourhood basis of `Spf J`.** Every point `x` of an open set `U`
in the formal spectrum of a finitely generated adic ring `J` admits a basic-open chart
`basicOpenChart J g` whose range contains `x` and is contained in `U`. Specialisation of the
affine-chart neighbourhood-basis argument to the identity ambient chart. -/
theorem exists_basicOpenChart_subset {S : Type u} [CommRing S] [TopologicalSpace S] (J : Ideal S)
    [IsAdicRing J] (hJ : J.FG) (x : FormalSpectrum J) (U : Set (FormalSpectrum J)) (hU : IsOpen U)
    (hxU : x ∈ U) :
    ∃ g : S, x ∈ Set.range (basicOpenChart J g).base ∧
      Set.range (basicOpenChart J g).base ⊆ U := by
  obtain ⟨v, ⟨g, rfl⟩, hxv, hvsub⟩ :=
    (isTopologicalBasis_basicOpen J).exists_subset_of_mem_open hxU hU
  refine ⟨g, ?_, ?_⟩
  · rw [range_basicOpenChart_base J g hJ]; exact hxv
  · rw [range_basicOpenChart_base J g hJ]; exact hvsub

end FormalSpectrum

namespace AlgebraicGeometry.FormalScheme

variable {S : Type u} [CommRing S] [TopologicalSpace S] {J : Ideal S} [IsAdicRing J]

/-- The lift of a basic-open chart of `Spf J` (whose range sits inside `range pf`) through the open
immersion `pf` is again an open immersion. Mirrors `exists_lifted_affineChart`. -/
theorem isOpenImmersion_lift_basicOpenChart {W : LocallyRingedSpace.{u}}
    (pf : W ⟶ FormalSpectrum.locallyRingedSpaceObj J) [LocallyRingedSpace.IsOpenImmersion pf]
    (hJ : J.FG) (g : S)
    (hsub : Set.range (basicOpenChart J g).base ⊆ Set.range pf.base) :
    LocallyRingedSpace.IsOpenImmersion
      (LocallyRingedSpace.IsOpenImmersion.lift pf (basicOpenChart J g) hsub) := by
  haveI := FormalSpectrum.isOpenImmersion_basicOpenChart J g hJ
  haveI := LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset pf
    (basicOpenChart J g) hsub
  have hlift : LocallyRingedSpace.IsOpenImmersion.lift pf (basicOpenChart J g) hsub
      = inv (pullback.snd pf (basicOpenChart J g)) ≫ pullback.fst pf (basicOpenChart J g) := rfl
  rw [hlift]
  infer_instance

/-- The per-point chart covering the source `W` of an open immersion `pf : W ⟶ Spf J`: a basic-open
chart of `Spf J` whose range lies in `range pf`, lifted back through `pf`, together with the point
it covers. -/
structure LiftedBasicChart {W : LocallyRingedSpace.{u}}
    (pf : W ⟶ FormalSpectrum.locallyRingedSpaceObj J)
    [LocallyRingedSpace.IsOpenImmersion pf] (v : W) where
  /-- The basic-open parameter. -/
  g : S
  /-- The basic-open chart's range lies inside the open range of `pf`. -/
  hsub : Set.range (basicOpenChart J g).base ⊆ Set.range pf.base
  /-- The lift covers `v`. -/
  hmem : v ∈ Set.range
    (LocallyRingedSpace.IsOpenImmersion.lift pf (basicOpenChart J g) hsub).base

variable {W : LocallyRingedSpace.{u}}

/-- A lifted basic-open chart exists around every point: pick a basic-open chart of `Spf J` around
`pf.base v` inside the open `range pf` (`exists_basicOpenChart_subset`); its lift covers `v` because
`lift_range` computes the lift's range as `pf ⁻¹' (range basicOpenChart)`. -/
theorem nonempty_liftedBasicChart (pf : W ⟶ FormalSpectrum.locallyRingedSpaceObj J)
    [H : LocallyRingedSpace.IsOpenImmersion pf] (hJ : J.FG) (v : W) :
    Nonempty (LiftedBasicChart pf v) := by
  have hopen : IsOpen (Set.range pf.base) := H.base_open.isOpen_range
  obtain ⟨g, hxmem, hxsub⟩ :=
    FormalSpectrum.exists_basicOpenChart_subset J hJ (pf.base v) (Set.range pf.base) hopen ⟨v, rfl⟩
  refine ⟨{ g := g, hsub := hxsub, hmem := ?_ }⟩
  rw [LocallyRingedSpace.IsOpenImmersion.lift_range]
  exact hxmem

/-- A chosen lifted basic-open chart around each point, via `Classical.choice`. -/
def liftedBasicChart (pf : W ⟶ FormalSpectrum.locallyRingedSpaceObj J)
    [LocallyRingedSpace.IsOpenImmersion pf] (hJ : J.FG) (v : W) : LiftedBasicChart pf v :=
  (nonempty_liftedBasicChart pf hJ v).some

/-- **The lifted basic-open cover** of the source `V` of an open immersion `pf : V.toLRS ⟶ Spf J`
(with `J` finitely generated): indexed by the points of `V`, the piece at `v` is the basic-open
chart `Spf (J{1/gᵥ})` of `Spf J` lifted back through `pf`. -/
def liftedBasicCover (V : FormalScheme.{u})
    (pf : V.toLocallyRingedSpace ⟶ FormalSpectrum.locallyRingedSpaceObj J)
    [LocallyRingedSpace.IsOpenImmersion pf] (hJ : J.FG) : FormalScheme.OpenCover V where
  J := V
  obj v :=
    letI : IsAdicRing (FormalSpectrum.awayCompletionIdeal J (liftedBasicChart pf hJ v).g) :=
      FormalSpectrum.isAdicRing_awayCompletionIdeal J (liftedBasicChart pf hJ v).g hJ
    FormalScheme.Spf (FormalSpectrum.awayCompletionIdeal J (liftedBasicChart pf hJ v).g)
  map v := FormalScheme.Hom.mk
    (LocallyRingedSpace.IsOpenImmersion.lift pf (basicOpenChart J (liftedBasicChart pf hJ v).g)
      (liftedBasicChart pf hJ v).hsub)
  f v := v
  covers v := (liftedBasicChart pf hJ v).hmem
  isOpenImmersion v :=
    isOpenImmersion_lift_basicOpenChart pf hJ (liftedBasicChart pf hJ v).g
      (liftedBasicChart pf hJ v).hsub

/-- **Each lifted cover map composed with `pf` is the underlying basic-open chart.** This is
`IsOpenImmersion.lift_fac`; it exhibits `(map v) ≫ pf` as a basic-open chart, hence adic on global
sections (issue 460a). -/
theorem liftedBasicCover_map_comp_pf (V : FormalScheme.{u})
    (pf : V.toLocallyRingedSpace ⟶ FormalSpectrum.locallyRingedSpaceObj J)
    [LocallyRingedSpace.IsOpenImmersion pf] (hJ : J.FG) (v : (liftedBasicCover V pf hJ).J) :
    ((liftedBasicCover V pf hJ).map v).toLRSHom ≫ pf =
      basicOpenChart J (liftedBasicChart pf hJ v).g :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac pf (basicOpenChart J (liftedBasicChart pf hJ v).g)
    (liftedBasicChart pf hJ v).hsub

end AlgebraicGeometry.FormalScheme

end
