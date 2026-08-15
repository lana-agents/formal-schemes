import FormalSchemes.LocallyFG

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The source of an open immersion into a formal scheme is a (LocallyFG) formal scheme

If `j : W ⟶ Y.toLocallyRingedSpace` is an open immersion of locally ringed spaces whose target is a
formal scheme `Y`, then `W` underlies a formal scheme, and it is `LocallyFG` whenever `Y` is. The
proof lifts, around each point, a finitely-generated affine chart of `Y` (contained in the open
range of `j`) back through the open immersion `j`, producing an affine open-immersion chart
`Spf K ⟶ W`; this single chart supplies both the `local_affine` datum (via `isoOfRangeEq` against
`W.ofRestrict`) and the `LocallyFG` witness.

This packages the pairwise-overlap pullbacks `pullback (𝒰.cmap c) (𝒰.cmap c')` of a
`FormalScheme.OpenCover` as `LocallyFG` formal schemes — the domains that the mediating-morphism
assembly of the general fibre-product universal property (EGA I §10.7, issue 234c) needs in order to
discharge the `glueMorphisms` overlap obligation via `fibreLift_unique` (issue 234d).

## Main definitions and results

* `FormalScheme.ofOpenImmersion`: the formal scheme structure on the source `W` of an open
  immersion into a `LocallyFG` formal scheme (its `toLocallyRingedSpace` is `W`, definitionally).
* `FormalScheme.ofOpenImmersion_locallyFG`: it is `LocallyFG`.
* `FormalScheme.overlapFormalScheme` / `overlapFormalScheme_locallyFG`: the instantiation to
  `pullback (𝒰.cmap c) (𝒰.cmap c')`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology FormalSpectrum

universe u

namespace AlgebraicGeometry.FormalScheme

variable {W : LocallyRingedSpace.{u}} {Y : FormalScheme.{u}}

/-- The **lifted affine chart** around a point `x : W`: a finitely generated affine chart of `Y`
around `j.base x`, contained in the open range of `j`, lifted back through the open immersion `j`.
Bundled as an existence statement supplying the ingredients both `local_affine` and `LocallyFG`
consume. -/
theorem exists_lifted_affineChart
    (j : W ⟶ Y.toLocallyRingedSpace) [H : LocallyRingedSpace.IsOpenImmersion j]
    (hY : Y.LocallyFG) (x : W) :
    ∃ (K : Type u) (_ : CommRing K) (_ : TopologicalSpace K) (KI : Ideal K) (_ : IsAdicRing KI)
      (f' : FormalSpectrum.locallyRingedSpaceObj KI ⟶ W),
      KI.FG ∧ x ∈ Set.range f'.base ∧ LocallyRingedSpace.IsOpenImmersion f' := by
  -- `range j.base` is open (open immersion) and contains `j.base x`.
  have hjopen : IsOpen (Set.range j.base) := H.base_open.isOpen_range
  obtain ⟨K, _, _, KI, _, fc, hKfg, hxc, hsub, hoic⟩ :=
    Y.exists_affineChart_subset hY (j.base x) (Set.range j.base) hjopen ⟨x, rfl⟩
  -- Lift `fc : Spf KI ⟶ Y` through `j`; the lift is an open immersion.
  letI := hoic
  have H' : Set.range fc.base ⊆ Set.range j.base := hsub
  -- Providing the lifted chart as a focused goal keeps the ideal `KI` concrete, avoiding an
  -- expensive `delta`-unfolding of `locallyRingedSpaceObj` during unification.
  refine ⟨K, ‹_›, ‹_›, KI, ‹_›, ?_, hKfg, ?_, ?_⟩
  · exact LocallyRingedSpace.IsOpenImmersion.lift j fc H'
  · -- `x ∈ range (lift).base`: `lift.base` has range `j.base ⁻¹' range fc.base` (`lift_range`),
    -- and `j.base x ∈ range fc.base` (from `hxc`), so `x` is in the preimage.
    rw [LocallyRingedSpace.IsOpenImmersion.lift_range]
    exact hxc
  · -- The lift of an open immersion along an open immersion is an open immersion.
    -- `lift j fc H' = inv (pullback.snd j fc) ≫ pullback.fst j fc`; the first factor is an iso
    -- (`pullback_snd_isIso_of_range_subset`) and the second an open immersion
    -- (`pullback_fst_of_right`), so the composite is an open immersion.
    haveI := LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset j fc H'
    have hlift : LocallyRingedSpace.IsOpenImmersion.lift j fc H'
        = inv (pullback.snd j fc) ≫ pullback.fst j fc := rfl
    rw [hlift]
    infer_instance

/-- **The formal scheme structure on the source of an open immersion into a `LocallyFG` formal
scheme.** Its underlying locally ringed space is `W`, definitionally. -/
def ofOpenImmersion
    (j : W ⟶ Y.toLocallyRingedSpace) [H : LocallyRingedSpace.IsOpenImmersion j]
    (hY : Y.LocallyFG) : FormalScheme.{u} :=
  -- Around every point of `W` the lifted affine chart is an affine open-immersion neighbourhood,
  -- so the local formal-scheme criterion `IsOpenImmersion.formalScheme` (which internally packages
  -- `isoOfRangeEq` against `ofRestrict`) applies, with underlying locally ringed space `W`.
  LocallyRingedSpace.IsOpenImmersion.formalScheme W fun x => by
    obtain ⟨K, _, _, KI, _, f', hKfg, hxmem, hoi'⟩ := exists_lifted_affineChart j hY x
    -- Provide the chart morphism as a focused goal so `KI` stays concrete (see above).
    refine ⟨K, ‹_›, ‹_›, KI, ‹_›, ?_, ?_, ?_⟩
    · exact f'
    · exact hxmem
    · exact hoi'

@[simp]
theorem ofOpenImmersion_toLocallyRingedSpace
    (j : W ⟶ Y.toLocallyRingedSpace) [LocallyRingedSpace.IsOpenImmersion j] (hY : Y.LocallyFG) :
    (ofOpenImmersion j hY).toLocallyRingedSpace = W := rfl

/-- The source of an open immersion into a `LocallyFG` formal scheme is `LocallyFG`. -/
theorem ofOpenImmersion_locallyFG
    (j : W ⟶ Y.toLocallyRingedSpace) [LocallyRingedSpace.IsOpenImmersion j] (hY : Y.LocallyFG) :
    (ofOpenImmersion j hY).LocallyFG := by
  intro x
  obtain ⟨K, _, _, KI, _, f', hKfg, hxmem, hoi'⟩ := exists_lifted_affineChart j hY x
  -- Provide the chart morphism as a focused goal so `KI` stays concrete (see
  -- `exists_lifted_affineChart`), avoiding a costly `delta`-unfolding of `locallyRingedSpaceObj`.
  refine ⟨K, ‹_›, ‹_›, KI, ‹_›, ?_, hKfg, ?_, ?_⟩
  · exact f'
  · exact hxmem
  · exact hoi'

end AlgebraicGeometry.FormalScheme

namespace AlgebraicGeometry.FormalScheme.OpenCover

variable {X : FormalScheme.{u}} (𝒰 : OpenCover.{u} X)

/-- The pairwise-overlap pullback `pullback (𝒰.cmap c) (𝒰.cmap c')` of an open cover, packaged as a
formal scheme via the open immersion `pullback.fst` into the affine chart `𝒰.obj c`. Needs the chart
piece to be `LocallyFG` (it is, when its defining ideal is finitely generated). -/
def overlapFormalScheme (c c' : 𝒰.J) (h : (𝒰.obj c).LocallyFG) : FormalScheme.{u} :=
  -- `(𝒰.map i).toLRSHom` is the underlying open immersion of the `i`-th chart (this is what
  -- `OpenCover.cmap` abbreviates); inlining it avoids importing the gluing module.
  letI : LocallyRingedSpace.IsOpenImmersion
      (Limits.pullback.fst (𝒰.map c).toLRSHom (𝒰.map c').toLRSHom) := inferInstance
  ofOpenImmersion (Limits.pullback.fst (𝒰.map c).toLRSHom (𝒰.map c').toLRSHom) h

theorem overlapFormalScheme_locallyFG (c c' : 𝒰.J) (h : (𝒰.obj c).LocallyFG) :
    (𝒰.overlapFormalScheme c c' h).LocallyFG :=
  ofOpenImmersion_locallyFG _ h

end AlgebraicGeometry.FormalScheme.OpenCover

end
