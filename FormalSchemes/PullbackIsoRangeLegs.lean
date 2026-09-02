import FormalSchemes.PullbackRangeLRS

set_option linter.style.header false

/-!
# Isolated-leg characterizations of `pullbackIsoOfRangeEq`

Continuation of `FormalSchemes.PullbackRangeLRS`. For open immersions `f : X ⟶ Z`, `g : Y ⟶ Z` of
locally ringed spaces and an open immersion `h : W ⟶ Z` with `range h = im f ∩ im g`, the merged
`pullbackIsoOfRangeEq f g h e : W ≅ pullback f g` identifies `W` with the pullback, but was
characterized there only *after* composing its legs with the maps `f`, `g` down to the common target
(`pullbackIsoOfRangeEq_hom_fst_comp`, `pullbackIsoOfRangeEq_hom_snd_comp`,
`pullbackIsoOfRangeEq_inv_comp`).

This file records the *isolated*-leg forms, obtained by cancelling the (mono) open immersions
`f`, `g`:

* `pullbackIsoOfRangeEq_hom_fst` / `pullbackIsoOfRangeEq_hom_snd`: the two legs of the `hom`
  direction are the open-immersion lifts `IsOpenImmersion.lift f h _` / `IsOpenImmersion.lift g h _`
  of `h` through `f` / `g`.
* `pullbackIsoOfRangeEq_fst_eq` / `pullbackIsoOfRangeEq_snd_eq`: dually, the pullback projections
  themselves factor through the `Iso.inv` direction as `inv ≫ lift f h _` / `inv ≫ lift g h _`.

These are exactly the shape consumed by the transition cocycle (`t'` / `t_fac` / `cocycle`) of a
glue datum whose overlap objects are cut out by open immersions of prescribed image and thereby
identified with concrete objects by range (`PullbackRangeLRS`): a summand-permuting map between the
identified overlap objects, composed with a pullback projection, reduces by these lemmas to the
mono-cancelled `lift`-uniqueness argument, so no explicit pullback-plumbing is needed. Reusable both
for the Tate self-product `𝔈_q ×_{Spf R} 𝔈_q` (issue 237) and the general fibre product `X ×_S Y`
(issue 233).
-/

open CategoryTheory Limits

namespace AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion

variable {X Y Z W : LocallyRingedSpace} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ Z)
  [LocallyRingedSpace.IsOpenImmersion f] [LocallyRingedSpace.IsOpenImmersion g]
  [LocallyRingedSpace.IsOpenImmersion h]
  (e : Set.range h.base = Set.range f.base ∩ Set.range g.base)

/-- The `pullback.fst` leg of `pullbackIsoOfRangeEq` is the open-immersion lift of `h` through
`f`. -/
theorem pullbackIsoOfRangeEq_hom_fst :
    (pullbackIsoOfRangeEq f g h e).hom ≫ pullback.fst f g =
      lift f h (e.le.trans Set.inter_subset_left) := by
  rw [← cancel_mono f, Category.assoc, pullbackIsoOfRangeEq_hom_fst_comp, lift_fac]

/-- The `pullback.snd` leg of `pullbackIsoOfRangeEq` is the open-immersion lift of `h` through
`g`. -/
theorem pullbackIsoOfRangeEq_hom_snd :
    (pullbackIsoOfRangeEq f g h e).hom ≫ pullback.snd f g =
      lift g h (e.le.trans Set.inter_subset_right) := by
  rw [← cancel_mono g, Category.assoc, pullbackIsoOfRangeEq_hom_snd_comp, lift_fac]

/-- The first pullback projection factors through the `Iso.inv` direction of
`IsOpenImmersion.pullbackIsoOfRangeEq` as `inv ≫ lift f h _`. -/
theorem pullbackIsoOfRangeEq_fst_eq :
    pullback.fst f g =
      (pullbackIsoOfRangeEq f g h e).inv ≫ lift f h (e.le.trans Set.inter_subset_left) := by
  rw [← pullbackIsoOfRangeEq_hom_fst f g h e, Iso.inv_hom_id_assoc]

/-- The second pullback projection factors through the `Iso.inv` direction of
`IsOpenImmersion.pullbackIsoOfRangeEq` as `inv ≫ lift g h _`. -/
theorem pullbackIsoOfRangeEq_snd_eq :
    pullback.snd f g =
      (pullbackIsoOfRangeEq f g h e).inv ≫ lift g h (e.le.trans Set.inter_subset_right) := by
  rw [← pullbackIsoOfRangeEq_hom_snd f g h e, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
