import FormalSchemes.PullbackRangeLRS

set_option linter.style.header false

/-!
# Symmetry of `pullbackIsoOfRangeEq`

Continuation of `FormalSchemes.PullbackRangeLRS`. For open immersions `f : X ⟶ Z`, `g : Y ⟶ Z` of
locally ringed spaces and an open immersion `h : W ⟶ Z` with `range h = im f ∩ im g`, the merged
`pullbackIsoOfRangeEq f g h e : W ≅ pullback f g` identifies `W`, cut out by prescribed image, with
the pullback of `f` and `g`. Since the image condition `im f ∩ im g` is symmetric in `f` and `g`,
the *same* `W` is equally the pullback of `g` and `f`; this file records that the two
identifications differ exactly by the canonical
`pullbackSymmetry f g : pullback f g ≅ pullback g f`.

* `pullbackIsoOfRangeEq_hom_symm`: the `hom` legs agree, `(pullbackIsoOfRangeEq f g h e).hom ≫
  (pullbackSymmetry f g).hom = (pullbackIsoOfRangeEq g f h e').hom`, where `e'` is the range
  equality with the intersection commuted.
* `pullbackIsoOfRangeEq_trans_symm`: the packaged iso form,
  `pullbackIsoOfRangeEq f g h e ≪≫ pullbackSymmetry f g = pullbackIsoOfRangeEq g f h e'`.
* `pullbackIsoOfRangeEq_symm_inv`: the dual `inv` form.

This is the compatibility a glue-datum cocycle needs when it identifies an overlap object `V i j =
pullback (fᵢ) (fⱼ)` with a concrete range-cut-out object: the concrete object does not know the
order of the two charts, so its identifications with `V i j` and with `V j i = pullback (fⱼ) (fᵢ)`
must be related by `pullbackSymmetry`. Reusable both for the Tate self-product `𝔈_q ×_{Spf R} 𝔈_q`
(issue 237) and the general fibre product `X ×_S Y` (issue 233).
-/

open CategoryTheory Limits

namespace AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion

variable {X Y Z W : LocallyRingedSpace} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ Z)
  [LocallyRingedSpace.IsOpenImmersion f] [LocallyRingedSpace.IsOpenImmersion g]
  [LocallyRingedSpace.IsOpenImmersion h]
  (e : Set.range h.base = Set.range f.base ∩ Set.range g.base)

/-- The image condition `im f ∩ im g` is symmetric, so `h` is equally the pullback of `g` and `f`;
the two identifications differ by `pullbackSymmetry`. This is the `hom`-leg form. -/
theorem pullbackIsoOfRangeEq_hom_symm :
    (pullbackIsoOfRangeEq f g h e).hom ≫ (pullbackSymmetry f g).hom =
      (pullbackIsoOfRangeEq g f h (e.trans (Set.inter_comm _ _))).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSymmetry_hom_comp_fst, ← cancel_mono g, Category.assoc,
      Category.assoc, pullbackIsoOfRangeEq_hom_snd_comp f g h e,
      pullbackIsoOfRangeEq_hom_fst_comp g f h (e.trans (Set.inter_comm _ _))]
  · rw [Category.assoc, pullbackSymmetry_hom_comp_snd, ← cancel_mono f, Category.assoc,
      Category.assoc, pullbackIsoOfRangeEq_hom_fst_comp f g h e,
      pullbackIsoOfRangeEq_hom_snd_comp g f h (e.trans (Set.inter_comm _ _))]

/-- Packaged iso form of `pullbackIsoOfRangeEq_hom_symm`: identifying `h` with `pullback f g` and
then swapping the factors is the identification of `h` with `pullback g f`. -/
theorem pullbackIsoOfRangeEq_trans_symm :
    pullbackIsoOfRangeEq f g h e ≪≫ pullbackSymmetry f g =
      pullbackIsoOfRangeEq g f h (e.trans (Set.inter_comm _ _)) := by
  ext1
  rw [Iso.trans_hom]
  exact pullbackIsoOfRangeEq_hom_symm f g h e

/-- The `inv`-leg dual of `pullbackIsoOfRangeEq_hom_symm`. -/
theorem pullbackIsoOfRangeEq_symm_inv :
    (pullbackSymmetry f g).inv ≫ (pullbackIsoOfRangeEq f g h e).inv =
      (pullbackIsoOfRangeEq g f h (e.trans (Set.inter_comm _ _))).inv := by
  rw [← Iso.trans_inv, pullbackIsoOfRangeEq_trans_symm]

end AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
