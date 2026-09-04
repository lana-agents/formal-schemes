import FormalSchemes.AwayCompletionRestrictUnique
import FormalSchemes.BasicOpenChartOverlapLegs
import FormalSchemes.BasicOpenImmersionLRS
import FormalSchemes.Gluing

set_option linter.style.header false

/-!
# The basic-open charts of `Spf R` are functorial in the basic open

For an adic ring `(R, I)` with `I` finitely generated and `f : R`, the basic open `D(f) ⊆ Spf R` is
realised as an affine formal scheme by `FormalSpectrum.basicOpenChart I f`
(`FormalSchemes.BasicOpenImmersion`), the open immersion `Spf R{1/f} ⟶ Spf R`. Until now the tree
related two such charts only in the **nested** case: `FormalSpectrum.basicOpenChartFurtherLeft`
(`FormalSchemes.BasicOpenChartOverlapLegs`) is `Spf R{1/(f * g)} ⟶ Spf R{1/f}`, and it exists
because `FormalSpectrum.awayCompletionMulHomLeft` is a further localization followed by a
completion. For a general inclusion `D(g) ⊆ D(f)` there is no such further localization — there is
no ring map `Localization.Away f → Localization.Away g` at all, which is the point of
`FormalSchemes.AwayCompletionRestrict`.

There is, however, a canonical map of the **completions**,
`FormalSpectrum.awayCompletionRestrict`, and it is the unique map under `R`
(`FormalSpectrum.awayCompletionRestrict_unique`, `FormalSchemes.AwayCompletionRestrictUnique`).
This file applies `FormalSpectrum.locallyRingedSpaceMap` to it. The result is that the affine
charts of `Spf R` form a diagram over `Spf R` indexed by the basic opens: every inclusion
`D(g) ≤ D(f)` induces `Spf R{1/g} ⟶ Spf R{1/f}` over `Spf R`, the induced map at `D(f) ≤ D(f)` is
the identity, the induced maps compose along a chain, and each of them is itself an open
immersion — so `D(g)` is an open of the chart at `f`, with its range computed.

## Main definitions and results

* `FormalSpectrum.basicOpenChartRestrict`: the chart inclusion `Spf R{1/g} ⟶ Spf R{1/f}` attached
  to `D(g) ≤ D(f)`.
* `FormalSpectrum.basicOpenChartRestrict_comp_basicOpenChart`: **the factorization**
  `D(g) ↪ D(f) ↪ Spf R` is the chart at `g`.
* `FormalSpectrum.basicOpenChartRestrict_self`, `FormalSpectrum.basicOpenChartRestrict_comp`: the
  identity and the chain law.
* `FormalSpectrum.basicOpenChartFurtherLeft_eq_basicOpenChartRestrict`: the nested chart inclusion
  is the special case `g := f * g`.
* `FormalSpectrum.isOpenImmersion_basicOpenChartRestrict`: **each chart inclusion is an open
  immersion**, by two out of three against
  `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_comp` (`FormalSchemes.Gluing`).
* `FormalSpectrum.base_basicOpenChartRestrict`,
  `FormalSpectrum.range_basicOpenChartRestrict_base`: the underlying map, pointwise, and its range
  as the preimage of `D(g)` in the chart at `f`.

## What is *not* proved here

**Nothing about sections, stalks, germs, colimits or `FormalSpectrum.IsStalkLimit`.** This file is
about morphisms of locally ringed spaces and their underlying maps only. In particular it does not
say that the charts of the basic opens containing a point compute the stalk there: the statements
that come closest are `FormalSpectrum.exists_adicCompletion_germ_eq` and
`FormalSpectrum.exists_basicOpen_res_eq` (`FormalSchemes.StructureSheafStalkBasicOpen`), which are
about *sections* and not about these morphisms, and `FormalSpectrum.IsStalkLimit`
(`FormalSchemes.StructureSheafStalks`) is undecided on this tree in both directions.

**That `FormalSpectrum.basicOpenChartRestrict` induces the structure-sheaf restriction.** Every
statement below is derived from `FormalSpectrum.awayCompletionRestrict_comp_awayCompletionHom` and
the functoriality of `FormalSpectrum.locallyRingedSpaceMap`, neither of which mentions the
structure sheaf, and nothing below is stated about global sections.

The corresponding statement is `FormalSpectrum.globalSectionsMap_basicOpenChartRestrict`
(`FormalSchemes.BasicOpenChartRestrictSections`), and it is downstream of this file rather than in
it. Stating it needs `IsAdicRing` on both ideals of definition, for
`FormalSpectrum.globalSectionsMap`, and a topology on `R` with `IsAdicRing I`, for the
structure-sheaf restriction to exist — instance data no statement below carries, and which would
change the generality of the statements here if it were added to the `variable` block. That file
supplies it at each statement instead.

**A `CategoryTheory.Functor` out of the poset of basic opens.** The identity and chain laws below
are equations between morphisms; nothing packages them, because no consumer wants the packaged
form yet. Note also that the poset of basic opens is not the poset of elements of `R`: distinct
`f` give distinct objects `Spf R{1/f}` here even when `D(f) = D(f')`.

**A reroute of `FormalSpectrum.basicOpenChartFurtherLeft`.** Its consumers
(`FormalSchemes.ChartSpfHomOverlap`, `FormalSchemes.SpfHomOfFamily`,
`FormalSchemes.GeneralFibreProductExposeXAlgebraData` and
`FormalSchemes.ChartSpfHomColimitTarget`) are untouched, and
`FormalSchemes.BasicOpenChartOverlapLegs` keeps it because the leg identifications
`FormalSpectrum.basicOpenChartOverlapIso_hom_fst` / `_hom_snd` are stated in terms of it. The
equation below records that the two agree, so a successor who wants the reroute has it.

## Implementation notes

The order of composition reverses between the ring level and the geometric level:
`FormalSpectrum.awayCompletionRestrict_comp` composes `R{1/f} → R{1/g} → R{1/h}` on the left, and
`FormalSpectrum.locallyRingedSpaceMap_comp` (`FormalSchemes.SpfFunctorial`) turns that into
`basicOpenChartRestrict I g h ≫ basicOpenChartRestrict I f g`.

`LocallyRingedSpace.comp_base` is `rfl`, but `rw [← LocallyRingedSpace.comp_base]` does not fire on
a goal where the base map has already been applied to a point — the applied form is stated
separately as `FormalSpectrum.base_basicOpenChartRestrict`, proved by rewriting the right-hand
side back to the composite and closing by reflexivity, and the range computation goes through it.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1 (10.1.4), §10.8.
* [The Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R) (f g : R)

/-- **The chart inclusion `Spf R{1/g} ⟶ Spf R{1/f}` attached to `D(g) ≤ D(f)`**: `Spf` of the
canonical `FormalSpectrum.awayCompletionRestrict`, whose continuity obligation in the form
`FormalSpectrum.locallyRingedSpaceMap` consumes is `FormalSpectrum.le_comap_awayCompletionRestrict`.

This generalises `FormalSpectrum.basicOpenChartFurtherLeft`
(`FormalSchemes.BasicOpenChartOverlapLegs`) from the nested inclusion `D(f * g) ≤ D(f)` to an
arbitrary one; the two agree, by
`FormalSpectrum.basicOpenChartFurtherLeft_eq_basicOpenChartRestrict`. -/
def basicOpenChartRestrict (hI : I.FG) (hle : basicOpen I g ≤ basicOpen I f) :
    locallyRingedSpaceObj (awayCompletionIdeal I g) ⟶
      locallyRingedSpaceObj (awayCompletionIdeal I f) :=
  locallyRingedSpaceMap (awayCompletionIdeal I f) (awayCompletionIdeal I g)
    (awayCompletionRestrict I f g hI hle) (le_comap_awayCompletionRestrict I f g hI hle)

/-- **The chart at `g` factors through the chart at `f`**: `D(g) ↪ D(f) ↪ Spf R` is the chart at
`g`. This is `Spf` of `FormalSpectrum.awayCompletionRestrict_comp_awayCompletionHom`, and it is the
statement that says the chart inclusion below is a morphism *over* `Spf R`. -/
@[reassoc]
theorem basicOpenChartRestrict_comp_basicOpenChart (hI : I.FG)
    (hle : basicOpen I g ≤ basicOpen I f) :
    basicOpenChartRestrict I f g hI hle ≫ basicOpenChart I f = basicOpenChart I g := by
  have hIK : I ≤ (awayCompletionIdeal I g).comap
      ((awayCompletionRestrict I f g hI hle).comp (awayCompletionHom I f)) := by
    rw [awayCompletionRestrict_comp_awayCompletionHom]
    exact le_comap_awayCompletionHom I g
  rw [basicOpenChartRestrict, basicOpenChart, basicOpenChart,
    ← locallyRingedSpaceMap_comp I (awayCompletionIdeal I f) (awayCompletionIdeal I g)
      (awayCompletionHom I f) (awayCompletionRestrict I f g hI hle)
      (le_comap_awayCompletionHom I f) (le_comap_awayCompletionRestrict I f g hI hle) hIK]
  exact locallyRingedSpaceMap_congr _ _ _ _ _ _
    (awayCompletionRestrict_comp_awayCompletionHom I f g hI hle)

/-- **The identity law**: restricting `D(f)` to itself is the identity of its chart. `Spf` of
`FormalSpectrum.awayCompletionRestrict_self`. -/
theorem basicOpenChartRestrict_self (hI : I.FG) :
    basicOpenChartRestrict I f f hI le_rfl =
      𝟙 (locallyRingedSpaceObj (awayCompletionIdeal I f)) := by
  rw [basicOpenChartRestrict, locallyRingedSpaceMap_congr _ _ _ (RingHom.id _) _
      (Ideal.comap_id _).ge (awayCompletionRestrict_self I f hI), locallyRingedSpaceMap_id]

/-- **The chain law**: along `D(h) ≤ D(g) ≤ D(f)` the two chart inclusions compose to the one for
`D(h) ≤ D(f)`. `Spf` of `FormalSpectrum.awayCompletionRestrict_comp`, whose composition order is
the opposite one. -/
@[reassoc]
theorem basicOpenChartRestrict_comp {h : R} (hI : I.FG)
    (hgf : basicOpen I g ≤ basicOpen I f) (hhg : basicOpen I h ≤ basicOpen I g) :
    basicOpenChartRestrict I g h hI hhg ≫ basicOpenChartRestrict I f g hI hgf =
      basicOpenChartRestrict I f h hI (hhg.trans hgf) := by
  rw [basicOpenChartRestrict, basicOpenChartRestrict, basicOpenChartRestrict,
    ← locallyRingedSpaceMap_comp (awayCompletionIdeal I f) (awayCompletionIdeal I g)
      (awayCompletionIdeal I h) (awayCompletionRestrict I f g hI hgf)
      (awayCompletionRestrict I g h hI hhg) (le_comap_awayCompletionRestrict I f g hI hgf)
      (le_comap_awayCompletionRestrict I g h hI hhg)
      (by rw [awayCompletionRestrict_comp]
          exact le_comap_awayCompletionRestrict I f h hI (hhg.trans hgf))]
  exact locallyRingedSpaceMap_congr _ _ _ _ _ _ (awayCompletionRestrict_comp I f g hI hgf hhg)

/-- **The nested chart inclusion is a special case.** `FormalSpectrum.basicOpenChartFurtherLeft`
(`FormalSchemes.BasicOpenChartOverlapLegs`) is this chart inclusion at `g := f * g`, by
`FormalSpectrum.awayCompletionRestrict_eq_awayCompletionMulHomLeft`.

Its consumers are not rerouted onto the general form, and that file keeps it, because the leg
identifications `FormalSpectrum.basicOpenChartOverlapIso_hom_fst` / `_hom_snd` are stated in terms
of it. -/
theorem basicOpenChartFurtherLeft_eq_basicOpenChartRestrict (hI : I.FG)
    (hle : basicOpen I (f * g) ≤ basicOpen I f) :
    basicOpenChartFurtherLeft I f g hI = basicOpenChartRestrict I f (f * g) hI hle :=
  locallyRingedSpaceMap_congr _ _ _ _ _ _
    (awayCompletionRestrict_eq_awayCompletionMulHomLeft I f g hI hle)

/-- **A chart inclusion is itself an open immersion**, so `D(g)` is an open of the affine chart of
`D(f)`. Two out of three: the composite with `FormalSpectrum.basicOpenChart I f` is
`FormalSpectrum.basicOpenChart I g`, and both charts are open immersions
(`FormalSpectrum.isOpenImmersion_basicOpenChart`, `FormalSchemes.BasicOpenImmersionLRS`), so
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_comp` (`FormalSchemes.Gluing`) applies. -/
theorem isOpenImmersion_basicOpenChartRestrict (hI : I.FG)
    (hle : basicOpen I g ≤ basicOpen I f) :
    LocallyRingedSpace.IsOpenImmersion (basicOpenChartRestrict I f g hI hle) := by
  haveI : LocallyRingedSpace.IsOpenImmersion (basicOpenChart I f) :=
    isOpenImmersion_basicOpenChart I f hI
  haveI : LocallyRingedSpace.IsOpenImmersion
      (basicOpenChartRestrict I f g hI hle ≫ basicOpenChart I f) := by
    rw [basicOpenChartRestrict_comp_basicOpenChart]
    exact isOpenImmersion_basicOpenChart I g hI
  exact AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_comp _ (basicOpenChart I f)

/-- The applied form of `FormalSpectrum.basicOpenChartRestrict_comp_basicOpenChart` on points. It
is stated separately because `LocallyRingedSpace.comp_base`, although `rfl`, does not rewrite a
goal in which the base map has already been applied. -/
theorem base_basicOpenChartRestrict (hI : I.FG) (hle : basicOpen I g ≤ basicOpen I f)
    (z : FormalSpectrum (awayCompletionIdeal I g)) :
    (basicOpenChart I f).base ((basicOpenChartRestrict I f g hI hle).base z) =
      (basicOpenChart I g).base z := by
  conv_rhs => rw [← basicOpenChartRestrict_comp_basicOpenChart I f g hI hle]
  rfl

/-- **The range of a chart inclusion**: inside the chart at `f`, the chart at `g` is exactly the
preimage of `D(g)`. Both inclusions in the proof use that `(basicOpenChart I f).base` is injective,
together with `FormalSpectrum.range_basicOpenChart_base` at `g`. -/
theorem range_basicOpenChartRestrict_base (hI : I.FG)
    (hle : basicOpen I g ≤ basicOpen I f) :
    Set.range (basicOpenChartRestrict I f g hI hle).base =
      (basicOpenChart I f).base ⁻¹' (basicOpen I g : Set (FormalSpectrum I)) := by
  have hinj : Function.Injective ⇑(basicOpenChart I f).base :=
    (isOpenImmersion_basicOpenChart I f hI).base_open.injective
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    rw [Set.mem_preimage, base_basicOpenChartRestrict I f g hI hle z,
      ← range_basicOpenChart_base I g hI]
    exact ⟨z, rfl⟩
  · intro hy
    rw [Set.mem_preimage, ← range_basicOpenChart_base I g hI] at hy
    obtain ⟨z, hz⟩ := hy
    exact ⟨z, hinj ((base_basicOpenChartRestrict I f g hI hle z).trans hz)⟩

end FormalSpectrum
