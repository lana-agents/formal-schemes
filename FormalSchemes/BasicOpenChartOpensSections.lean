import FormalSchemes.AdicSectionsRestrictOpen
import FormalSchemes.AdicOnOpenSections
import FormalSchemes.AwayCompletionRestrictUnique

set_option linter.style.header false

/-!
# The basic-open chart realises the sections over its own range

`AlgebraicGeometry.FormalScheme.AffineChart.opensSectionsHom`
(`FormalSchemes.AdicSectionsRestrictOpen`) reads a section over an open `U` of a formal scheme on a
chart whose range is inside `U`. When the chart is a **basic-open chart of an affine patch** — the
only shape in which charts of a glued formal scheme are ever produced — that reading has a second,
completely different description: `FormalSpectrum.sectionsEquivOfEqBasicOpen`
(`FormalSchemes.AdicOnOpenSections`), which identifies `Γ (Spf R, D(f))` with `R{1/f}` by EGA I
10.1.4 and mentions no chart at all.

**The two agree.** That is this file, and it is what makes a bound stated at a chart of a glued
object checkable: the chart side is where the predicate lives, the `sectionsEquivOfEqBasicOpen` side
is where the tree's computations of section rings live, and nothing before this file connected them.

## The argument, which is a rigidity argument and not a computation

Both readings are ring **isomorphisms** `Γ (Spf R, U) ≃ R{1/f}` for `U = D(f)`, so their comparison
is an endomorphism `Φ` of `R{1/f}`, and `FormalSpectrum.awayCompletion_hom_ext`
(`FormalSchemes.AwayCompletionRestrictUnique`) says an endomorphism of `R{1/f}` that carries the
ideal of definition into itself and fixes the image of `R` is the identity. So the whole file is the
verification that `Φ` fixes the image of `R`, i.e. that the chart-side reading is a map **under
`R`**:

* `FormalSpectrum.comp_sectionsOpenHom_sectionsMapOfRangeSubset_basicOpenChart` is that
  verification. It is three naturality steps —
  `FormalSpectrum.comp_sectionsOpenHom` (a sheaf component commutes with the structural maps),
  `FormalSpectrum.globalSectionsMap_basicOpenChart` (`Γ ∘ Spf = id` at the chart) and
  `FormalSpectrum.comp_eqToHom_sectionsOpenHom` (the transport is absorbed) — closed by
  `FormalSpectrum.globalSectionsEquiv_comp_sectionsOpenHom_top`.
* The ideal condition is then free: the ideal of definition of `R{1/f}` is the extension of `I`
  along `FormalSpectrum.awayCompletionHom` (`FormalSpectrum.map_awayCompletionHom`), so any map
  under `R` carries it onto itself by `Ideal.map_map`.

**No level-by-level computation and no `AdicCompletion.evalₐ` chase happens here.** In particular
this file does not go through `FormalSpectrum.chartComponent`
(`FormalSchemes.BasicOpenImmersionSheaf`), which conjugates the same sheaf component by
`FormalSpectrum.sectionsBasicOpenEquiv` on **both** sides and is about a basic open `D(g) ⊆ D(f)`
strictly inside the chart's range; the statement here is at the range itself, where the target open
is `⊤` and the conjugation is by `FormalSpectrum.globalSectionsEquiv`.

## Main definitions and results

* `FormalSpectrum.globalSectionsEquiv_comp_sectionsOpenHom_top`: the structural map at `⊤` is
  inverse to `FormalSpectrum.globalSectionsEquiv`.
* `FormalSpectrum.comp_sectionsOpenHom_sectionsMapOfRangeSubset_basicOpenChart`: the chart-side
  reading is a map under `R`.
* `FormalSpectrum.globalSectionsEquiv_comp_sectionsMapOfRangeSubset_basicOpenChart`: **the
  identification.**
* `FormalSpectrum.sectionsEquivOfEqBasicOpen_trans`: two nested equalities of opens compose, so a
  reading obtained through an intermediate open is the reading through the composite.
* `AlgebraicGeometry.FormalScheme.AffineChart.ofPatchBasicOpen`: a basic-open chart of an affine
  patch, bundled as an `AlgebraicGeometry.FormalScheme.AffineChart` of the ambient.
* `AlgebraicGeometry.FormalScheme.AffineChart.opensSectionsHom_ofPatchBasicOpen`: **its
  chart-restriction is the patch's sheaf component followed by
  `FormalSpectrum.sectionsEquivOfEqBasicOpen`** — no chart, no `⊤` and no
  `AlgebraicGeometry.LocallyRingedSpace.sectionsMapOfRangeSubset` left on the right.

## What is *not* proved here

**Nothing here says that any bound holds at any chart.** The identification is an equality of ring
homomorphisms; whether an ideal is carried into an ideal along it is a separate question and is not
asked, let alone answered, in this file.

`AlgebraicGeometry.FormalScheme.AffineChart.opensSectionsHom_ofPatchBasicOpen` requires the
hypothesis `hU` that the patch's preimage of the open **is** the basic open the chart is taken at.
That is a strong hypothesis — it says the chart exhausts the patch's part of the open — and it is
not implied by the containment `Set.range (basicOpenChart J g ≫ p).base ⊆ U` that the chart
otherwise needs. Nothing here produces such a `hU`; a caller has to have one.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1.3, §10.1.4, §10.4.6.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.LocallyRingedSpace FormalSpectrum

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I] (f : R)

/-- **The structural map at `⊤` is inverse to the global-sections identification.**
`FormalSpectrum.sectionsOpenHom` restricts along `U ⊆ ⊤`; at `U = ⊤` that restriction is the
identity, because `Opens` is thin. -/
theorem globalSectionsEquiv_comp_sectionsOpenHom_top :
    (globalSectionsEquiv I).toRingHom.comp (sectionsOpenHom I ⊤) = RingHom.id R := by
  refine RingHom.ext fun r => ?_
  have hid : (homOfLE (le_top (a := (⊤ : Opens (FormalSpectrum I))))).op
      = 𝟙 (op (⊤ : Opens (FormalSpectrum I))) := Subsingleton.elim _ _
  simp only [sectionsOpenHom, RingHom.comp_apply]
  rw [hid]
  erw [CategoryTheory.Functor.map_id]
  exact (globalSectionsEquiv I).apply_symm_apply r

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Two nested equalities of opens compose.** Reading a section over `U₁` as an element of
`R{1/f}` by first transporting to `U₂` and then applying
`FormalSpectrum.sectionsEquivOfEqBasicOpen` is the same as applying it along the composite
equality. Both sides are one presheaf transport followed by
`FormalSpectrum.sectionsBasicOpenEquiv`, and `CategoryTheory.eqToHom_trans` merges the two
transports. -/
theorem sectionsEquivOfEqBasicOpen_trans {U₁ U₂ : Opens (FormalSpectrum I)}
    (h : U₁ = U₂) (hU : U₂ = basicOpen I f)
    (s : ((structureSheaf I).presheaf.obj (op U₁) : Type u)) :
    sectionsEquivOfEqBasicOpen I (h.trans hU) s
      = sectionsEquivOfEqBasicOpen I hU
          (((structureSheaf I).presheaf.map (eqToHom (congrArg op h))).hom s) := by
  subst h
  have hs : (((structureSheaf I).presheaf.map
      (eqToHom (congrArg op (rfl : U₁ = U₁)))).hom) s = s := by
    simp only [eqToHom_refl]
    erw [CategoryTheory.Functor.map_id]
    rfl
  rw [hs]

variable [IsAdicRing (awayCompletionIdeal I f)]

set_option backward.isDefEq.respectTransparency false in
/-- **The chart-side reading of a section over `U` is a ring map under `R`.** The composite of the
structural map `R → Γ (Spf R, U)` with "restrict along the basic-open chart and read as a global
section" is the structural map `R → R{1/f}`.

This is the only hypothesis of the rigidity principle that has to be checked; see this file's
module docstring for why the other one is free. -/
theorem comp_sectionsOpenHom_sectionsMapOfRangeSubset_basicOpenChart
    {U : Opens (FormalSpectrum I)}
    (h : Set.range (basicOpenChart I f).base ⊆ (U : Set (FormalSpectrum I))) :
    ((globalSectionsEquiv (awayCompletionIdeal I f)).toRingHom.comp
        (sectionsMapOfRangeSubset (basicOpenChart I f) U h).hom).comp (sectionsOpenHom I U)
      = awayCompletionHom I f := by
  have h₀ := opens_map_obj_eq_top_of_range_subset (basicOpenChart I f) U h
  have hmap : ((locallyRingedSpaceObj (awayCompletionIdeal I f)).presheaf.map
        (eqToHom h₀.symm).op).hom
      = ((structureSheaf (awayCompletionIdeal I f)).presheaf.map
        (eqToHom (congrArg op h₀))).hom := by
    rw [show (eqToHom h₀.symm).op = eqToHom (congrArg op h₀) by simp only [eqToHom_op]]
    rfl
  have key : ((globalSectionsEquiv (awayCompletionIdeal I f)).toRingHom.comp
        ((locallyRingedSpaceObj (awayCompletionIdeal I f)).presheaf.map
          (eqToHom h₀.symm).op).hom).comp
        (sectionsOpenHom (awayCompletionIdeal I f)
          ((Opens.map (basicOpenChart I f).base).obj U))
      = RingHom.id (awayCompletion I f) := by
    rw [RingHom.comp_assoc, hmap, comp_eqToHom_sectionsOpenHom (awayCompletionIdeal I f) h₀,
      globalSectionsEquiv_comp_sectionsOpenHom_top]
  rw [sectionsMapOfRangeSubset, CommRingCat.hom_comp, RingHom.comp_assoc, RingHom.comp_assoc,
    comp_sectionsOpenHom, globalSectionsMap_basicOpenChart, ← RingHom.comp_assoc,
    ← RingHom.comp_assoc, key, RingHom.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- **The identification.** Restricting a section over an open `U = D(f)` along the basic-open chart
and reading the result as a global section of `Spf R{1/f}` is
`FormalSpectrum.sectionsEquivOfEqBasicOpen`, the EGA I 10.1.4 reading of the same section.

The comparison is an endomorphism of `R{1/f}`; it is under `R` by
`FormalSpectrum.comp_sectionsOpenHom_sectionsMapOfRangeSubset_basicOpenChart`, hence carries the
ideal of definition into itself by `FormalSpectrum.map_awayCompletionHom` and `Ideal.map_map`,
hence is the identity by `FormalSpectrum.awayCompletion_hom_ext`. -/
theorem globalSectionsEquiv_comp_sectionsMapOfRangeSubset_basicOpenChart (hI : I.FG)
    {U : Opens (FormalSpectrum I)} (hU : U = basicOpen I f)
    (h : Set.range (basicOpenChart I f).base ⊆ (U : Set (FormalSpectrum I))) :
    (globalSectionsEquiv (awayCompletionIdeal I f)).toRingHom.comp
        (sectionsMapOfRangeSubset (basicOpenChart I f) U h).hom
      = (sectionsEquivOfEqBasicOpen I hU).toRingHom := by
  have hE : (sectionsEquivOfEqBasicOpen I hU).symm.toRingHom.comp (awayCompletionHom I f)
      = sectionsOpenHom I U := by
    rw [← sectionsEquivOfEqBasicOpen_comp_sectionsOpenHom I hU, ← RingHom.comp_assoc,
      RingEquiv.symm_toRingHom_comp_toRingHom, RingHom.id_comp]
  set L := (globalSectionsEquiv (awayCompletionIdeal I f)).toRingHom.comp
    (sectionsMapOfRangeSubset (basicOpenChart I f) U h).hom with hL
  have hΦcomp : (L.comp (sectionsEquivOfEqBasicOpen I hU).symm.toRingHom).comp
      (awayCompletionHom I f) = awayCompletionHom I f := by
    rw [RingHom.comp_assoc, hE, hL]
    exact comp_sectionsOpenHom_sectionsMapOfRangeSubset_basicOpenChart I f h
  have hΦid : L.comp (sectionsEquivOfEqBasicOpen I hU).symm.toRingHom
      = RingHom.id (awayCompletion I f) := by
    refine awayCompletion_hom_ext I f f hI ?_ ?_ ?_
    · rw [← Ideal.map_le_iff_le_comap, ← map_awayCompletionHom I f, Ideal.map_map, hΦcomp,
        map_awayCompletionHom]
    · rw [Ideal.comap_id]
    · rw [hΦcomp, RingHom.id_comp]
  calc L = (L.comp (sectionsEquivOfEqBasicOpen I hU).symm.toRingHom).comp
        (sectionsEquivOfEqBasicOpen I hU).toRingHom := by
        rw [RingHom.comp_assoc, RingEquiv.symm_toRingHom_comp_toRingHom, RingHom.comp_id]
    _ = (sectionsEquivOfEqBasicOpen I hU).toRingHom := by rw [hΦid, RingHom.id_comp]

end FormalSpectrum

namespace AlgebraicGeometry.FormalScheme

variable {X : FormalScheme.{u}} {S : Type u} [CommRing S] [TopologicalSpace S]
variable (J : Ideal S) [IsAdicRing J] (g : S) [IsAdicRing (awayCompletionIdeal J g)]
variable (p : FormalSpectrum.locallyRingedSpaceObj J ⟶ X.toLocallyRingedSpace)

/-- **A basic-open chart of an affine patch, as a chart of the ambient.** The ring and the ideal of
definition are those of the basic open, and the morphism is the patch's inclusion after the
basic-open chart. The open-immersion field is an instance argument rather than a construction: for
a patch of a `AlgebraicGeometry.FormalScheme.GlueData` it is the composite of
`FormalSpectrum.isOpenImmersion_basicOpenChart` with
`AlgebraicGeometry.FormalScheme.GlueData.ι_isOpenImmersion`, and a caller that has a different
patch has to supply its own. -/
def AffineChart.ofPatchBasicOpen {x : X}
    [LocallyRingedSpace.IsOpenImmersion (FormalSpectrum.basicOpenChart J g ≫ p)]
    (hx : x ∈ Set.range (FormalSpectrum.basicOpenChart J g ≫ p).base) : AffineChart X x where
  R := awayCompletion J g
  I := awayCompletionIdeal J g
  map := FormalSpectrum.basicOpenChart J g ≫ p
  mem := hx

set_option backward.isDefEq.respectTransparency false in
/-- **The chart-restriction of a section over `V` at such a chart is the patch's sheaf component
followed by the EGA I 10.1.4 reading.** The chart, the `⊤` and the
`AlgebraicGeometry.LocallyRingedSpace.sectionsMapOfRangeSubset` all disappear from the right-hand
side; what is left is a `c`-component of the patch inclusion and an identification of section rings.

The hypothesis `hU` says the patch's preimage of `V` is exactly the basic open the chart is taken
at. It is what
`AlgebraicGeometry.LocallyRingedSpace.sectionsMapOfRangeSubset_comp_opens` needs in order to split
the composite at the patch inclusion, whose own range is *not* inside `V`. -/
theorem AffineChart.opensSectionsHom_ofPatchBasicOpen (hJ : J.FG) {x : X}
    [LocallyRingedSpace.IsOpenImmersion (FormalSpectrum.basicOpenChart J g ≫ p)]
    (hx : x ∈ Set.range (FormalSpectrum.basicOpenChart J g ≫ p).base) (V : Opens X)
    (hd : Set.range (FormalSpectrum.basicOpenChart J g ≫ p).base ⊆ (V : Set X))
    (hU : (Opens.map p.base).obj V = FormalSpectrum.basicOpen J g) :
    (AffineChart.ofPatchBasicOpen J g p hx).opensSectionsHom V hd
      = (FormalSpectrum.sectionsEquivOfEqBasicOpen J hU).toRingHom.comp
        ((p.c.app (op V)).hom) := by
  have hg : Set.range (FormalSpectrum.basicOpenChart J g).base ⊆
      SetLike.coe ((Opens.map p.base).obj V) := by
    rw [hU]
    exact (FormalSpectrum.range_basicOpenChart_base J g hJ).le
  rw [AffineChart.opensSectionsHom]
  change (globalSectionsEquiv (awayCompletionIdeal J g)).toRingHom.comp
      (LocallyRingedSpace.sectionsMapOfRangeSubset
        (FormalSpectrum.basicOpenChart J g ≫ p) V hd).hom = _
  rw [LocallyRingedSpace.sectionsMapOfRangeSubset_comp_opens _ _ _ hg hd,
    CommRingCat.hom_comp, ← RingHom.comp_assoc,
    FormalSpectrum.globalSectionsEquiv_comp_sectionsMapOfRangeSubset_basicOpenChart J g hJ hU hg]

end AlgebraicGeometry.FormalScheme

end
