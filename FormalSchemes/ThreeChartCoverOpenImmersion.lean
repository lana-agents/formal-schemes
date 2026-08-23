import FormalSchemes.ChartedDatumGlueOpenImmersion
import FormalSchemes.ThreeChartCoverToBase

set_option linter.style.header false

/-!
# The three-chart cover is an open formal subscheme of `Spf A` (EGA I §10.13, §10.15)

`FormalSchemes.ThreeChartCoverToBase` (issue 860) builds the morphism
`ThreeChartCover.gluedXToBase : gluedX ⟶ Spf A` and shows that each chart maps by an open immersion
with range the basic open `D(f_i)`. Its docstring is explicit that this leaves the two statements
carrying the geometry unproved: that the *glued* morphism is an open immersion, and that its range
is `D(f₀) ∪ D(f₁) ∪ D(f₂)`. This file proves both.

The consequence is the sentence the tree has been unable to write down: `gluedX` **is** an open
formal subscheme of `Spf A`, namely the union of the three basic opens.

## The one non-formal input

Everything topological is handled by the general criterion
`AffineChartedFibreDatumX.isOpenImmersion_glueChartMorphisms`
(`FormalSchemes.ChartedDatumGlueOpenImmersion`), which needs exactly one geometric fact about this
datum: *the charts meet in `Spf A` only along their glue overlap*,

```
D(f_i) ∩ D(f_j) ⊆ range (basicOpenChart (I·A_i) (g_ij) ≫ chartToBase i).
```

Here it is an equality, and it is the identity `D(f_i) ∩ D(f_j) = D(f_i · f_j)` in disguise: the
overlap element `g_ij` is the image of `f_i · f_j` in `A{1/f_i}`, so `D(g_ij)` is the preimage of
`D(f_i f_j)` under the chart (`FormalSpectrum.map_preimage_basicOpen`), and pushing it forward along
the chart's open embedding gives `D(f_i f_j) ∩ D(f_i) = D(f_i f_j)`. That this is an *equality*
rather than only the needed inclusion is why the three-chart datum is a genuine open cover of its
image and not merely a family of open immersions.

Without such a hypothesis the criterion is false — the line with two origins is glued from two
copies of `𝔸¹` whose images meet in more than the overlap accounts for — so this is where the
content sits, not in the topology.

## What is here and what is not

Delivered: the range, the open immersion, and the corollary that when the three basic opens cover
`Spf A` the cover map is an **isomorphism**, so `gluedX ≅ Spf A` in `FormalScheme`.

**Not** delivered: the identification of `gluedX` with an open formal subscheme *as an object* —
the tree has no construction of the open formal subscheme cut out by an open subset of a formal
scheme, only `basicOpenChart` for a single basic open. Consequently the chart-free restatements of
`gluedX_isSeparatedOverSpf` (`FormalSchemes.ThreeChartCoverSeparatedScheme`) and
`gluedX_isRelativelyTopFiniteType` (`FormalSchemes.ThreeChartCoverTopFiniteType`) are still out of
reach in general; they are reachable here only under the covering hypothesis, where the object in
question is `Spf A` itself. Building the open formal subscheme is the next issue.

## Main results

* `AlgebraicGeometry.ThreeChartCover.range_overlapChart_comp_chartToBase`: the charts meet exactly
  along the overlap — the one non-formal input.
* `AlgebraicGeometry.ThreeChartCover.range_gluedXToBase_base` and
  `range_gluedXToBase_base_sup`: **the range is `D(f₀) ∪ D(f₁) ∪ D(f₂)`**, as an indexed union and
  as a three-fold supremum of opens.
* `AlgebraicGeometry.ThreeChartCover.isOpenImmersion_gluedXToBase`: **the cover map is an open
  immersion.**
* `AlgebraicGeometry.ThreeChartCover.isIso_gluedXToBase` and
  `AlgebraicGeometry.ThreeChartCover.gluedXIsoSpf`: if the three basic opens cover `Spf A`, it is an
  isomorphism, and `gluedX ≅ Spf A`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6, §10.13, §10.15.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace ThreeChartCover

variable {R : Type u} [CommRing R] (I : Ideal R) [TopologicalSpace R] [IsAdicRing I]
variable {A : Type u} [CommRing A] [Algebra R A]
variable (f : ULift.{u} (Fin 3) → A)

/-! ### The charts meet exactly along their overlap -/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The overlap `D(g_ij)` of the `i`-th chart is the preimage of `D(f_i · f_j)` under
`chartToBase i`: the overlap element is the image of `f_i · f_j`, and the preimage of a basic open
along a morphism of formal spectra is the basic open at the image element
(`FormalSpectrum.map_preimage_basicOpen`). -/
theorem preimage_basicOpen_chartToBase (i j : ULift.{u} (Fin 3)) :
    (chartToBase I f i).base ⁻¹'
        (basicOpen (I.map (algebraMap R A)) (f i * f j) :
          Set (FormalSpectrum (I.map (algebraMap R A)))) =
      (basicOpen (I.map (algebraMap R (chartAlgebra I f i))) (overlapElt I f i j) :
        Set (FormalSpectrum (I.map (algebraMap R (chartAlgebra I f i))))) :=
  congrArg SetLike.coe
    (map_preimage_basicOpen (I.map (algebraMap R A))
      (I.map (algebraMap R (chartAlgebra I f i))) (algebraMap A (chartAlgebra I f i))
      (le_comap_chartToBase I f i) (f i * f j))

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The `i`-th and `j`-th charts meet in `Spf A` exactly along their glue overlap.** The range of
the overlap chart, pushed into `Spf A`, is `D(f_i · f_j) = D(f_i) ∩ D(f_j)`.

This is the geometric hypothesis of `isOpenImmersion_glueChartMorphisms`, and the only step of the
open-immersion proof that is not formal. It holds here as an equality; only `⊇` is used downstream.
Note that it needs no `i ≠ j`: at `i = j` it reads `D(f_i²) = D(f_i)`. -/
theorem range_overlapChart_comp_chartToBase (hI : I.FG) (i j : ULift.{u} (Fin 3)) :
    Set.range (basicOpenChart (I.map (algebraMap R (chartAlgebra I f i)))
          (overlapElt I f i j) ≫ chartToBase I f i).base =
      Set.range (chartToBase I f i).base ∩ Set.range (chartToBase I f j).base := by
  have hsub := fun x (hx : x ∈ (basicOpen (I.map (algebraMap R A)) (f i * f j) :
      Set (FormalSpectrum (I.map (algebraMap R A))))) =>
    (range_chartToBase_base I f hI i).ge (by rw [basicOpen_mul] at hx; exact hx.1)
  have hL : Set.range (basicOpenChart (I.map (algebraMap R (chartAlgebra I f i)))
        (overlapElt I f i j) ≫ chartToBase I f i).base =
      (basicOpen (I.map (algebraMap R A)) (f i * f j) :
        Set (FormalSpectrum (I.map (algebraMap R A)))) := by
    rw [LocallyRingedSpace.comp_base, TopCat.coe_comp, Set.range_comp,
      range_basicOpenChart_base _ _ (hI.map _), ← preimage_basicOpen_chartToBase I f i j,
      Set.image_preimage_eq_inter_range]
    exact Set.inter_eq_self_of_subset_left hsub
  rw [hL, range_chartToBase_base I f hI i, range_chartToBase_base I f hI j, basicOpen_mul]
  rfl

/-! ### The range of the cover map, and the open immersion -/

variable (B : Type u) [CommRing B] [Algebra R B]

/-- **The range of the cover map is the union of the three basic opens.** -/
theorem range_gluedXToBase_base (hI : I.FG) :
    Set.range (gluedXToBase I f B hI).base =
      ⋃ i, (FormalSpectrum.basicOpen (I.map (algebraMap R A)) (f i) :
        Set (FormalSpectrum (I.map (algebraMap R A)))) :=
  ((datumX I f B hI).range_glueChartMorphisms _ _).trans
    (Set.iUnion_congr fun i => range_chartToBase_base I f hI i)

/-- **The range of the cover map is `D(f₀) ∪ D(f₁) ∪ D(f₂)`**, spelled as a three-fold supremum of
opens rather than an indexed union over `ULift (Fin 3)`. -/
theorem range_gluedXToBase_base_sup (hI : I.FG) :
    Set.range (gluedXToBase I f B hI).base =
      ((basicOpen (I.map (algebraMap R A)) (f ⟨0⟩) ⊔
          basicOpen (I.map (algebraMap R A)) (f ⟨1⟩) ⊔
          basicOpen (I.map (algebraMap R A)) (f ⟨2⟩) :
            Opens (FormalSpectrum (I.map (algebraMap R A)))) :
        Set (FormalSpectrum (I.map (algebraMap R A)))) := by
  rw [range_gluedXToBase_base I f B hI]
  ext x
  simp only [Set.mem_iUnion, Opens.coe_sup, Set.mem_union, SetLike.mem_coe]
  constructor
  · rintro ⟨⟨i⟩, hi⟩
    fin_cases i
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hi)
    · exact Or.inr hi
  · rintro ((h | h) | h)
    exacts [⟨⟨0⟩, h⟩, ⟨⟨1⟩, h⟩, ⟨⟨2⟩, h⟩]

/-- **The three-chart cover maps to `Spf A` by an open immersion.** With
`range_gluedXToBase_base_sup` this says that `gluedX` is the open formal subscheme
`D(f₀) ∪ D(f₁) ∪ D(f₂)` of `Spf A`.

The charts are open immersions by `isOpenImmersion_chartToBase` (issue 860) and they meet only along
their overlaps by `range_overlapChart_comp_chartToBase`; the general criterion supplies the rest. -/
theorem isOpenImmersion_gluedXToBase (hI : I.FG) :
    LocallyRingedSpace.IsOpenImmersion (gluedXToBase I f B hI) :=
  (datumX I f B hI).isOpenImmersion_glueChartMorphisms _ _
    (fun i => isOpenImmersion_chartToBase I f hI i)
    (fun i j _ => (range_overlapChart_comp_chartToBase I f hI i j).ge)

/-! ### When the three basic opens cover -/

/-- **If the three basic opens cover `Spf A`, the cover map is an isomorphism.** An open immersion
whose range is everything is surjective on points, hence an isomorphism of locally ringed spaces
(`LocallyRingedSpace.IsOpenImmersion.to_iso`). -/
theorem isIso_gluedXToBase (hI : I.FG)
    (hcov : basicOpen (I.map (algebraMap R A)) (f ⟨0⟩) ⊔
      basicOpen (I.map (algebraMap R A)) (f ⟨1⟩) ⊔
      basicOpen (I.map (algebraMap R A)) (f ⟨2⟩) = ⊤) :
    IsIso (gluedXToBase I f B hI) := by
  haveI := isOpenImmersion_gluedXToBase I f B hI
  haveI : Epi (gluedXToBase I f B hI).base := by
    rw [TopCat.epi_iff_surjective, ← Set.range_eq_univ,
      range_gluedXToBase_base_sup I f B hI, hcov]
    exact Opens.coe_top
  exact LocallyRingedSpace.IsOpenImmersion.to_iso _

section Adic

variable [TopologicalSpace A] [IsAdicRing (I.map (algebraMap R A))]

/-- **If the three basic opens cover `Spf A`, then `gluedX ≅ Spf A` as formal schemes.** The
locally-ringed-space isomorphism `isIso_gluedXToBase` lifted along the fully faithful forgetful
functor, as in `oneChartXGluedIso`. -/
def gluedXIsoSpf (hI : I.FG)
    (hcov : basicOpen (I.map (algebraMap R A)) (f ⟨0⟩) ⊔
      basicOpen (I.map (algebraMap R A)) (f ⟨1⟩) ⊔
      basicOpen (I.map (algebraMap R A)) (f ⟨2⟩) = ⊤) :
    gluedX I f B hI ≅ FormalScheme.Spf (I.map (algebraMap R A)) :=
  letI hiso := isIso_gluedXToBase I f B hI hcov
  (Functor.FullyFaithful.ofFullyFaithful
    FormalScheme.forgetToLocallyRingedSpace).preimageIso
      (@asIso _ _ _ _ (gluedXToBase I f B hI) hiso)

end Adic

end ThreeChartCover

end AlgebraicGeometry

end
