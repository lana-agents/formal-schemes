import FormalSchemes.AffineFibreProductLRS
import FormalSchemes.BothDatumAdicOverBase
import FormalSchemes.GeneralFibreProductBothCone

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The general fibre product is adic over its own base

`FormalSchemes.BothDatumAdicOverBase` proves that the two glued *factors* `D.xGlued` and
`D.yGlued` of a two-sided fibre-product datum are adic over their structural morphisms. This file
proves the same statement for the *product* `D.generalFibreProduct = X ×_{Spf R} Y`, over the
structural morphism `pr₁ ≫ xStructMap`.

## Why this is the statement worth having

Since issues 794 and 518 the general fibre product has **both halves** of its universal property —
`BothChartedFibreDatumXY.fibreLiftAdic` (existence) and `fibreLift_unique_adicOverBase`
(uniqueness) — but each of them applies only to a source `Z` carrying a witness
`FormalScheme.AdicOverBaseLocallyFG Z s`. Until now the only such witnesses on master were the two
factors (`BothDatumAdicOverBase`), an affine `Spf L`
(`FormalSchemes.GeneralSeparatedChartCodiagonal`), and — for the Tate model alone —
`tateSelfProductInv_adicOverBase` (`FormalSchemes.TateSelfProductAdicOverBase`), which is this
file's theorem hand-built against one specific glue datum.

So the fibre product was not an admissible **source** for its own universal property, and none of
the statements that universal property exists for could even be phrased: the identity law
`fibreLiftAdic pr₁ pr₂ = 𝟙` (`FormalSchemes.GeneralFibreProductLiftAdicSelf`), uniqueness of the
fibre product up to canonical isomorphism, symmetry, associativity. This file supplies the missing
input, once, at an arbitrary datum.

## The argument

Every point of `D.generalFibreProduct` lies in the image of a glue inclusion
`ι p : Spf(A_{p.1} ⊗̂_R B_{p.2}) ⟶ X ×_{Spf R} Y` (`ι_jointly_surjective`), an open immersion whose
ideal of definition is finitely generated (`CompletedTensorProduct.idealOfDefinition_fg`). What has
to be checked is that `ι p ≫ (pr₁ ≫ xStructMap)` is adic on global sections, and by `ι_pr₁` and
`ι_xStructMap` that composite is the affine `pr₁ChartSelf p ≫ xStructMapChart p.1`. That map fuses
through `locallyRingedSpaceMap_comp` into `Spf` of `inl ∘ (R → A_{p.1}) = algebraMap R (A ⊗̂_R B)`
(`CompletedTensorProduct.inl_comp_baseMap`), which is adic by
`CompletedTensorProduct.algebraMap_isAdicHom`.

This is the *first-projection half* of `cone_identity_chart`
(`FormalSchemes.GeneralFibreProductBothCone`) named in its own right: that theorem proves the two
chart projections agree over `Spf R` by computing both composites, and here only the value of the
computation is wanted, not the agreement.

## Two things about the spelling

`inl_comp_baseMap` is stated at **variable** rings `A`, `B` rather than at the datum's charts
`D.A p.1`, `D.B p.2`. Instantiating first and proving the fused identity afterwards times out at
`isDefEq` even at 3200000 heartbeats; at variable rings the identical proof takes seconds and the
datum-level `pr₁ChartSelf_comp_xStructMapChart` is then a `letI`-wrapped application with no tactic
at all. This is the tree's standing rule — generalise the constant to a variable *before* the
equation, never after.

The composite continuity bound is supplied as `((IsAdicHom.of_map I).comp inl_isAdicHom).le_comap`
rather than as an inline `fun _ hx => …`. The lambda times out: its three implicit ideals have to
be solved against the expected type, whereas `IsAdicHom.comp` fixes them from its explicit
arguments first.

## Now redundant elsewhere

`tateSelfProductInv_adicOverBase` (`FormalSchemes.TateSelfProductAdicOverBase`) is this file's
`adicOverBase_fibreStructMap` for the Tate self-product's hand-built glue datum, and
`tensorIdealOfDefinition_fg` there is `CompletedTensorProduct.idealOfDefinition_fg`
(`FormalSchemes.AffineFibreProductLRS`) with `A` pinned to the annulus. Neither is retired here:
that is a deletion in the style of issues 805/812 and it touches the Tate tower.

## Main results

* `CompletedTensorProduct.inl_comp_baseMap`: the affine crux, at variable rings.
* `BothChartedFibreDatumXY.pr₁ChartSelf_comp_xStructMapChart`: it at the datum's charts.
* `BothChartedFibreDatumXY.adicOverBase_fibreStructMap`: **the theorem** —
  `AdicOverBaseLocallyFG D.generalFibreProduct (pr₁ ≫ xStructMap)`.
* `BothChartedFibreDatumXY.adicOverBase_fibreStructMap'`: the same in the `pr₂ ≫ yStructMap`
  spelling, free by `cone_comm`.
* `BothChartedFibreDatumXY.generalFibreProduct_locallyFG`: the `LocallyFG` corollary.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.12.
-/

noncomputable section

open CategoryTheory TopologicalSpace Topology FormalSpectrum
open AlgebraicGeometry CompletedTensorProduct

universe u

namespace CompletedTensorProduct

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The affine crux.** The left chart leg `Spf(A ⊗̂_R B) ⟶ Spf(I·A)` of the affine fibre product,
followed by the structural morphism `Spf(I·A) ⟶ Spf R` of `A`, is `Spf` of the algebra map
`R → A ⊗̂_R B`.

Both sides are `Spf` of a ring homomorphism, so this is `locallyRingedSpaceMap_comp` together with
`inl ∘ (R → A) = (R → A ⊗̂_R B)` (`AlgHom.comp_algebraMap`). Stated at variable `A`, `B`: at a
datum's charts the same computation does not elaborate (see the module docstring). -/
theorem inl_comp_baseMap :
    FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R A))
        (idealOfDefinition R I A B) (inl R I A B).toRingHom inl_isAdicHom.le_comap ≫
      FormalSpectrum.locallyRingedSpaceMap I (I.map (algebraMap R A))
        (algebraMap R A) Ideal.le_comap_map =
    FormalSpectrum.locallyRingedSpaceMap I (idealOfDefinition R I A B)
      (algebraMap R (CompletedTensorProduct R I A B)) algebraMap_isAdicHom.le_comap := by
  rw [← FormalSpectrum.locallyRingedSpaceMap_comp
    (I := I) (J := I.map (algebraMap R A)) (K := idealOfDefinition R I A B)
    (φ := algebraMap R A) (ψ := (inl R I A B).toRingHom)
    (hIJ := Ideal.le_comap_map) (hJK := inl_isAdicHom.le_comap)
    (hIK := ((IsAdicHom.of_map I (A := A)).comp inl_isAdicHom).le_comap)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _
    (AlgHom.comp_algebraMap (inl R I A B))

end CompletedTensorProduct

namespace AlgebraicGeometry

namespace BothChartedFibreDatumXY

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable [TopologicalSpace R] [IsAdicRing I]
variable (D : BothChartedFibreDatumXY R I hI)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The per-chart structural morphism of the fibre product is `Spf` of the algebra map.**
`inl_comp_baseMap` at the datum's charts `A_{p.1}`, `B_{p.2}`; no tactic is needed, only the
carried instances. -/
theorem pr₁ChartSelf_comp_xStructMapChart (p : D.JX × D.JY) :
    letI := D.commRingA
    letI := D.algebraA
    letI := D.commRingB
    letI := D.algebraB
    D.pr₁ChartSelf p ≫ D.xStructMapChart p.1 =
      FormalSpectrum.locallyRingedSpaceMap I
        (idealOfDefinition R I (D.A p.1) (D.B p.2))
        (algebraMap R (CompletedTensorProduct R I (D.A p.1) (D.B p.2)))
        algebraMap_isAdicHom.le_comap :=
  letI := D.commRingA
  letI := D.algebraA
  letI := D.commRingB
  letI := D.algebraB
  CompletedTensorProduct.inl_comp_baseMap I (D.A p.1) (D.B p.2)

set_option backward.isDefEq.respectTransparency false in
/-- **The general fibre product is adic over its own base.** Every point of `X ×_{Spf R} Y` lies in
a glue chart `Spf(A_{p.1} ⊗̂_R B_{p.2})`, an open immersion with finitely generated ideal of
definition, whose composite with `pr₁ ≫ xStructMap` is `Spf (algebraMap R (A ⊗̂_R B))` and hence
adic on global sections.

This is the hypothesis `hZadic` of both `fibreLiftAdic` (issue 794) and
`fibreLift_unique_adicOverBase` (issue 518) for `Z = X ×_{Spf R} Y`, so it is what makes the fibre
product an admissible source for its own universal property. -/
theorem adicOverBase_fibreStructMap
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm) :
    letI := D.commRingA
    letI := D.algebraA
    letI := D.commRingB
    letI := D.algebraB
    letI := D.topologyA
    letI := D.isAdicA
    letI := D.topologyB
    letI := D.isAdicB
    FormalScheme.AdicOverBaseLocallyFG D.generalFibreProduct
      (D.pr₁ hV hf ht ≫ D.xStructMap) := by
  letI := D.commRingA
  letI := D.algebraA
  letI := D.commRingB
  letI := D.algebraB
  letI := D.topologyA
  letI := D.isAdicA
  letI := D.topologyB
  letI := D.isAdicB
  intro x
  obtain ⟨p, y, hy⟩ := D.formalGlueData.ι_jointly_surjective x
  haveI : IsAdicRing (idealOfDefinition R I (D.A p.1) (D.B p.2)) :=
    CompletedTensorProduct.isAdicRing R I (D.A p.1) (D.B p.2) hI
  refine ⟨CompletedTensorProduct R I (D.A p.1) (D.B p.2), inferInstance, inferInstance,
    idealOfDefinition R I (D.A p.1) (D.B p.2), inferInstance,
    D.formalGlueData.ι p, CompletedTensorProduct.idealOfDefinition_fg hI, ⟨y, hy⟩,
    FormalScheme.GlueData.ι_isOpenImmersion _ p, ?_⟩
  have hmap : D.formalGlueData.ι p ≫ (D.pr₁ hV hf ht ≫ D.xStructMap) =
      FormalSpectrum.locallyRingedSpaceMap I
        (idealOfDefinition R I (D.A p.1) (D.B p.2))
        (algebraMap R (CompletedTensorProduct R I (D.A p.1) (D.B p.2)))
        algebraMap_isAdicHom.le_comap :=
    (Category.assoc _ _ _).symm.trans <|
      ((D.ι_pr₁ hV hf ht p) =≫ D.xStructMap).trans <|
        (Category.assoc _ _ _).trans <|
          (D.pr₁ChartSelf p ≫= D.ι_xStructMap p.1).trans
            (D.pr₁ChartSelf_comp_xStructMapChart p)
  rw [hmap, FormalSpectrum.globalSectionsMap_locallyRingedSpaceMap]
  exact algebraMap_isAdicHom.le_comap

/-- **The `Y`-side spelling of `adicOverBase_fibreStructMap`.** The two structural morphisms of the
fibre product agree (`cone_comm`), so a consumer holding its witness over `pr₂ ≫ yStructMap` need
not transport along an equality of morphisms into `Spf I`. -/
theorem adicOverBase_fibreStructMap'
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm) :
    letI := D.commRingA
    letI := D.algebraA
    letI := D.commRingB
    letI := D.algebraB
    letI := D.topologyA
    letI := D.isAdicA
    letI := D.topologyB
    letI := D.isAdicB
    FormalScheme.AdicOverBaseLocallyFG D.generalFibreProduct
      (D.pr₂ hV hf ht ≫ D.yStructMap) :=
  letI := D.commRingA
  letI := D.algebraA
  letI := D.commRingB
  letI := D.algebraB
  letI := D.topologyA
  letI := D.isAdicA
  letI := D.topologyB
  letI := D.isAdicB
  D.cone_comm hV hf ht ▸ D.adicOverBase_fibreStructMap hV hf ht

/-- **The general fibre product is locally of finite generation**, by dropping the adic-over-base
conjunct. This is the hypothesis `hZ` that several lemmas about a general source still take. -/
theorem generalFibreProduct_locallyFG
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm) :
    letI := D.commRingA
    letI := D.algebraA
    letI := D.commRingB
    letI := D.algebraB
    letI := D.topologyA
    letI := D.isAdicA
    letI := D.topologyB
    letI := D.isAdicB
    D.generalFibreProduct.LocallyFG :=
  letI := D.commRingA
  letI := D.algebraA
  letI := D.commRingB
  letI := D.algebraB
  letI := D.topologyA
  letI := D.isAdicA
  letI := D.topologyB
  letI := D.isAdicB
  (D.adicOverBase_fibreStructMap hV hf ht).locallyFG

end BothChartedFibreDatumXY

end AlgebraicGeometry

end
