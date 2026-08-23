import FormalSchemes.BothDatumFibreAdicOverBase
import FormalSchemes.GeneralFibreProductLiftAdic
import FormalSchemes.GeneralFibreProductLiftUniqueAdic

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The identity law of the general fibre product's universal property

`FormalSchemes.BothDatumFibreAdicOverBase` makes `X ×_{Spf R} Y` an admissible **source** for its
own universal property. The first thing that buys is the identity law: the mediating morphism of
the fibre product's own two projections is the identity.

```
fibreLiftAdic pr₁ pr₂ … = 𝟙 (X ×_{Spf R} Y)
```

Both halves of the universal property are needed and both are now hypothesis-free: existence is
`BothChartedFibreDatumXY.fibreLiftAdic` (issue 794), uniqueness is
`BothChartedFibreDatumXY.fibreLift_unique_adicOverBase` (issue 518), and the adic-over-base witness
they share is `adicOverBase_fibreStructMap`. Before that witness existed the statement could not be
phrased at all, not merely not proved.

## The proof

Uniqueness applied to the two competing morphisms `fibreLiftAdic pr₁ pr₂` and `𝟙`. Its three
hypotheses are:

* `hpr₁`, `hpr₂` — the lift's projection triangles `fibreLiftAdic_comp_pr₁`/`_comp_pr₂`, against
  `Category.id_comp` on the other side;
* `hstruct` — the same triangle reassociated: `m ≫ (pr₁ ≫ xStructMap) = (m ≫ pr₁) ≫ xStructMap`.

Note that `fibreLift_unique_adicOverBase` compares morphisms of **locally ringed spaces**, so the
right-hand side is `𝟙 D.generalFibreProduct.toLocallyRingedSpace` and not the `FormalScheme`
identity.

## What this is for

It is the first of the two facts behind "any two objects with this universal property are
canonically isomorphic": given a second presentation of the same `X` and `Y`, the two mediating
morphisms compose to endomorphisms satisfying exactly the hypotheses above, hence to identities.
That comparison is deliberately not attempted here — it needs a statement of what "the same `X` and
`Y`" means for two datums, which is its own scoping problem.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open CategoryTheory TopologicalSpace Topology FormalSpectrum
open CompletedTensorProduct

universe u

namespace AlgebraicGeometry.BothChartedFibreDatumXY

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable [TopologicalSpace R] [IsAdicRing I]
variable (D : BothChartedFibreDatumXY R I hI)

set_option backward.isDefEq.respectTransparency false in
/-- **The identity law of the general fibre product.** The mediating morphism of `X ×_{Spf R} Y`'s
own projections is the identity — the fibre product's universal property applied to itself. -/
theorem fibreLiftAdic_self
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
    D.fibreLiftAdic (D.pr₁ hV hf ht) (D.pr₂ hV hf ht) (D.pr₁ hV hf ht ≫ D.xStructMap)
        (D.adicOverBase_fibreStructMap hV hf ht) rfl hV hf ht (D.cone_comm hV hf ht) =
      𝟙 D.generalFibreProduct.toLocallyRingedSpace := by
  letI := D.commRingA
  letI := D.algebraA
  letI := D.commRingB
  letI := D.algebraB
  letI := D.topologyA
  letI := D.isAdicA
  letI := D.topologyB
  letI := D.isAdicB
  refine D.fibreLift_unique_adicOverBase hV hf ht _ _ (D.pr₁ hV hf ht ≫ D.xStructMap)
    (D.adicOverBase_fibreStructMap hV hf ht) ?_ ?_ ?_
  · rw [D.fibreLiftAdic_comp_pr₁, Category.id_comp]
  · rw [D.fibreLiftAdic_comp_pr₂, Category.id_comp]
  · rw [← Category.assoc, D.fibreLiftAdic_comp_pr₁]

end AlgebraicGeometry.BothChartedFibreDatumXY

end
