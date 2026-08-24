import FormalSchemes.LocallyFG
import FormalSchemes.TateGlueTwoPatch
import FormalSchemes.AnnulusNontrivial

set_option linter.style.header false

/-!
# The two-patch Tate formal scheme is locally finitely generated

The companion of `FormalSchemes/CompletionLocallyFG.lean` on the Tate side. `tateTwoPatch`
(`FormalSchemes/TateGlueTwoPatch.lean`) glues two copies of `Spf A`, where
`A = R{x, y} / (x·y − q)` is the coordinate ring of the formal Tate annulus, along the overlap; over
a Noetherian base its ideal of definition `I·A` is adic (`annulus_isAdicRing`) and finitely
generated (`annulusIdealOfDefinition_fg`), so each patch is `LocallyFG` and
`FormalScheme.GlueData.gluedFormalScheme_locallyFG` transports that to the glued object.

This is a separate file from `FormalSchemes/CompletionLocallyFG.lean` because
`FormalSchemes.TateGlueTwoPatch` does not import `FormalSchemes.CompletionGlueTwoPatch` and should
not: the Tate chain and the completion chain are independent subtrees over
`FormalSchemes.Gluing`.

Unlike the completion side, the index is **not** split on: both patches of
`tateTwoPatchFormalGlueData` are literally the same object `FormalScheme.Spf (I·A)`, so a constant
function discharges the hypothesis.

## Why this is not vacuous

`LocallyFG` is a `∀ x, ∃ …` statement and so holds vacuously on an empty space.
`tateTwoPatch_nonempty` rules that out whenever the Tate parameter `q` lies in a proper ideal of
definition `I`, which is the standing situation of the Tate chain: the special fibre
`A ⧸ I·A = (R ⧸ I){x, y}/(x·y)` is then nontrivial (`annulus_nontrivial`), so the patch `Spf A` has
a point (`annulus_formalSpectrum_nonempty`) and its image under the `false` chart is a point of the
glued object.

## Main results

* `AlgebraicGeometry.tateTwoPatch_locallyFG`: the two-patch Tate formal scheme is `LocallyFG`.
* `AlgebraicGeometry.tateTwoPatch_nonempty`: it has points when `q ∈ I` and `I ≠ ⊤`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- **The two-patch Tate formal scheme is locally finitely generated.** Both patches are the same
affine formal scheme `Spf (I·A)`, whose ideal of definition is finitely generated over a Noetherian
base, so no case split on the index is needed. -/
theorem tateTwoPatch_locallyFG (hI : I.FG) [IsNoetherianRing R] :
    (tateTwoPatch R I q hI).LocallyFG :=
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  FormalScheme.GlueData.gluedFormalScheme_locallyFG _ (fun _ =>
    ⟨FormalScheme.Spf (annulusIdealOfDefinition R I q),
      FormalScheme.locallyFG_Spf (annulusIdealOfDefinition_fg R I q hI), ⟨Iso.refl _⟩⟩)

/-- **The two-patch Tate formal scheme has points** when the Tate parameter lies in a proper ideal
of definition: the special fibre of the annulus is then nontrivial, so `Spf (I·A)` has a point, and
the `false` chart of the glue datum carries it into the glued object. Together with
`tateTwoPatch_locallyFG` this rules out the vacuous reading of that statement. -/
theorem tateTwoPatch_nonempty (hI : I.FG) [IsNoetherianRing R] (hq : q ∈ I) (hIne : I ≠ ⊤) :
    Nonempty (tateTwoPatch R I q hI).toLocallyRingedSpace := by
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  obtain ⟨x⟩ := annulus_formalSpectrum_nonempty R I q hq hIne
  exact ⟨((tateTwoPatchFormalGlueData R I q hI).toLocallyRingedSpaceGlueData.toGlueData.ι
    ⟨false⟩).base x⟩

end AlgebraicGeometry
