import FormalSchemes.CofinalAdicRing
import FormalSchemes.CofinalSheafComparisonIso
import FormalSchemes.LargestIdealOfDefinition

set_option linter.style.header false

/-!
# Ideal-independence of `Spf`, the general (non-nested) case (EGA I, §10.3, goal 1)

`FormalSchemes/CofinalSheafComparisonIso.lean` (`FormalSpectrum.cofinalSpfIso`) produced the
isomorphism of locally ringed spaces `Spf_I R ≅ Spf_J R` for two ideals of definition `I ≤ J`
(the *nested* case). This file removes the nesting hypothesis: for **two arbitrary ideals of
definition** `I J : Ideal R` of the same adic ring, `Spf_I R` and `Spf_J R` are isomorphic. This
closes goal 1 of the structure-sheaf intertwining (EGA I §10.3) in full — `Spf R` depends only on
the topological ring `R`, not on the chosen ideal of definition.

## Route

Set `K := I * J`. Then `K ≤ I` and `K ≤ J` are both *nested* comparisons, so — once `K` is known to
be an ideal of definition — the two nested isomorphisms `cofinalSpfIso K I` and `cofinalSpfIso K J`
compose to `Spf_I R ≅ Spf_K R ≅ Spf_J R`.

The work is in exhibiting `K = I * J` as an ideal of definition (`IsAdicRing K`), and that is
`IsAdicRing.mul` (`FormalSchemes.CofinalAdicRing`), where the commutative algebra it needs already
lives: `K` is squeezed `I ^ (m+1) ≤ K ≤ I` between cofinal powers of `I`, so it carries the same
adic topology, and its completeness transfers from `I`'s. Nothing about that argument mentions
`Spf`, which is why it is stated there and only used here.

## Main definitions and results

* `FormalSpectrum.generalCofinalSpfIso`: the isomorphism `Spf_I R ≅ Spf_J R` for two arbitrary
  ideals of definition `I`, `J`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], §10.3.
* [The Stacks Project, Tag 0AHZ](https://stacks.math.columbia.edu/tag/0AHZ).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I J : Ideal R)
  [IsAdicRing I] [IsAdicRing J]

/-- **The formal spectra of two arbitrary ideals of definition are isomorphic** (EGA I, §10.3,
goal 1). For an adic ring `R` with two ideals of definition `I`, `J` (no nesting assumed), the
affine formal schemes `Spf_I R` and `Spf_J R` are isomorphic as locally ringed spaces: `Spf R`
depends only on the topological ring `R`, not on the chosen ideal of definition. The proof factors
through the product `K = I * J`, which is again an ideal of definition (`IsAdicRing.mul`) and is
nested below both `I` and `J`, so the merged nested isomorphism `cofinalSpfIso` applies twice. -/
def generalCofinalSpfIso (hI : I.FG) (hJ : J.FG) :
    locallyRingedSpaceObj I ≅ locallyRingedSpaceObj J :=
  haveI := IsAdicRing.mul I J
  (cofinalSpfIso (I * J) I Ideal.mul_le_right (hI.mul hJ) hI).symm ≪≫
    cofinalSpfIso (I * J) J Ideal.mul_le_left (hI.mul hJ) hJ

/-- **Existence form** of the ideal-independence isomorphism: for any two ideals of definition of an
adic ring, the two formal spectra are isomorphic. -/
theorem nonempty_cofinalSpfIso (hI : I.FG) (hJ : J.FG) :
    Nonempty (locallyRingedSpaceObj I ≅ locallyRingedSpaceObj J) :=
  ⟨generalCofinalSpfIso I J hI hJ⟩

end FormalSpectrum

end
