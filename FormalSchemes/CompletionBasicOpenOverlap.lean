import FormalSchemes.CompletionBasicOpen
import FormalSchemes.PullbackRangeLRS

set_option linter.style.header false

/-!
# The overlap of two affine basic-open formal completions (EGA I, 10.8)

For a commutative ring `R`, a finitely generated ideal `I`, and elements `f g : R`, the two
basic-open formal completions `Spf (R_f)^` and `Spf (R_g)^` sit inside the affine formal
completion `Spf R^ = formalCompletion R I` as open formal subschemes with ranges the basic opens
`D(f̂)` and `D(ĝ)` (merged `basicOpenImmersion` / `range_basicOpenImmersion`). Their
**overlap** is the basic open `D(f̂) ∩ D(ĝ) = D(f̂·ĝ) = D((f·g)^)`, again a basic-open
completion `Spf (R_{fg})^`. This file records that overlap datum:

* `formalCompletion.range_basicOpenImmersion_inter`: the ranges intersect in the range of the
  basic-open immersion at the product, `im (bOI f) ∩ im (bOI g) = im (bOI (f·g))` — the
  set-theoretic core `D(f̂) ⊓ D(ĝ) = D(f̂ĝ)`.
* `formalCompletion.basicOpenOverlapIso`: the resulting identification of the overlap object
  `Spf (R_{fg})^` with the fibre product `pullback (bOI f) (bOI g)` of the two chart immersions,
  via the merged locally-ringed-space open-immersion pullback identification
  `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq`.
* `formalCompletion.basicOpenOverlapIso_hom_fst_comp` / `..._hom_snd_comp`: the two chart-inclusion
  compatibilities — the overlap identification followed by either projection and the corresponding
  chart immersion is the basic-open immersion at the product.

This is the affine-cover overlap-object datum a *separated* scheme's completion-gluing consumes: the
basic opens `D(f)` of an affine chart cover `Spf R^`, their pairwise overlaps `D(f) ∩ D(g) = D(fg)`
are again basic, and the overlap object identifies with the fibre product of the two chart
immersions — exactly the `V i j = pullback (fᵢ) (fⱼ)` datum of a `FormalScheme.GlueData` for the
completion. It is the completion analogue of the Tate self-product overlap identifications
(`TateSelfProductTripleOverlap.lean`, issue 237), reusing the same merged `pullbackIsoOfRangeEq`
API.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Limits

universe u

namespace formalCompletion

open FormalSpectrum AdicCompletion

variable {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) (f g : R)

/-- **The ranges of two basic-open completion immersions intersect in the range of the immersion at
the product**: `im (bOI f) ∩ im (bOI g) = im (bOI (f·g))`. On underlying spaces this is the
basic-open identity `D(f̂) ⊓ D(ĝ) = D(f̂ĝ)` in `Spf R^`, using the merged range computation
`range_basicOpenImmersion` and the multiplicativity of `awayPoint = algebraMap R R^`. -/
theorem range_basicOpenImmersion_inter :
    Set.range (basicOpenImmersion I hI f).toLRSHom.base ∩
        Set.range (basicOpenImmersion I hI g).toLRSHom.base =
      Set.range (basicOpenImmersion I hI (f * g)).toLRSHom.base := by
  rw [range_basicOpenImmersion, range_basicOpenImmersion, range_basicOpenImmersion,
    show awayPoint I (f * g) = awayPoint I f * awayPoint I g from
      map_mul (algebraMap R (AdicCompletion I R)) f g, basicOpen_mul, Opens.coe_inf]
  rfl

/-- **The overlap object of two basic-open completion charts is their fibre product.** The
basic-open completion `Spf (R_{fg})^` at the product `f·g`, whose range in `Spf R^` is
`D(f̂) ∩ D(ĝ)` (`range_basicOpenImmersion_inter`), identifies with the pullback of the two chart
immersions `bOI f`, `bOI g`, via the merged open-immersion pullback identification. -/
def basicOpenOverlapIso :
    (formalCompletion (Localization.Away (f * g))
          (I.map (algebraMap R (Localization.Away (f * g)))) (hI.map _)).toLocallyRingedSpace ≅
        pullback (basicOpenImmersion I hI f).toLRSHom (basicOpenImmersion I hI g).toLRSHom :=
  LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq
    (basicOpenImmersion I hI f).toLRSHom (basicOpenImmersion I hI g).toLRSHom
    (basicOpenImmersion I hI (f * g)).toLRSHom
    (range_basicOpenImmersion_inter I hI f g).symm

/-- The overlap identification is compatible with the first chart inclusion: mapping the overlap
object to the fibre product, projecting to the first factor, and including into `Spf R^` recovers
the basic-open immersion at the product. -/
@[reassoc]
theorem basicOpenOverlapIso_hom_fst_comp :
    (basicOpenOverlapIso I hI f g).hom ≫
        pullback.fst (basicOpenImmersion I hI f).toLRSHom (basicOpenImmersion I hI g).toLRSHom ≫
          (basicOpenImmersion I hI f).toLRSHom =
      (basicOpenImmersion I hI (f * g)).toLRSHom :=
  LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq_hom_fst_comp _ _ _ _

/-- The overlap identification is compatible with the second chart inclusion: mapping the overlap
object to the fibre product, projecting to the second factor, and including into `Spf R^` recovers
the basic-open immersion at the product. -/
@[reassoc]
theorem basicOpenOverlapIso_hom_snd_comp :
    (basicOpenOverlapIso I hI f g).hom ≫
        pullback.snd (basicOpenImmersion I hI f).toLRSHom (basicOpenImmersion I hI g).toLRSHom ≫
          (basicOpenImmersion I hI g).toLRSHom =
      (basicOpenImmersion I hI (f * g)).toLRSHom :=
  LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq_hom_snd_comp _ _ _ _

end formalCompletion
