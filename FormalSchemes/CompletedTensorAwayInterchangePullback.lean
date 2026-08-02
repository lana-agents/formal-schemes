import FormalSchemes.CompletedTensorAwayInterchangeSpf
import FormalSchemes.PullbackRangeLRS

set_option linter.style.header false
-- The interchange open immersions range over the nested localization/completion towers of the
-- completed tensor product, which are slow for the elaborator and the kernel; raise the budgets.
set_option linter.style.setOption false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The triple overlap of two interchange charts is again an affine interchange chart

Fix an adic base `(R, I)` with `I` finitely generated, an `R`-algebra `A`, an affine base change
`B`, and write `C = A ⊗̂_R B` for the completed tensor product. For an away element `g : A` the
*interchange open immersion* `CompletedTensorAwayInterchange.interchangeOpenImmersion I g hI`
(`FormalSchemes.CompletedTensorAwayInterchangeSpf`) realises the localise-then-tensor patch
`Spf((A{1/g}) ⊗̂_R B)` as the basic open `D(inl g) ⊆ Spf C`.

This file records that the **pullback** (triple overlap) of two such charts, cut out by away
elements `g₁, g₂ : A`, is again an affine interchange chart — the one at the *product* `g₁ · g₂`:

* `range_interchangeOpenImmersion_mul`: the range of the interchange chart at `g₁ · g₂` is the
  intersection of the ranges of the charts at `g₁` and `g₂`. This is the geometric shadow of
  `inl (g₁ g₂) = inl g₁ · inl g₂` (`inl` is a ring homomorphism) together with the basic-open
  product rule `D(a·b) = D(a) ∩ D(b)` (`FormalSpectrum.basicOpen_mul`).
* `interchangePullbackIso`: the resulting isomorphism `Spf((A{1/(g₁ g₂)}) ⊗̂_R B) ≅ pullback` of the
  two interchange charts, obtained from the range identity by the open-immersion universal property
  (`AlgebraicGeometry.pullbackIsoOfRangeEq`).

The two legs of the isomorphism down to the charts are the generic `pullbackIsoOfRangeEq_hom_fst`
/ `_hom_snd` (`FormalSchemes.PullbackIsoRangeLegs`) and `pullbackIsoOfRangeEq_hom_fst_comp`
/ `_hom_snd_comp` (`FormalSchemes.PullbackRangeLRS`).

This identifies the triple overlap of the general fibre product `X ×_{Spf R} Spf B` as an affine
chart — the input to constructing the geometric triple-overlap cocycle `t'`/`t_fac`/`cocycle` of
`AlgebraicGeometry.AffineChartedFibreDatum` from the algebra transition data alone (EGA I §10.7).

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum

namespace CompletedTensorAwayInterchange

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- **The range of the interchange chart at a product equals the intersection of the ranges.** For
away elements `g₁ g₂ : A`, the interchange open immersion at `g₁ · g₂` has range the intersection of
the ranges of the charts at `g₁` and `g₂`. Geometrically this is the basic-open
product rule `D(inl (g₁ g₂)) = D(inl g₁) ∩ D(inl g₂)` in `Spf(A ⊗̂_R B)`, using that `inl` is a ring
homomorphism (`inl (g₁ g₂) = inl g₁ · inl g₂`) and `FormalSpectrum.basicOpen_mul`. -/
theorem range_interchangeOpenImmersion_mul (g₁ g₂ : A) (hI : I.FG) :
    Set.range (interchangeOpenImmersion (B := B) I (g₁ * g₂) hI).base =
      Set.range (interchangeOpenImmersion (B := B) I g₁ hI).base ∩
        Set.range (interchangeOpenImmersion (B := B) I g₂ hI).base := by
  rw [range_interchangeOpenImmersion_base (B := B) I (g₁ * g₂) hI,
    range_interchangeOpenImmersion_base (B := B) I g₁ hI,
    range_interchangeOpenImmersion_base (B := B) I g₂ hI,
    map_mul (CompletedTensorProduct.inl R I A B) g₁ g₂,
    FormalSpectrum.basicOpen_mul]
  exact TopologicalSpace.Opens.coe_inf _ _

/-- **The triple overlap of two interchange charts is an affine interchange chart.** The pullback of
the interchange open immersions at `g₁` and `g₂` — the triple overlap of the two charts inside
`Spf(A ⊗̂_R B)` — is canonically isomorphic to the interchange chart `Spf((A{1/(g₁ g₂)}) ⊗̂_R B)` at
the product `g₁ · g₂`, compatibly with the maps down to `Spf(A ⊗̂_R B)`
(`pullbackIsoOfRangeEq_hom_fst` / `_hom_snd`). Built from `range_interchangeOpenImmersion_mul` by
the open-immersion universal property `AlgebraicGeometry.pullbackIsoOfRangeEq`. -/
def interchangePullbackIso (g₁ g₂ : A) (hI : I.FG) :
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I g₁ hI
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I g₂ hI
    (FormalSpectrum.locallyRingedSpaceObj
        (CompletedTensorProduct.idealOfDefinition R I
          (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) (g₁ * g₂)) B) ≅
      pullback (interchangeOpenImmersion (B := B) I g₁ hI)
        (interchangeOpenImmersion (B := B) I g₂ hI)) :=
  letI := isOpenImmersion_interchangeOpenImmersion (B := B) I g₁ hI
  letI := isOpenImmersion_interchangeOpenImmersion (B := B) I g₂ hI
  letI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g₁ * g₂) hI
  LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq
    (interchangeOpenImmersion (B := B) I g₁ hI)
    (interchangeOpenImmersion (B := B) I g₂ hI)
    (interchangeOpenImmersion (B := B) I (g₁ * g₂) hI)
    (range_interchangeOpenImmersion_mul I g₁ g₂ hI)

end CompletedTensorAwayInterchange
