import FormalSchemes.TateSelfProductCocycle
import FormalSchemes.TwoPatchFibreProduct

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The four-chart Tate self-fibre-product `𝔈_q ×_{Spf R} 𝔈_q` as a glued formal scheme

Fix an adic base `R` with finitely generated ideal of definition `I` and a Tate parameter `q ∈ I`,
and let `A = R{x, y} / (x·y − q)` be the coordinate ring of the formal Tate annulus. The Tate curve
formal model `𝔈_q` is glued from two copies of `Spf A`; its self fibre product `𝔈_q ×_{Spf R} 𝔈_q`
is therefore glued from the `2×2 = 4` charts `Spf(A ⊗̂_R A)`, indexed by `Bool × Bool`.

This file assembles the full glue datum from the merged fields delivered by the earlier bricks
(`TateSelfProductGlueDatum`, `TateSelfProductGlueTPrime`, `TateSelfProductCocycle`), pushes it
through `CategoryTheory.GlueData.ofGlueData'` to a `LocallyRingedSpace.GlueData`, upgrades it to a
`FormalScheme.GlueData` (each of the four charts is the affine `Spf(A ⊗̂_R A)`), and forms the glued
object `tateSelfProduct : FormalScheme` — the fibre product `𝔈_q ×_{Spf R} 𝔈_q`.

Unlike the two-patch base change `TwoPatchFibreProductObject` (whose `Bool` index admits no
pairwise-distinct triple, so `t'`/`t_fac`/`cocycle` are vacuous), the `Bool × Bool` index here has
genuine pairwise-distinct triples; the transition-of-transitions `t' = tateSelfProductGlueT'`, its
compatibility `t_fac = tateSelfProductGlueT_fac`, and the genuine three-fold `cocycle =
tateSelfProductGlueCocycle` are supplied by the dedicated bricks.

The index `Bool × Bool` lives in `Type 0`, whereas a `GlueData' LocallyRingedSpace.{u}` needs its
index in `Type u`; we therefore glue over `ULift.{u} (Bool × Bool)` and pass through `ULift.down` to
the `Bool × Bool`-indexed fields, converting `i ≠ j` to `i.down ≠ j.down` via `uliftDownNe`.

## Main definitions

* `AlgebraicGeometry.tateSelfProductGlueData'`: the four-chart glue datum as a
  `CategoryTheory.GlueData' LocallyRingedSpace`.
* `AlgebraicGeometry.tateSelfProductLRSGlueData`, `...FormalGlueData`: the glue datum as a
  `LocallyRingedSpace.GlueData` (via `ofGlueData'` + `f_open`) and a `FormalScheme.GlueData`.
* `AlgebraicGeometry.tateSelfProduct`: the glued fibre product `𝔈_q ×_{Spf R} 𝔈_q`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
  CompletedTensorProduct

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- On the lifted index `ULift (Bool × Bool)`, distinctness descends to the underlying pairs: if
`i ≠ j` then `i.down ≠ j.down`. This converts the `ULift`-indexed distinctness hypotheses of the
`GlueData'` fields to the `Bool × Bool`-indexed hypotheses of the merged glue lemmas. -/
private theorem uliftDownNe {i j : ULift.{u} (Bool × Bool)} (h : i ≠ j) : i.down ≠ j.down := by
  intro e
  exact h (by rw [← ULift.up_down i, ← ULift.up_down j, e])

/-- The common chart `Spf(A ⊗̂_R A)`, the four patches to be glued (definitionally the codomain
`tateSelfProductGlueU` of the merged overlap charts). -/
private abbrev tspU : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj
    (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))

/-! ### The glue datum -/

/-- **The four-chart Tate self-fibre-product glue datum** as a `CategoryTheory.GlueData'` on
`ULift (Bool × Bool)`: four copies of `Spf(A ⊗̂_R A)` glued along the merged overlap charts
`tateSelfProductGlueF`, transitions `tateSelfProductGlueT`, transition-of-transitions
`tateSelfProductGlueT'`, its compatibility `tateSelfProductGlueT_fac`, and the genuine three-fold
`tateSelfProductGlueCocycle`. -/
def tateSelfProductGlueData' (hq : q ∈ I) (hI : I.FG) :
    CategoryTheory.GlueData' LocallyRingedSpace.{u} where
  J := ULift.{u} (Bool × Bool)
  U := fun _ => tspU R I q
  V := fun i j h => tateSelfProductGlueV R I q hI i.down j.down (uliftDownNe h)
  f := fun i j h => tateSelfProductGlueF R I q hI i.down j.down (uliftDownNe h)
  f_mono := fun i j h => tateSelfProductGlueF_mono R I q hq hI i.down j.down (uliftDownNe h)
  f_hasPullback := fun i j k hij hik =>
    tateSelfProductGlueF_hasPullback R I q hq hI i.down j.down k.down
      (uliftDownNe hij) (uliftDownNe hik)
  t := fun i j h => tateSelfProductGlueT R I q hI i.down j.down (uliftDownNe h)
  t' := fun i j k hij hik hjk => by
    haveI := tateSelfProductGlueF_isOpenImmersion R I q hq hI i.down j.down (uliftDownNe hij)
    haveI := tateSelfProductGlueF_isOpenImmersion R I q hq hI i.down k.down (uliftDownNe hik)
    haveI := tateSelfProductGlueF_isOpenImmersion R I q hq hI j.down k.down (uliftDownNe hjk)
    exact tateSelfProductGlueT' R I q hI i.down j.down k.down
      (uliftDownNe hij) (uliftDownNe hik) (uliftDownNe hjk)
  t_fac := fun i j k hij hik hjk => by
    haveI := tateSelfProductGlueF_isOpenImmersion R I q hq hI i.down j.down (uliftDownNe hij)
    haveI := tateSelfProductGlueF_isOpenImmersion R I q hq hI i.down k.down (uliftDownNe hik)
    haveI := tateSelfProductGlueF_isOpenImmersion R I q hq hI j.down k.down (uliftDownNe hjk)
    exact tateSelfProductGlueT_fac R I q hI i.down j.down k.down
      (uliftDownNe hij) (uliftDownNe hik) (uliftDownNe hjk)
  t_inv := fun i j h => tateSelfProductGlueT_inv R I q hI i.down j.down (uliftDownNe h)
  cocycle := fun i j k hij hik hjk => by
    haveI := tateSelfProductGlueF_isOpenImmersion R I q hq hI i.down j.down (uliftDownNe hij)
    haveI := tateSelfProductGlueF_isOpenImmersion R I q hq hI i.down k.down (uliftDownNe hik)
    haveI := tateSelfProductGlueF_isOpenImmersion R I q hq hI j.down k.down (uliftDownNe hjk)
    haveI := tateSelfProductGlueF_isOpenImmersion R I q hq hI j.down i.down (uliftDownNe hij).symm
    haveI := tateSelfProductGlueF_isOpenImmersion R I q hq hI k.down i.down (uliftDownNe hik).symm
    haveI := tateSelfProductGlueF_isOpenImmersion R I q hq hI k.down j.down (uliftDownNe hjk).symm
    exact tateSelfProductGlueCocycle R I q hq hI i.down j.down k.down
      (uliftDownNe hij) (uliftDownNe hik) (uliftDownNe hjk)

/-- **The four-chart Tate self-fibre-product glue datum as a `LocallyRingedSpace.GlueData`**, via
`GlueData.ofGlueData'` together with the open-immersion field `f_open`. Off the diagonal each glue
map is `eqToHom ≫ (overlap chart)`, a composite of an isomorphism with an open immersion; on the
diagonal it is `eqToHom`, an isomorphism. -/
def tateSelfProductLRSGlueData (hq : q ∈ I) (hI : I.FG) : LocallyRingedSpace.GlueData.{u} :=
  { CategoryTheory.GlueData.ofGlueData' (tateSelfProductGlueData' R I q hq hI) with
    f_open := by
      rintro i j
      simp only [CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f']
      split_ifs with h
      · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (eqToHom _))
      · haveI := tateSelfProductGlueF_isOpenImmersion R I q hq hI i.down j.down (uliftDownNe h)
        exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
          (eqToHom _ ≫ tateSelfProductGlueF R I q hI i.down j.down (uliftDownNe h))) }

/-- **The four-chart Tate self-fibre-product glue datum as a `FormalScheme.GlueData`**: each of the
four pieces is the affine formal scheme `Spf(A ⊗̂_R A)`, whose underlying locally ringed space is
definitionally the patch `locallyRingedSpaceObj (I·(A ⊗̂_R A))`. -/
def tateSelfProductFormalGlueData (hq : q ∈ I) (hI : I.FG) : FormalScheme.GlueData.{u} :=
  haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I (annulusAlgebra R I q) (annulusAlgebra R I q) hI
  { toLocallyRingedSpaceGlueData := tateSelfProductLRSGlueData R I q hq hI
    isFormalScheme := fun _ =>
      ⟨FormalScheme.Spf (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
          (annulusAlgebra R I q)),
        ⟨Iso.refl _⟩⟩ }

/-- **The four-chart Tate self-fibre product `𝔈_q ×_{Spf R} 𝔈_q`**: the (non-affine) formal scheme
obtained by gluing the four copies of the affine chart `Spf(A ⊗̂_R A)` along the merged Tate
self-product overlap charts and transitions. This is the fibre product of the Tate curve model
with itself over `Spf R`; issue 304 supplies its projections and cone identity. -/
def tateSelfProduct (hq : q ∈ I) (hI : I.FG) : FormalScheme.{u} :=
  (tateSelfProductFormalGlueData R I q hq hI).gluedFormalScheme

end AlgebraicGeometry
