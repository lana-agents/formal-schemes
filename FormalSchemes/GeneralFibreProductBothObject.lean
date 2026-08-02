import FormalSchemes.GeneralFibreProductAffineBase

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The two-sided general fibre product `X ×_{Spf R} Y` (both factors affine-charted)

Fix an adic base `(R, I)` with `I` finitely generated. Let `X` be a formal scheme glued from
**affine charts** `Spf A_i` (`i : JX`) over `Spf R`, and let `Y` be a formal scheme glued from
affine charts `Spf B_j` (`j : JY`) over `Spf R`, each with its own overlap away-elements and
`R`-algebra transition isomorphisms. This file assembles the fibre product `X ×_{Spf R} Y` as a
glued `FormalScheme` whose charts are the double completed tensor products
`Spf(A_i ⊗̂_R B_j)`, indexed by the product `JX × JY`.

## The carried-glue design

Unlike the one-sided template `AlgebraicGeometry.AffineChartedFibreDatum`
(`FormalSchemes.GeneralFibreProductAffineBase`), where the base is a *single* affine `Spf B` and the
overlap immersions are the *uniform* `interchangeOpenImmersion`s (so `f`/`t` are built concretely
from `interchangeOpenImmersion`/`mapSpfIso`), here the overlap of two product-index charts
`(i, j)`, `(i', j')` dispatches on which coordinate differs. The concrete interchange dispatch
is the sibling brick 329 (`ofAlgebraData`) and is *out of scope* here. Instead, this file **carries
the
whole geometric glue as data** over the concrete double-tensor charts
`Spf(A_i ⊗̂_R B_j)`: the overlap objects `V`, immersions `f` (with their open-immersion witnesses
`hf`), transitions `t`, the self-inverse law `t_inv`, and the triple-overlap datum `t'`/`t_fac`/
`cocycle`, all typed exactly against the fields of `CategoryTheory.GlueData'` on `JX × JY`.

`AlgebraicGeometry.BothChartedFibreDatum` also records, as *documentation of intent* feeding brick
329, the algebra-level data: the index types `JX`, `JY`, the chart algebras `A i`, `B j`, the
overlap away-elements `gX`, `gY`, and the `R`-algebra transitions `τX`, `τY` (with symmetries).

## The assembled fibre product

Mirroring the one-sided template we build, from a `BothChartedFibreDatum`:

* `BothChartedFibreDatum.glueData'`: the `CategoryTheory.GlueData'` on `LocallyRingedSpace` with
  index `JX × JY`, charts `Spf(A_i ⊗̂_R B_j)`, and the carried overlap datum;
* `BothChartedFibreDatum.lrsGlueData`, `...formalGlueData`: the glue datum as a
  `LocallyRingedSpace.GlueData` (via `GlueData.ofGlueData'` + `f_open`) and as a
  `FormalScheme.GlueData`;
* `BothChartedFibreDatum.generalFibreProduct`: the glued fibre product `X ×_{Spf R} Y`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace AlgebraicGeometry

/-! ### The two-sided affine-charted fibre-product input datum -/

set_option linter.unusedVariables false in
/-- **A two-sided affine-charted fibre-product datum over the adic base `(R, I)`.** It packages two
affine-charted glued formal schemes `X` (charts `Spf A_i`, `i : JX`) and `Y` (charts `Spf B_j`,
`j : JY`) over `Spf R`, together with the **carried geometric glue** of their fibre product
`X ×_{Spf R} Y` over the concrete double-tensor charts `Spf(A_i ⊗̂_R B_j)` (indexed by `JX × JY`).

It records, as algebra-level *documentation of intent* (feeding the concrete interchange dispatch of
brick 329):

* the index types `JX`, `JY` and the chart `R`-algebras `A i`, `B j`;
* the overlap away-elements `gX i i' : A i`, `gY j j' : B j`;
* the `R`-algebra transitions `τX`, `τY` between the two presentations of each overlap, with their
  symmetries `τX_symm`, `τY_symm`.

The *geometric* content is carried directly against the `CategoryTheory.GlueData'` fields on the
product index `JX × JY`, with charts
`U (p) = Spf(A_{p.1} ⊗̂_R B_{p.2})`: the overlap objects `V`, the open immersions `f` (with
witnesses `hf`), the transitions `t`, the self-inverse law `t_inv`, and the triple-overlap datum
`t'` together
with its laws `t_fac` and `cocycle`. -/
structure BothChartedFibreDatum (R : Type u) [CommRing R] (I : Ideal R) (hI : I.FG) where
  /-- The index type of the charts of `X`. -/
  JX : Type u
  /-- The index type of the charts of `Y`. -/
  JY : Type u
  /-- The chart `R`-algebra of the `i`-th affine chart `Spf (A i)` of `X`. -/
  A : JX → Type u
  /-- The chart `R`-algebra of the `j`-th affine chart `Spf (B j)` of `Y`. -/
  B : JY → Type u
  [commRingA : ∀ i, CommRing (A i)]
  [algebraA : ∀ i, Algebra R (A i)]
  [commRingB : ∀ j, CommRing (B j)]
  [algebraB : ∀ j, Algebra R (B j)]
  /-- The away element cutting out the overlap of the `i`-th chart of `X` with the `i'`-th. -/
  gX : ∀ (i i' : JX), A i
  /-- The away element cutting out the overlap of the `j`-th chart of `Y` with the `j'`-th. -/
  gY : ∀ (j j' : JY), B j
  /-- The `R`-algebra transition between the two presentations of the double overlap in `X`. -/
  τX : ∀ (i i' : JX), i ≠ i' →
    (awayCompletion (I.map (algebraMap R (A i))) (gX i i') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (A i'))) (gX i' i))
  /-- The `X`-transitions are mutually inverse: `τX i' i = (τX i i')⁻¹`. -/
  τX_symm : ∀ (i i' : JX) (h : i ≠ i'), τX i' i h.symm = (τX i i' h).symm
  /-- The `R`-algebra transition between the two presentations of the double overlap in `Y`. -/
  τY : ∀ (j j' : JY), j ≠ j' →
    (awayCompletion (I.map (algebraMap R (B j))) (gY j j') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (B j'))) (gY j' j))
  /-- The `Y`-transitions are mutually inverse: `τY j' j = (τY j j')⁻¹`. -/
  τY_symm : ∀ (j j' : JY) (h : j ≠ j'), τY j' j h.symm = (τY j j' h).symm
  /-- The overlap object of two distinct product-index charts of `X ×_{Spf R} Y`. -/
  V : ∀ (p p' : JX × JY), p ≠ p' → LocallyRingedSpace.{u}
  /-- The overlap immersion into the `p`-th product-index chart `Spf(A_{p.1} ⊗̂_R B_{p.2})`. -/
  f : ∀ (p p' : JX × JY) (h : p ≠ p'), V p p' h ⟶
    FormalSpectrum.locallyRingedSpaceObj
      (CompletedTensorProduct.idealOfDefinition R I (A p.1) (B p.2))
  /-- Each overlap immersion `f` is an open immersion. -/
  hf : ∀ (p p' : JX × JY) (h : p ≠ p'), LocallyRingedSpace.IsOpenImmersion (f p p' h)
  /-- The transition between the two overlap objects of a pair of distinct charts. -/
  t : ∀ (p p' : JX × JY) (h : p ≠ p'), V p p' h ⟶ V p' p h.symm
  /-- The transitions are mutually inverse. -/
  t_inv : ∀ (p p' : JX × JY) (h : p ≠ p'), t p p' h ≫ t p' p h.symm = 𝟙 _
  /-- The geometric triple-overlap transition of the fibre-product glue. -/
  t' : ∀ (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'') (hp'p'' : p' ≠ p''),
    letI := hf p p' hpp'
    letI := hf p p'' hpp''
    letI := hf p' p'' hp'p''
    letI := hf p' p hpp'.symm
    (pullback (f p p' hpp') (f p p'' hpp'') ⟶
      pullback (f p' p'' hp'p'') (f p' p hpp'.symm))
  /-- Compatibility of `t'` with the transition `t` (the `t_fac` law). -/
  t_fac : ∀ (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'') (hp'p'' : p' ≠ p''),
    letI := hf p p' hpp'
    letI := hf p p'' hpp''
    letI := hf p' p'' hp'p''
    letI := hf p' p hpp'.symm
    t' p p' p'' hpp' hpp'' hp'p'' ≫
        pullback.snd (f p' p'' hp'p'') (f p' p hpp'.symm) =
      pullback.fst (f p p' hpp') (f p p'' hpp'') ≫ t p p' hpp'
  /-- The triple cocycle of the fibre-product glue. -/
  cocycle : ∀ (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'') (hp'p'' : p' ≠ p''),
    letI := hf p p' hpp'
    letI := hf p p'' hpp''
    letI := hf p' p'' hp'p''
    letI := hf p' p hpp'.symm
    letI := hf p'' p hpp''.symm
    letI := hf p'' p' hp'p''.symm
    t' p p' p'' hpp' hpp'' hp'p'' ≫ t' p' p'' p hp'p'' hpp'.symm hpp''.symm ≫
      t' p'' p p' hpp''.symm hp'p''.symm hpp' = 𝟙 _

namespace BothChartedFibreDatum

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable (D : BothChartedFibreDatum R I hI)

/-- **The two-sided affine-charted fibre-product glue datum** as a `CategoryTheory.GlueData'` on
`D.JX × D.JY`: the `p`-th chart is `Spf(A_{p.1} ⊗̂_R B_{p.2})`, and the overlap data `V`, `f`, `t`,
`t'` and their laws are the carried geometric datum of `D`. -/
def glueData' : CategoryTheory.GlueData'.{u} LocallyRingedSpace :=
  letI := D.commRingA
  letI := D.algebraA
  letI := D.commRingB
  letI := D.algebraB
  { J := D.JX × D.JY
    U := fun p => locallyRingedSpaceObj
      (CompletedTensorProduct.idealOfDefinition R I (D.A p.1) (D.B p.2))
    V := D.V
    f := D.f
    f_mono := fun p p' h => by
      haveI := D.hf p p' h
      infer_instance
    f_hasPullback := fun p p' p'' hpp' hpp'' => by
      haveI := D.hf p p' hpp'
      haveI := D.hf p p'' hpp''
      infer_instance
    t := D.t
    t' := D.t'
    t_fac := D.t_fac
    t_inv := D.t_inv
    cocycle := D.cocycle }

/-- **The two-sided fibre-product glue datum as a `LocallyRingedSpace.GlueData`**, via
`GlueData.ofGlueData'` and the open-immersion field `f_open`. Off the diagonal each glue map is
`eqToHom ≫ (carried immersion)`; on the diagonal it is `eqToHom`. -/
def lrsGlueData : LocallyRingedSpace.GlueData.{u} :=
  letI := D.commRingA
  letI := D.algebraA
  letI := D.commRingB
  letI := D.algebraB
  { CategoryTheory.GlueData.ofGlueData' D.glueData' with
    f_open := by
      rintro p p'
      simp only [glueData', CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f']
      split_ifs with h
      · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (eqToHom _))
      · haveI := D.hf p p' h
        exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
          (eqToHom _ ≫ D.f p p' h)) }

/-- **The two-sided fibre-product glue datum as a `FormalScheme.GlueData`**: each chart is the
affine formal scheme `Spf(A_{p.1} ⊗̂_R B_{p.2})`. -/
def formalGlueData : FormalScheme.GlueData.{u} :=
  letI := D.commRingA
  letI := D.algebraA
  letI := D.commRingB
  letI := D.algebraB
  { toLocallyRingedSpaceGlueData := D.lrsGlueData
    isFormalScheme := fun p =>
      haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (D.A p.1) (D.B p.2)) :=
        CompletedTensorProduct.isAdicRing R I (D.A p.1) (D.B p.2) hI
      ⟨FormalScheme.Spf (CompletedTensorProduct.idealOfDefinition R I (D.A p.1) (D.B p.2)),
        ⟨Iso.refl _⟩⟩ }

/-- **The general fibre product `X ×_{Spf R} Y`** of two affine-charted glued formal schemes over
the affine adic base `Spf R`, as a glued formal scheme. -/
def generalFibreProduct : FormalScheme.{u} :=
  D.formalGlueData.gluedFormalScheme

end BothChartedFibreDatum

/-! ### Validation: a subsingleton-index witness

We exhibit a genuine `BothChartedFibreDatum` on a subsingleton product index `PUnit × PUnit`, so
that every off-diagonal field (`V`, `f`, `hf`, `t`, `t_inv`, `t'`, `t_fac`, `cocycle`) is discharged
vacuously from the impossibility of two distinct points. This proves the whole pipeline typechecks
end-to-end and yields a real `generalFibreProduct : FormalScheme`. -/

/-- **A subsingleton-index witness `BothChartedFibreDatum`.** On `JX = JY = PUnit` the product index
`PUnit × PUnit` is a subsingleton, so no two charts are distinct and all overlap data is vacuous.
The chart algebras are `R` itself. This witnesses that `BothChartedFibreDatum.generalFibreProduct`
is inhabited. -/
def punitBothDatum (R : Type u) [CommRing R] (I : Ideal R) (hI : I.FG) :
    BothChartedFibreDatum R I hI where
  JX := PUnit
  JY := PUnit
  A := fun _ => R
  B := fun _ => R
  gX := fun _ _ => 1
  gY := fun _ _ => 1
  τX := fun i i' h => (h (Subsingleton.elim i i')).elim
  τX_symm := fun i i' h => (h (Subsingleton.elim i i')).elim
  τY := fun j j' h => (h (Subsingleton.elim j j')).elim
  τY_symm := fun j j' h => (h (Subsingleton.elim j j')).elim
  V := fun p p' h => (h (Subsingleton.elim p p')).elim
  f := fun p p' h => (h (Subsingleton.elim p p')).elim
  hf := fun p p' h => (h (Subsingleton.elim p p')).elim
  t := fun p p' h => (h (Subsingleton.elim p p')).elim
  t_inv := fun p p' h => (h (Subsingleton.elim p p')).elim
  t' := fun p p' _ hpp' _ _ => (hpp' (Subsingleton.elim p p')).elim
  t_fac := fun p p' _ hpp' _ _ => (hpp' (Subsingleton.elim p p')).elim
  cocycle := fun p p' _ hpp' _ _ => (hpp' (Subsingleton.elim p p')).elim

end AlgebraicGeometry
