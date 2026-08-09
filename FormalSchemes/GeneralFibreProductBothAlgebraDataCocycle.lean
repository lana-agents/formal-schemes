import FormalSchemes.GeneralFibreProductBothAlgebraDataCocycleAux
import FormalSchemes.GeneralFibreProductBothAlgebraDataTPrimeFac

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.style.openClassical false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The cocycle law `bothAlgDataT'_cocycle` and the smart constructor `ofAlgebraData`

This file completes the two-sided smart constructor `BothChartedFibreDatum.ofAlgebraData`, the
analogue of the one-sided `AlgebraicGeometry.AffineChartedFibreDatum.ofAlgebraData`
(`FormalSchemes.GeneralFibreProductAlgebraData`). It proves the twelve *mixed* leaves of the
triple-overlap cocycle `bothAlgDataT'_cocycle` (the three same-shape leaves are in
`FormalSchemes.GeneralFibreProductBothAlgebraDataCocycleAux`), assembles the fifteen-leaf dispatch,
and packages everything into `ofAlgebraData`, validated on a subsingleton product index.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace AlgebraicGeometry

open scoped Classical

/-- **Conjugated-`mapSpf` collapse.** If the two underlying algebra endomorphisms are the identity,
the `Sp`-conjugated `mapSpf` is the identity. This packages the final collapse shared by every mixed
cocycle leaf: after telescoping the source isos and combining the three `mapSpf` into one, the goal is
of this shape, and the two per-factor `AlgHom` cocycle identities `hfA`/`hfB` discharge it. -/
theorem inv_mapSpf_hom_collapse {R : Type u} [CommRing R] {I : Ideal R} {D E : Type u}
    [CommRing D] [CommRing E] [Algebra R D] [Algebra R E] (hI : I.FG)
    {W : LocallyRingedSpace}
    (Sp : (haveI := isAdicRing R I D E hI;
      FormalSpectrum.locallyRingedSpaceObj (idealOfDefinition R I D E)) ≅ W)
    (fA : D →ₐ[R] D) (fB : E →ₐ[R] E)
    (hfA : fA = AlgHom.id R D) (hfB : fB = AlgHom.id R E) :
    haveI := isAdicRing R I D E hI
    Sp.inv ≫ CompletedTensorProduct.mapSpf hI fA fB ≫ Sp.hom = 𝟙 W := by
  haveI := isAdicRing R I D E hI
  rw [hfA, hfB, CompletedTensorProduct.mapSpf_id, Category.id_comp, Iso.inv_hom_id]

/-! ### Reduction of the transport equivalences along reflexive equalities -/

/-- `awayIdxTransA` along `rfl` is the identity equivalence. -/
theorem awayIdxTransA_refl {R : Type u} [CommRing R] {I : Ideal R} {JX : Type u}
    {A : JX → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] {i : JX}
    (g : ∀ x : JX, A x) :
    awayIdxTransA (I := I) (rfl : i = i) g = AlgEquiv.refl := rfl

/-- `awayIdxTransB` along `rfl` is the identity equivalence. -/
theorem awayIdxTransB_refl {R : Type u} [CommRing R] {I : Ideal R} {JY : Type u}
    {B : JY → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)] {j : JY}
    (g : ∀ y : JY, B y) :
    awayIdxTransB (I := I) (rfl : j = j) g = AlgEquiv.refl := rfl

/-- `awayCongrEltA` along a reflexive element equality is the identity equivalence. -/
theorem awayCongrEltA_refl {R : Type u} [CommRing R] {I : Ideal R} {JX : Type u}
    {A : JX → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] {i : JX} {g : A i}
    (h : g = g) : awayCongrEltA (I := I) h = AlgEquiv.refl := rfl

/-- `awayCongrEltB` along a reflexive element equality is the identity equivalence. -/
theorem awayCongrEltB_refl {R : Type u} [CommRing R] {I : Ideal R} {JY : Type u}
    {B : JY → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)] {j : JY} {g : B j}
    (h : g = g) : awayCongrEltB (I := I) h = AlgEquiv.refl := rfl

/-! ### Generic per-factor closers for mixed cocycle leaves with one degenerate coordinate

`cocycle_snd_fst_hfA`/`cocycle_snd_fst_hfB` close the two per-factor `AlgHom` cocycle identities
produced by a mixed leaf in which the first (resp. second) coordinate is degenerate. In the
degenerate factor the index transport `awayIdxTrans*` and the element congruences `awayCongrElt*`
reduce to the identity, and the two `τ`-transitions become mutually inverse (via `τ*_symm`) while
the two `awaySelfMul*` isomorphisms cancel; both facts are exposed by `subst`-ing the index and the
middle-element equalities. -/

/-- **`A`-factor closer, degenerate first coordinate.** With `i = i'`, the three-fold composite of
inverse algebra maps around the `A` factor is the identity. -/
theorem cocycle_snd_fst_hfA {R : Type u} [CommRing R] {I : Ideal R} {JX : Type u}
    {A : JX → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    (gX : ∀ i i' : JX, A i)
    (τX : ∀ (i i' : JX), i ≠ i' →
      awayCompletion (I.map (algebraMap R (A i))) (gX i i') ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A i'))) (gX i' i))
    (τX_symm : ∀ (i i' : JX) (h : i ≠ i'), τX i' i h.symm = (τX i i' h).symm)
    (hI : I.FG) {i i' k : JX} {h : i = i'} {hi'k : i' ≠ k} {hki : k ≠ i}
    {m : A k} {heq2 : gX k i' * gX k i' = m} {heq3 : m = gX k i * gX k i} :
    (awayIdxTransA h (fun x => gX x k)).symm.toAlgHom.comp
        (((τX i' k hi'k).trans
              ((awaySelfMulA hI (gX k i')).trans (awayCongrEltA heq2))).symm.toAlgHom.comp
          ((awayCongrEltA heq3).trans
              ((awaySelfMulA hI (gX k i)).symm.trans (τX k i hki))).symm.toAlgHom) =
      AlgHom.id R (awayCompletion (I.map (algebraMap R (A i))) (gX i k)) := by
  subst h
  subst heq2
  refine trans_cocycle_symm_comp _ _ _ ?_
  have hτ : τX k i hki = (τX i k hi'k).symm := τX_symm i k hi'k
  rw [hτ, awayIdxTransA_refl]
  ext x
  simp [awayCongrEltA_refl]

/-- **`B`-factor closer, degenerate second coordinate.** With `j = j''`, the three-fold composite of
inverse algebra maps around the `B` factor is the identity. -/
theorem cocycle_snd_fst_hfB {R : Type u} [CommRing R] {I : Ideal R} {JY : Type u}
    {B : JY → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
    (gY : ∀ j j' : JY, B j)
    (τY : ∀ (j j' : JY), j ≠ j' →
      awayCompletion (I.map (algebraMap R (B j))) (gY j j') ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (B j'))) (gY j' j))
    (τY_symm : ∀ (j j' : JY) (h : j ≠ j'), τY j' j h.symm = (τY j j' h).symm)
    (hI : I.FG) {j j' j'' : JY} {h : j'' = j} {hjj' : j ≠ j'} {hj'j'' : j' ≠ j''}
    {m : B j'} {heqB1 : gY j' j * gY j' j = m} {heqB2 : m = gY j' j'' * gY j' j''} :
    ((τY j j' hjj').trans
          ((awaySelfMulB hI (gY j' j)).trans (awayCongrEltB heqB1))).symm.toAlgHom.comp
        (((awayCongrEltB heqB2).trans
              ((awaySelfMulB hI (gY j' j'')).symm.trans (τY j' j'' hj'j''))).symm.toAlgHom.comp
          (awayIdxTransB h (fun y => gY y j')).symm.toAlgHom) =
      AlgHom.id R (awayCompletion (I.map (algebraMap R (B j))) (gY j j')) := by
  subst h
  subst heqB1
  refine trans_cocycle_symm_comp _ _ _ ?_
  have hτ : τY j' j'' hj'j'' = (τY j'' j' hjj').symm := τY_symm j'' j' hjj'
  rw [hτ, awayIdxTransB_refl]
  ext x
  simp [awayCongrEltB_refl]

/-- **`A`-factor closer, degenerate first coordinate, rotation `R1`.** Companion of
`cocycle_snd_fst_hfA` in which the index-transport factor sits in the *last* position; used by leaves
whose `A`-factor order is `[Fwd, Bwd, I]`. -/
theorem cocycle_fst_snd_hfA {R : Type u} [CommRing R] {I : Ideal R} {JX : Type u}
    {A : JX → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    (gX : ∀ i i' : JX, A i)
    (τX : ∀ (i i' : JX), i ≠ i' →
      awayCompletion (I.map (algebraMap R (A i))) (gX i i') ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A i'))) (gX i' i))
    (τX_symm : ∀ (i i' : JX) (h : i ≠ i'), τX i' i h.symm = (τX i i' h).symm)
    (hI : I.FG) {i i' i'' : JX} {h : i'' = i} {hii' : i ≠ i'} {hi'i'' : i' ≠ i''}
    {m : A i'} {heq1 : gX i' i * gX i' i = m} {heq2 : m = gX i' i'' * gX i' i''} :
    ((τX i i' hii').trans
          ((awaySelfMulA hI (gX i' i)).trans (awayCongrEltA heq1))).symm.toAlgHom.comp
        (((awayCongrEltA heq2).trans
              ((awaySelfMulA hI (gX i' i'')).symm.trans (τX i' i'' hi'i''))).symm.toAlgHom.comp
          (awayIdxTransA h (fun x => gX x i')).symm.toAlgHom) =
      AlgHom.id R (awayCompletion (I.map (algebraMap R (A i))) (gX i i')) := by
  subst h
  subst heq1
  refine trans_cocycle_symm_comp _ _ _ ?_
  have hτ : τX i' i'' hi'i'' = (τX i'' i' hii').symm := τX_symm i'' i' hii'
  rw [hτ, awayIdxTransA_refl]
  ext x
  simp [awayCongrEltA_refl]

/-- **`B`-factor closer, degenerate second coordinate, rotation `R0`.** Companion of
`cocycle_snd_fst_hfB` in which the index-transport factor sits in the *first* position (the exact
`B`-mirror of `cocycle_snd_fst_hfA`); used by leaves whose `B`-factor order is `[I, Fwd, Bwd]`. -/
theorem cocycle_fst_snd_hfB {R : Type u} [CommRing R] {I : Ideal R} {JY : Type u}
    {B : JY → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
    (gY : ∀ j j' : JY, B j)
    (τY : ∀ (j j' : JY), j ≠ j' →
      awayCompletion (I.map (algebraMap R (B j))) (gY j j') ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (B j'))) (gY j' j))
    (τY_symm : ∀ (j j' : JY) (h : j ≠ j'), τY j' j h.symm = (τY j j' h).symm)
    (hI : I.FG) {j j' k : JY} {h : j = j'} {hj'k : j' ≠ k} {hkj : k ≠ j}
    {m : B k} {heq2 : gY k j' * gY k j' = m} {heq3 : m = gY k j * gY k j} :
    (awayIdxTransB h (fun y => gY y k)).symm.toAlgHom.comp
        (((τY j' k hj'k).trans
              ((awaySelfMulB hI (gY k j')).trans (awayCongrEltB heq2))).symm.toAlgHom.comp
          ((awayCongrEltB heq3).trans
              ((awaySelfMulB hI (gY k j)).symm.trans (τY k j hkj))).symm.toAlgHom) =
      AlgHom.id R (awayCompletion (I.map (algebraMap R (B j))) (gY j k)) := by
  subst h
  subst heq2
  refine trans_cocycle_symm_comp _ _ _ ?_
  have hτ : τY k j hkj = (τY j k hj'k).symm := τY_symm j k hj'k
  rw [hτ, awayIdxTransB_refl]
  ext x
  simp [awayCongrEltB_refl]

/-- **`B`-factor closer, degenerate second-coordinate `both`-endpoint, rotation `R2`.** Here the
source `B`-element is the *product* `gY j j' * gY j j''` of the two Y-neighbours, but the two
neighbours coincide (`j' = j''`), so the self-multiply expansions cancel and the two `τ`-transitions
are mutually inverse. The index-transport factor sits in the *middle*; used by leaves whose
`B`-factor order is `[Bwd, I, Fwd]` at a `both`-edge endpoint. -/
theorem cocycle_snd_both_fst_hfB {R : Type u} [CommRing R] {I : Ideal R} {JY : Type u}
    {B : JY → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
    (gY : ∀ j j' : JY, B j)
    (τY : ∀ (j j' : JY), j ≠ j' →
      awayCompletion (I.map (algebraMap R (B j))) (gY j j') ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (B j'))) (gY j' j))
    (τY_symm : ∀ (j j' : JY) (h : j ≠ j'), τY j' j h.symm = (τY j j' h).symm)
    (hI : I.FG) {j j' j'' : JY} {h : j' = j''} {hjj' : j ≠ j'} {hj''j : j'' ≠ j}
    {heq1 : gY j j' * gY j j'' = gY j j' * gY j j'}
    {heq3 : gY j j'' * gY j j'' = gY j j' * gY j j''} :
    ((awayCongrEltB heq1).trans
          ((awaySelfMulB hI (gY j j')).symm.trans (τY j j' hjj'))).symm.toAlgHom.comp
        ((awayIdxTransB h (fun y => gY y j)).symm.toAlgHom.comp
          ((τY j'' j hj''j).trans
              ((awaySelfMulB hI (gY j j'')).trans (awayCongrEltB heq3))).symm.toAlgHom) =
      AlgHom.id R (awayCompletion (I.map (algebraMap R (B j))) (gY j j' * gY j j'')) := by
  subst h
  refine trans_cocycle_symm_comp _ _ _ ?_
  have hτ : τY j' j hj''j = (τY j j' hjj').symm := τY_symm j j' hjj'
  rw [hτ, awayIdxTransB_refl]
  ext x
  simp [awayCongrEltB_refl]

/-- **`A`-factor closer, degenerate first-coordinate `both`-endpoint, rotation `R2`.** The exact
`A`-mirror of `cocycle_snd_both_fst_hfB`: the source `A`-element is the product `gX i i' * gX i i''`
of the two X-neighbours, which coincide (`i' = i''`), so the composite collapses. -/
theorem cocycle_fst_both_snd_hfA {R : Type u} [CommRing R] {I : Ideal R} {JX : Type u}
    {A : JX → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    (gX : ∀ i i' : JX, A i)
    (τX : ∀ (i i' : JX), i ≠ i' →
      awayCompletion (I.map (algebraMap R (A i))) (gX i i') ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A i'))) (gX i' i))
    (τX_symm : ∀ (i i' : JX) (h : i ≠ i'), τX i' i h.symm = (τX i i' h).symm)
    (hI : I.FG) {i i' i'' : JX} {h : i' = i''} {hii' : i ≠ i'} {hi''i : i'' ≠ i}
    {heq1 : gX i i' * gX i i'' = gX i i' * gX i i'}
    {heq3 : gX i i'' * gX i i'' = gX i i' * gX i i''} :
    ((awayCongrEltA heq1).trans
          ((awaySelfMulA hI (gX i i')).symm.trans (τX i i' hii'))).symm.toAlgHom.comp
        ((awayIdxTransA h (fun x => gX x i)).symm.toAlgHom.comp
          ((τX i'' i hi''i).trans
              ((awaySelfMulA hI (gX i i'')).trans (awayCongrEltA heq3))).symm.toAlgHom) =
      AlgHom.id R (awayCompletion (I.map (algebraMap R (A i))) (gX i i' * gX i i'')) := by
  subst h
  refine trans_cocycle_symm_comp _ _ _ ?_
  have hτ : τX i' i hi''i = (τX i i' hii').symm := τX_symm i i' hii'
  rw [hτ, awayIdxTransA_refl]
  ext x
  simp [awayCongrEltA_refl]

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {JX JY : Type u}
variable {A : JX → Type u} {B : JY → Type u}
variable [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]

variable (gX : ∀ i i' : JX, A i) (gY : ∀ j j' : JY, B j)
variable
  (τX : ∀ (i i' : JX), i ≠ i' →
    (awayCompletion (I.map (algebraMap R (A i))) (gX i i') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (A i'))) (gX i' i)))
  (τY : ∀ (j j' : JY), j ≠ j' →
    (awayCompletion (I.map (algebraMap R (B j))) (gY j j') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (B j'))) (gY j' j)))
  (σX : ∀ (i i' i'' : JX), i ≠ i' → i ≠ i'' → i' ≠ i'' →
    (awayCompletion (I.map (algebraMap R (A i))) (gX i i' * gX i i'') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (A i'))) (gX i' i'' * gX i' i)))
  (σY : ∀ (j j' j'' : JY), j ≠ j' → j ≠ j'' → j' ≠ j'' →
    (awayCompletion (I.map (algebraMap R (B j))) (gY j j' * gY j j'') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (B j'))) (gY j' j'' * gY j' j)))
  (hσcX : ∀ (i i' i'' : JX) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
    (σX i i' i'' h1 h2 h3).trans ((σX i' i'' i h3 h1.symm h2.symm).trans
      (σX i'' i i' h2.symm h3.symm h1)) =
      AlgEquiv.refl (R := R)
        (A₁ := awayCompletion (I.map (algebraMap R (A i))) (gX i i' * gX i i'')))
  (hσcY : ∀ (j j' j'' : JY) (h1 : j ≠ j') (h2 : j ≠ j'') (h3 : j' ≠ j''),
    (σY j j' j'' h1 h2 h3).trans ((σY j' j'' j h3 h1.symm h2.symm).trans
      (σY j'' j j' h2.symm h3.symm h1)) =
      AlgEquiv.refl (R := R)
        (A₁ := awayCompletion (I.map (algebraMap R (B j))) (gY j j' * gY j j'')))
  (τX_symm : ∀ (i i' : JX) (h : i ≠ i'), τX i' i h.symm = (τX i i' h).symm)
  (τY_symm : ∀ (j j' : JY) (h : j ≠ j'), τY j' j h.symm = (τY j j' h).symm)
variable (hI : I.FG) (p p' p'' : JX × JY)
  (hpp' : p ≠ p') (hpp'' : p ≠ p'') (hp'p'' : p' ≠ p'')

include gX gY τX τY σX σY hI hpp' hpp'' hp'p''

/-! ### Mixed-shape cocycle leaves

Each leaf mirrors the same-shape leaves of `GeneralFibreProductBothAlgebraDataCocycleAux`: rewrite
the three cyclic `bothAlgDataT'_<leaf>` reductions, telescope the adjacent `SrcIso.hom ≫ SrcIso.inv`
by `Iso.hom_inv_id_assoc` (twice), then collapse the residual `M₁ ≫ M₂ ≫ M₃ = 𝟙` via `mapSpfIso_hom`
+ `mapSpf_comp₃`, feeding the two per-factor 3-fold `AlgHom` closers (`hA`/`hB`). -/

include τX_symm τY_symm in
/-- **Cocycle, mixed leaf `snd_fst`.** `(p,p')` differs in the second coordinate, `(p,p'')` in the
first. -/
theorem bothAlgDataT'_cocycle_snd_fst (h1' : p.1 = p'.1) (h1'' : p.1 ≠ p''.1) (h2'' : p.2 = p''.2) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    letI := bothAlgDataHf hI gX gY p' p'' hp'p''
    letI := bothAlgDataHf hI gX gY p' p hpp'.symm
    letI := bothAlgDataHf hI gX gY p'' p hpp''.symm
    letI := bothAlgDataHf hI gX gY p'' p' hp'p''.symm
    bothAlgDataT' hI gX gY τX τY σX σY p p' p'' hpp' hpp'' hp'p'' ≫
        bothAlgDataT' hI gX gY τX τY σX σY p' p'' p hp'p'' hpp'.symm hpp''.symm ≫
      bothAlgDataT' hI gX gY τX τY σX σY p'' p p' hpp''.symm hp'p''.symm hpp' = 𝟙 _ := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  haveI := bothAlgDataHf hI gX gY p' p'' hp'p''
  haveI := bothAlgDataHf hI gX gY p' p hpp'.symm
  haveI := bothAlgDataHf hI gX gY p'' p hpp''.symm
  haveI := bothAlgDataHf hI gX gY p'' p' hp'p''.symm
  have h2' : p.2 ≠ p'.2 := fun e => hpp' (Prod.ext h1' e)
  have h1t : p'.1 ≠ p''.1 := fun e => h1'' (h1'.trans e)
  have h2t : p'.2 ≠ p''.2 := fun e => h2' (h2''.trans e.symm)
  rw [bothAlgDataT'_snd_fst gX gY τX τY σX σY hI p p' p'' hpp' hpp'' hp'p'' h1' h1'' h2'',
    bothAlgDataT'_both_snd_fst gX gY τX τY σX σY hI p' p'' p hp'p'' hpp'.symm hpp''.symm
      h1t h2t h1'.symm h2''.symm,
    bothAlgDataT'_fst_both_snd gX gY τX τY σX σY hI p'' p p' hpp''.symm hp'p''.symm hpp'
      h1''.symm h2''.symm h1t.symm h2t.symm h1']
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc]
  simp only [mapSpfIso_hom]
  rw [← Category.assoc (mapSpf hI _ _), ← mapSpf_comp,
    ← Category.assoc (mapSpf hI _ _), ← mapSpf_comp]
  refine inv_mapSpf_hom_collapse hI _ _ _ ?hfA ?hfB
  case hfA =>
    rw [AlgHom.comp_assoc]
    exact cocycle_snd_fst_hfA gX τX τX_symm hI
  case hfB =>
    rw [AlgHom.comp_assoc]
    exact cocycle_snd_fst_hfB gY τY τY_symm hI

include τX_symm τY_symm in
/-- **Cocycle, mixed leaf `fst_snd`.** `(p,p')` differs in the first coordinate, `(p,p'')` in the
second. -/
theorem bothAlgDataT'_cocycle_fst_snd (h1' : p.1 ≠ p'.1) (h2' : p.2 = p'.2) (h1'' : p.1 = p''.1) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    letI := bothAlgDataHf hI gX gY p' p'' hp'p''
    letI := bothAlgDataHf hI gX gY p' p hpp'.symm
    letI := bothAlgDataHf hI gX gY p'' p hpp''.symm
    letI := bothAlgDataHf hI gX gY p'' p' hp'p''.symm
    bothAlgDataT' hI gX gY τX τY σX σY p p' p'' hpp' hpp'' hp'p'' ≫
        bothAlgDataT' hI gX gY τX τY σX σY p' p'' p hp'p'' hpp'.symm hpp''.symm ≫
      bothAlgDataT' hI gX gY τX τY σX σY p'' p p' hpp''.symm hp'p''.symm hpp' = 𝟙 _ := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  haveI := bothAlgDataHf hI gX gY p' p'' hp'p''
  haveI := bothAlgDataHf hI gX gY p' p hpp'.symm
  haveI := bothAlgDataHf hI gX gY p'' p hpp''.symm
  haveI := bothAlgDataHf hI gX gY p'' p' hp'p''.symm
  have h2'' : p.2 ≠ p''.2 := fun e => hpp'' (Prod.ext h1'' e)
  have h1t : p'.1 ≠ p''.1 := fun e => h1' (h1''.trans e.symm)
  have h2t : p'.2 ≠ p''.2 := fun e => h2'' (h2'.trans e)
  rw [bothAlgDataT'_fst_snd gX gY τX τY σX σY hI p p' p'' hpp' hpp'' hp'p'' h1' h2' h1'',
    bothAlgDataT'_both_fst_snd gX gY τX τY σX σY hI p' p'' p hp'p'' hpp'.symm hpp''.symm
      h1t h2t (fun e => h1' e.symm) h2'.symm h1''.symm,
    bothAlgDataT'_snd_both_fst gX gY τX τY σX σY hI p'' p p' hpp''.symm hp'p''.symm hpp'
      h1''.symm (fun e => h1t e.symm) (fun e => h2t e.symm) h2']
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc]
  simp only [mapSpfIso_hom]
  rw [← Category.assoc (mapSpf hI _ _), ← mapSpf_comp,
    ← Category.assoc (mapSpf hI _ _), ← mapSpf_comp]
  refine inv_mapSpf_hom_collapse hI _ _ _ ?hfA ?hfB
  case hfA =>
    rw [AlgHom.comp_assoc]
    exact cocycle_fst_snd_hfA gX τX τX_symm hI
  case hfB =>
    rw [AlgHom.comp_assoc]
    exact cocycle_fst_snd_hfB gY τY τY_symm hI

include τX_symm τY_symm in
/-- **Cocycle, mixed leaf `snd_both_fst`.** `(p,p')` differs in the second coordinate, `(p,p'')` in
both, `(p',p'')` in the first. -/
theorem bothAlgDataT'_cocycle_snd_both_fst (h1' : p.1 = p'.1) (h1'' : p.1 ≠ p''.1)
    (h2'' : p.2 ≠ p''.2) (h2t : p'.2 = p''.2) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    letI := bothAlgDataHf hI gX gY p' p'' hp'p''
    letI := bothAlgDataHf hI gX gY p' p hpp'.symm
    letI := bothAlgDataHf hI gX gY p'' p hpp''.symm
    letI := bothAlgDataHf hI gX gY p'' p' hp'p''.symm
    bothAlgDataT' hI gX gY τX τY σX σY p p' p'' hpp' hpp'' hp'p'' ≫
        bothAlgDataT' hI gX gY τX τY σX σY p' p'' p hp'p'' hpp'.symm hpp''.symm ≫
      bothAlgDataT' hI gX gY τX τY σX σY p'' p p' hpp''.symm hp'p''.symm hpp' = 𝟙 _ := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  haveI := bothAlgDataHf hI gX gY p' p'' hp'p''
  haveI := bothAlgDataHf hI gX gY p' p hpp'.symm
  haveI := bothAlgDataHf hI gX gY p'' p hpp''.symm
  haveI := bothAlgDataHf hI gX gY p'' p' hp'p''.symm
  have h2' : p.2 ≠ p'.2 := fun e => hpp' (Prod.ext h1' e)
  have h1t : p'.1 ≠ p''.1 := fun e => h1'' (h1'.trans e)
  rw [bothAlgDataT'_snd_both_fst gX gY τX τY σX σY hI p p' p'' hpp' hpp'' hp'p'' h1' h1'' h2'' h2t,
    bothAlgDataT'_fst_snd gX gY τX τY σX σY hI p' p'' p hp'p'' hpp'.symm hpp''.symm
      h1t h2t h1'.symm,
    bothAlgDataT'_both_fst_snd gX gY τX τY σX σY hI p'' p p' hpp''.symm hp'p''.symm hpp'
      (fun e => h1'' e.symm) (fun e => h2'' e.symm) (fun e => h1t e.symm) h2t.symm h1']
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc]
  simp only [mapSpfIso_hom]
  rw [← Category.assoc (mapSpf hI _ _), ← mapSpf_comp,
    ← Category.assoc (mapSpf hI _ _), ← mapSpf_comp]
  refine inv_mapSpf_hom_collapse hI _ _ _ ?hfA ?hfB
  case hfA =>
    rw [AlgHom.comp_assoc]
    exact cocycle_snd_fst_hfA gX τX τX_symm hI
  case hfB =>
    rw [AlgHom.comp_assoc]
    exact cocycle_snd_both_fst_hfB gY τY τY_symm hI

include τX_symm τY_symm in
/-- **Cocycle, mixed leaf `fst_both_snd`.** `(p,p')` differs in the first coordinate, `(p,p'')` in
both, `(p',p'')` in the second. -/
theorem bothAlgDataT'_cocycle_fst_both_snd (h1' : p.1 ≠ p'.1) (h2' : p.2 = p'.2) (h1'' : p.1 ≠ p''.1)
    (h2'' : p.2 ≠ p''.2) (h1t : p'.1 = p''.1) :
    letI := bothAlgDataHf hI gX gY p p' hpp'
    letI := bothAlgDataHf hI gX gY p p'' hpp''
    letI := bothAlgDataHf hI gX gY p' p'' hp'p''
    letI := bothAlgDataHf hI gX gY p' p hpp'.symm
    letI := bothAlgDataHf hI gX gY p'' p hpp''.symm
    letI := bothAlgDataHf hI gX gY p'' p' hp'p''.symm
    bothAlgDataT' hI gX gY τX τY σX σY p p' p'' hpp' hpp'' hp'p'' ≫
        bothAlgDataT' hI gX gY τX τY σX σY p' p'' p hp'p'' hpp'.symm hpp''.symm ≫
      bothAlgDataT' hI gX gY τX τY σX σY p'' p p' hpp''.symm hp'p''.symm hpp' = 𝟙 _ := by
  haveI := bothAlgDataHf hI gX gY p p' hpp'
  haveI := bothAlgDataHf hI gX gY p p'' hpp''
  haveI := bothAlgDataHf hI gX gY p' p'' hp'p''
  haveI := bothAlgDataHf hI gX gY p' p hpp'.symm
  haveI := bothAlgDataHf hI gX gY p'' p hpp''.symm
  haveI := bothAlgDataHf hI gX gY p'' p' hp'p''.symm
  have h2t : p'.2 ≠ p''.2 := fun e => h2'' (h2'.trans e)
  rw [bothAlgDataT'_fst_both_snd gX gY τX τY σX σY hI p p' p'' hpp' hpp'' hp'p''
      h1' h2' h1'' h2'' h1t,
    bothAlgDataT'_snd_fst gX gY τX τY σX σY hI p' p'' p hp'p'' hpp'.symm hpp''.symm
      h1t (fun e => h1' e.symm) h2'.symm,
    bothAlgDataT'_both_snd_fst gX gY τX τY σX σY hI p'' p p' hpp''.symm hp'p''.symm hpp'
      (fun e => h1'' e.symm) (fun e => h2'' e.symm) h1t.symm h2']
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc]
  simp only [mapSpfIso_hom]
  rw [← Category.assoc (mapSpf hI _ _), ← mapSpf_comp,
    ← Category.assoc (mapSpf hI _ _), ← mapSpf_comp]
  refine inv_mapSpf_hom_collapse hI _ _ _ ?hfA ?hfB
  case hfA =>
    rw [AlgHom.comp_assoc]
    exact cocycle_fst_both_snd_hfA gX τX τX_symm hI
  case hfB =>
    rw [AlgHom.comp_assoc]
    exact cocycle_fst_snd_hfB gY τY τY_symm hI

end AlgebraicGeometry
