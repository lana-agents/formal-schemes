import FormalSchemes.GeneralFibreProductBothObject
import FormalSchemes.CompletedTensorBaseChange

set_option linter.style.header false

/-!
# The base change of a general fibre product, glued from its charts

`FormalSchemes.CompletedTensorBaseChange` builds, for a tower `R → R'` with `I' = I·R'`, the
comparison `Spf (A ⊗̂_{R'} B) ⟶ Spf (A ⊗̂_R B)` and proves it a closed immersion. The charts of
`AlgebraicGeometry.BothChartedFibreDatum.generalFibreProduct` are exactly of that shape, one per
ordered pair of charts, so that comparison is the chart level of

```
X ×_{Spf I'} Y ⟶ X ×_{Spf I} Y
```

and what is missing is the assembly. This file does the assembly, and isolates what the assembly
costs.

## The obstacle, and why it is not the one the tree expected

For the one-sided `X` the base change moves only the *ideal* on each chart — the chart ring `A i`
is the same ring over `R` and over `R'` — and the glued object is literally **equal**
(`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_congr`,
`FormalSchemes.GeneralFibreProductExposeXIdealCongr`, and its tower form in
`FormalSchemes.AwayBaseChangeGluedX`). For the fibre product the base change moves the chart
**ring**: `A_i ⊗̂_R B_j` and `A_i ⊗̂_{R'} B_j` are different rings. So the `…OfIdeals` idiom of
that file — abstract the ideal family to a variable and `subst` — has nothing to abstract here,
there is no equality to state, and only a morphism can relate the two glued objects.

## What is assembled, and on what hypothesis

A morphism out of a glued formal scheme is a compatible family of chart morphisms
(`AlgebraicGeometry.FormalScheme.GlueData.glueMorphisms`, `FormalSchemes.GlueMorphisms`). The
compatibility is a square relating the chart comparison at `p` to the fibre product's transition
between the `p`-th and `p'`-th charts. **That square is an input here, not an output**, and it is
named: `AlgebraicGeometry.DoubleChartGlue.IsBaseChangeOverlapCompatible`. The reason is measured
rather than assumed and is recorded under *What is not proved here* below.

To state two fibre products over two bases at once, the chart family has to be a *parameter* and
not a field. `AlgebraicGeometry.BothChartedFibreDatum` carries `A` and `B` as fields, so two of
them over different bases share nothing that a statement can quantify over. This file therefore
repeats the carried geometric glue as `AlgebraicGeometry.DoubleChartGlue`, a structure over a
**fixed** chart family `A`, `B` and adic base `(R, I)`, and
`AlgebraicGeometry.BothChartedFibreDatum.generalFibreProduct_eq` says by `rfl` that nothing is
lost: the glued fibre product reads off a datum exactly its chart algebras and its eight geometric
fields, and none of `gX`, `gY`, `τX`, `τY`, which are documentation of intent there.

## Main definitions and results

* `CategoryTheory.GlueData.ofGlueData'_f_comp`: the overlap condition of an assembled
  `CategoryTheory.GlueData` has content only **off the diagonal**, so a caller owes the square only
  at `p ≠ p'`.
* `AlgebraicGeometry.FormalScheme.GlueData.mapGlued`: a morphism **between** two glued formal
  schemes from an index map and a compatible family of chart morphisms, with
  `AlgebraicGeometry.FormalScheme.GlueData.ι_mapGlued` and
  `AlgebraicGeometry.FormalScheme.GlueData.mapGlued_ext`.
* `AlgebraicGeometry.DoubleChartGlue`: the geometric glue of a two-sided fibre product over a fixed
  chart family, with `AlgebraicGeometry.DoubleChartGlue.fibreProduct` its glued object and
  `AlgebraicGeometry.DoubleChartGlue.ι` its chart immersions.
* `AlgebraicGeometry.BothChartedFibreDatum.toDoubleChartGlue` and
  `AlgebraicGeometry.BothChartedFibreDatum.generalFibreProduct_eq`: every datum's fibre product is
  one of these, by `rfl`.
* `AlgebraicGeometry.DoubleChartGlue.map`: a morphism of glued fibre products over two bases from a
  family of chart morphisms owed only at **distinct** pairs, with
  `AlgebraicGeometry.DoubleChartGlue.ι_map` and `AlgebraicGeometry.DoubleChartGlue.map_ext`.
* `AlgebraicGeometry.DoubleChartGlue.chartBaseChange`: the chart-level comparison, which is
  `CompletedTensorProduct.schemeBaseChange` underneath
  (`AlgebraicGeometry.DoubleChartGlue.chartBaseChange_eq_schemeBaseChange`), hence a closed
  immersion at every chart.
* `AlgebraicGeometry.DoubleChartGlue.IsBaseChangeOverlapCompatible`: **the square**.
* `AlgebraicGeometry.DoubleChartGlue.baseChange`: the glued comparison
  `X ×_{Spf I'} Y ⟶ X ×_{Spf I} Y`, with `AlgebraicGeometry.DoubleChartGlue.ι_baseChange` and
  `AlgebraicGeometry.DoubleChartGlue.baseChange_ext`.

## What is not proved here

* **The square is not discharged.**
  `AlgebraicGeometry.DoubleChartGlue.IsBaseChangeOverlapCompatible` is a hypothesis of
  `AlgebraicGeometry.DoubleChartGlue.baseChange`, and nothing here produces one at a general pair
  of glues. This is not a gap that a harder proof closes: at a general pair the two glues are
  *unrelated data*, and the square is then false as often as it is true. It becomes a theorem only
  for a pair produced by the smart constructor
  `AlgebraicGeometry.BothChartedFibreDatum.ofAlgebraData`, where the overlap objects are the
  three-branch interchange dispatch of `FormalSchemes.GeneralFibreProductBothAlgebraDataObject` —
  and discharging it there needs a base change of `FormalSpectrum.awayCompletion`, a commutation of
  `CompletedTensorProduct.baseChangeHom` with each of
  `CompletedTensorAwayInterchange.interchangeOpenImmersion`,
  `CompletedTensorAwayInterchange.rightInterchangeOpenImmersion` and
  `CompletedTensorAwayInterchange.bothInterchangeOpenImmersion`, and the agreement of the primed
  transitions with the unprimed ones, which is itself the step `FormalSchemes.AwayBaseChangeGluedX`
  records as unavailable on its own side.
* **No cancellation, and no separation statement.** Nothing here mentions
  `AlgebraicGeometry.BothChartedFibreDatumXY.IsSeparated` or
  `AlgebraicGeometry.FormalScheme.IsSeparatedOverSpf`, and nothing here says the glued comparison
  is injective, a closed immersion, or anything else beyond being a morphism restricting to
  `CompletedTensorProduct.schemeBaseChange` on each chart.
* **The general base is not available and is not an oversight.** Every statement below carries
  `I.map (algebraMap R R') = I'`, inherited from `CompletedTensorProduct.map_baseChangeHom`;
  `FormalSchemes.CompletedTensorBaseChange` records why, and `FormalSchemes.AdicOnSections` is the
  refutation it points at.

## Implementation notes

`CategoryTheory.GlueData.ofGlueData'_f_comp` is the general form of a bookkeeping step this tree
already does inline: the proof of `AlgebraicGeometry.AffineChartedFibreDatumX.glueChartMorphisms`
(`FormalSchemes.ChartedDatumGlueMorphisms`) is the same `by_cases`, the same `dif_neg` unfolding
and the same closing `rw`, specialised to one `CategoryTheory.GlueData'`. Stated generally it needs
one thing less: that proof has to re-type its disequalities in `¬ @Eq _ i j` form before `dif_neg`
will fire, because the `dite` conditions live at the `CategoryTheory.GlueData'.J` of the charted
datum's glue while `AlgebraicGeometry.FormalScheme.GlueData.glueMorphisms` indexes by the
`CategoryTheory.GlueData.J` of the assembled one, and the two agree only by unfolding. A lemma
stated at the former never meets the mismatch.

The general lemma is **not** moved down beside
`AlgebraicGeometry.FormalScheme.GlueData.glueMorphisms` in `FormalSchemes.GlueMorphisms`, whose
reverse closure is **275**, against this file's **0**. Rerouting
`AlgebraicGeometry.AffineChartedFibreDatumX.glueChartMorphisms` through it is a separate,
non-additive change to a module the fibre-product cluster sits above, and is worth its own row.

## Placement

A leaf over `FormalSchemes.GeneralFibreProductBothObject`, of forward closure **64**, and
`FormalSchemes.CompletedTensorBaseChange`, of forward closure **44**: forward closure **79**,
reverse closure **0**. `FormalSchemes.GlueMorphisms`, whose
`AlgebraicGeometry.FormalScheme.GlueData.glueMorphisms` this file consumes, is already inside the
first parent's closure, so the edge to it is free and it is not imported again.

The two parents are import-incomparable, so the statement costs either an import edge or a new
leaf, and the edge was rejected in both directions. Adding to
`FormalSchemes.GeneralFibreProductBothObject` puts the whole completed-tensor base change inside
the closure of a module whose reverse closure is **67**; adding to
`FormalSchemes.CompletedTensorBaseChange`, whose reverse closure is **1**, puts the entire
fibre-product cluster inside a module that is otherwise affine throughout. A leaf keeps both
parents at the cost they were landed at, and this file's own reverse closure is **0**, so nothing
pays for it. This is the disposition `FormalSchemes.AwayBaseChangeGluedX` reached, for the same
pair of reasons, on the one-sided side of the same question.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.15.
* [The Stacks Project, Tag 01HJ](https://stacks.math.columbia.edu/tag/01HJ).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open CompletedTensorProduct

universe v u

namespace CategoryTheory

open scoped Classical in
/-- **The overlap condition of an assembled glue datum has content only off the diagonal.**
`CategoryTheory.GlueData.ofGlueData'` sends the diagonal to an `eqToHom`, so the condition
`f i j ≫ k i = t i j ≫ f j i ≫ k j` that `AlgebraicGeometry.LocallyRingedSpace.GlueData.desc` asks
for at *every* pair follows from the same condition at pairs of **distinct** indices, which is the
only place a `CategoryTheory.GlueData'` carries data at all. -/
theorem GlueData.ofGlueData'_f_comp {C : Type u} [Category.{v} C] (D : GlueData'.{v} C)
    {Y : C} (k : ∀ i, D.U i ⟶ Y)
    (h : ∀ (i j : D.J) (hij : i ≠ j), D.f i j hij ≫ k i = D.t i j hij ≫ D.f j i hij.symm ≫ k j)
    (i j : D.J) :
    (GlueData.ofGlueData' D).f i j ≫ k i =
      (GlueData.ofGlueData' D).t i j ≫ (GlueData.ofGlueData' D).f j i ≫ k j := by
  by_cases hij : i = j
  · subst hij
    simp [GlueData.ofGlueData', GlueData'.f']
  · simp only [GlueData.ofGlueData', GlueData'.f', dif_neg hij, dif_neg (Ne.symm hij),
      Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [h i j hij]

end CategoryTheory

namespace AlgebraicGeometry

/-! ### A morphism between two glued formal schemes -/

namespace FormalScheme.GlueData

variable (G' G : FormalScheme.GlueData.{u})

/-- **A morphism between two glued formal schemes.** Given an index map `e` and a family of chart
morphisms `k i : U' i ⟶ U (e i)` whose composites with the target's chart immersions agree on the
source's overlaps, the induced morphism of glued formal schemes.

This is `AlgebraicGeometry.FormalScheme.GlueData.glueMorphisms` at the target
`(G.gluedFormalScheme).toLocallyRingedSpace`: a morphism *between* two glued objects is a morphism
*out of* the source into the glued target, and nothing more is needed. -/
def mapGlued (e : G'.toLocallyRingedSpaceGlueData.J → G.toLocallyRingedSpaceGlueData.J)
    (k : ∀ i, G'.toLocallyRingedSpaceGlueData.U i ⟶ G.toLocallyRingedSpaceGlueData.U (e i))
    (h : ∀ i j, G'.toLocallyRingedSpaceGlueData.toGlueData.f i j ≫ k i ≫ G.ι (e i) =
      G'.toLocallyRingedSpaceGlueData.toGlueData.t i j ≫
        G'.toLocallyRingedSpaceGlueData.toGlueData.f j i ≫ k j ≫ G.ι (e j)) :
    (G'.gluedFormalScheme).toLocallyRingedSpace ⟶ (G.gluedFormalScheme).toLocallyRingedSpace :=
  G'.glueMorphisms (fun i => k i ≫ G.ι (e i)) (by simpa only [Category.assoc] using h)

@[reassoc (attr := simp)]
theorem ι_mapGlued (e) (k) (h) (i) : G'.ι i ≫ G'.mapGlued G e k h = k i ≫ G.ι (e i) :=
  G'.ι_glueMorphisms _ _ i

/-- **Uniqueness**: a morphism of glued formal schemes restricting to `k i` on every chart is the
glued one. -/
theorem mapGlued_ext {e k h} {m : (G'.gluedFormalScheme).toLocallyRingedSpace ⟶
      (G.gluedFormalScheme).toLocallyRingedSpace}
    (hm : ∀ i, G'.ι i ≫ m = k i ≫ G.ι (e i)) : m = G'.mapGlued G e k h :=
  G'.hom_ext fun i => by rw [hm i, ι_mapGlued]

end FormalScheme.GlueData

/-! ### The two-sided fibre-product glue over a fixed chart family -/

variable {JX JY : Type u}
variable (R : Type u) [CommRing R] (I : Ideal R)
variable (A : JX → Type u) (B : JY → Type u)
variable [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]

/-- The `p`-th double-tensor chart `Spf (A_{p.1} ⊗̂_R B_{p.2})` as a locally ringed space. -/
abbrev doubleChartObj (p : JX × JY) : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I (A p.1) (B p.2))

/-- **The geometric glue of a two-sided fibre product over a fixed chart family.** These are
exactly the eight geometric fields of `AlgebraicGeometry.BothChartedFibreDatum`, with the chart
algebras `A`, `B` and the adic base `(R, I)` moved out of the structure and into its parameters.

That move is the whole reason the structure exists: a base change compares two fibre products over
*different* bases on the *same* charts, and a field cannot be shared between two structures.
`AlgebraicGeometry.BothChartedFibreDatum.generalFibreProduct_eq` shows nothing is lost. -/
structure DoubleChartGlue where
  /-- The overlap object of two distinct product-index charts. -/
  V : ∀ (p p' : JX × JY), p ≠ p' → LocallyRingedSpace.{u}
  /-- The overlap immersion into the `p`-th chart. -/
  f : ∀ (p p' : JX × JY) (h : p ≠ p'), V p p' h ⟶ doubleChartObj R I A B p
  /-- Each overlap immersion is an open immersion. -/
  hf : ∀ (p p' : JX × JY) (h : p ≠ p'), LocallyRingedSpace.IsOpenImmersion (f p p' h)
  /-- The transition between the two overlap objects of a pair of distinct charts. -/
  t : ∀ (p p' : JX × JY) (h : p ≠ p'), V p p' h ⟶ V p' p h.symm
  /-- The transitions are mutually inverse. -/
  t_inv : ∀ (p p' : JX × JY) (h : p ≠ p'), t p p' h ≫ t p' p h.symm = 𝟙 _
  /-- The geometric triple-overlap transition. -/
  t' : ∀ (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'') (hp'p'' : p' ≠ p''),
    letI := hf p p' hpp'
    letI := hf p p'' hpp''
    letI := hf p' p'' hp'p''
    letI := hf p' p hpp'.symm
    (pullback (f p p' hpp') (f p p'' hpp'') ⟶ pullback (f p' p'' hp'p'') (f p' p hpp'.symm))
  /-- Compatibility of `t'` with the transition `t`. -/
  t_fac : ∀ (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'') (hp'p'' : p' ≠ p''),
    letI := hf p p' hpp'
    letI := hf p p'' hpp''
    letI := hf p' p'' hp'p''
    letI := hf p' p hpp'.symm
    t' p p' p'' hpp' hpp'' hp'p'' ≫ pullback.snd (f p' p'' hp'p'') (f p' p hpp'.symm) =
      pullback.fst (f p p' hpp') (f p p'' hpp'') ≫ t p p' hpp'
  /-- The triple cocycle. -/
  cocycle : ∀ (p p' p'' : JX × JY) (hpp' : p ≠ p') (hpp'' : p ≠ p'') (hp'p'' : p' ≠ p''),
    letI := hf p p' hpp'
    letI := hf p p'' hpp''
    letI := hf p' p'' hp'p''
    letI := hf p' p hpp'.symm
    letI := hf p'' p hpp''.symm
    letI := hf p'' p' hp'p''.symm
    t' p p' p'' hpp' hpp'' hp'p'' ≫ t' p' p'' p hp'p'' hpp'.symm hpp''.symm ≫
      t' p'' p p' hpp''.symm hp'p''.symm hpp' = 𝟙 _

namespace DoubleChartGlue

variable {R I A B} (G : DoubleChartGlue R I A B)

/-- The `CategoryTheory.GlueData'` of a `AlgebraicGeometry.DoubleChartGlue`. -/
def glueData' : CategoryTheory.GlueData'.{u} LocallyRingedSpace where
  J := JX × JY
  U := doubleChartObj R I A B
  V := G.V
  f := G.f
  f_mono := fun p p' h => by
    haveI := G.hf p p' h
    infer_instance
  f_hasPullback := fun p p' p'' hpp' hpp'' => by
    haveI := G.hf p p' hpp'
    haveI := G.hf p p'' hpp''
    infer_instance
  t := G.t
  t' := G.t'
  t_fac := G.t_fac
  t_inv := G.t_inv
  cocycle := G.cocycle

/-- The `AlgebraicGeometry.LocallyRingedSpace.GlueData` of a `AlgebraicGeometry.DoubleChartGlue`.
Off the diagonal each glue map is `eqToHom ≫ (carried immersion)`; on the diagonal it is `eqToHom`.
-/
def lrsGlueData : LocallyRingedSpace.GlueData.{u} :=
  { CategoryTheory.GlueData.ofGlueData' G.glueData' with
    f_open := by
      rintro p p'
      simp only [glueData', CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f']
      split_ifs with h
      · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (eqToHom _))
      · haveI := G.hf p p' h
        exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (eqToHom _ ≫ G.f p p' h)) }

/-- The `AlgebraicGeometry.FormalScheme.GlueData` of a `AlgebraicGeometry.DoubleChartGlue`. -/
def formalGlueData (hI : I.FG) : FormalScheme.GlueData.{u} where
  toLocallyRingedSpaceGlueData := G.lrsGlueData
  isFormalScheme := fun p =>
    haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (A p.1) (B p.2)) :=
      CompletedTensorProduct.isAdicRing R I (A p.1) (B p.2) hI
    ⟨FormalScheme.Spf (CompletedTensorProduct.idealOfDefinition R I (A p.1) (B p.2)),
      ⟨Iso.refl _⟩⟩

/-- **The glued fibre product** of a `AlgebraicGeometry.DoubleChartGlue`. -/
def fibreProduct (hI : I.FG) : FormalScheme.{u} := (G.formalGlueData hI).gluedFormalScheme

/-- The open immersion of the `p`-th chart into the glued fibre product. -/
abbrev ι (hI : I.FG) (p : JX × JY) :
    doubleChartObj R I A B p ⟶ (G.fibreProduct hI).toLocallyRingedSpace :=
  (G.formalGlueData hI).ι p

/-! ### A morphism of glued fibre products -/

section Map

variable {R' : Type u} [CommRing R'] {I' : Ideal R'}
variable [∀ i, Algebra R' (A i)] [∀ j, Algebra R' (B j)]
variable (G' : DoubleChartGlue R' I' A B) (G : DoubleChartGlue R I A B)

/-- **A morphism of glued fibre products from a family of chart morphisms** that agree on the
overlaps of the source. The square is owed only at **distinct** pairs, by
`CategoryTheory.GlueData.ofGlueData'_f_comp`. -/
def map (hI' : I'.FG) (hI : I.FG)
    (k : ∀ p : JX × JY, doubleChartObj R' I' A B p ⟶ doubleChartObj R I A B p)
    (h : ∀ (p p' : JX × JY) (hne : p ≠ p'), G'.f p p' hne ≫ k p ≫ G.ι hI p =
      G'.t p p' hne ≫ G'.f p' p hne.symm ≫ k p' ≫ G.ι hI p') :
    (G'.fibreProduct hI').toLocallyRingedSpace ⟶ (G.fibreProduct hI).toLocallyRingedSpace :=
  (G'.formalGlueData hI').mapGlued (G.formalGlueData hI) id (fun p => k p)
    (CategoryTheory.GlueData.ofGlueData'_f_comp G'.glueData' (fun p => k p ≫ G.ι hI p) h)

@[reassoc (attr := simp)]
theorem ι_map (hI' : I'.FG) (hI : I.FG) (k) (h) (p : JX × JY) :
    G'.ι hI' p ≫ G'.map G hI' hI k h = k p ≫ G.ι hI p :=
  (G'.formalGlueData hI').ι_mapGlued _ _ _ _ p

/-- **Uniqueness**: a morphism of glued fibre products restricting to `k p` on every chart is
`AlgebraicGeometry.DoubleChartGlue.map`. -/
theorem map_ext (hI' : I'.FG) (hI : I.FG) {k} {h}
    {m : (G'.fibreProduct hI').toLocallyRingedSpace ⟶ (G.fibreProduct hI).toLocallyRingedSpace}
    (hm : ∀ p, G'.ι hI' p ≫ m = k p ≫ G.ι hI p) : m = G'.map G hI' hI k h :=
  (G'.formalGlueData hI').mapGlued_ext _ hm

end Map

/-! ### The base change -/

section BaseChange

variable {R' : Type u} [CommRing R'] [Algebra R R'] {I' : Ideal R'}
variable [∀ i, Algebra R' (A i)] [∀ i, IsScalarTower R R' (A i)]
variable [∀ j, Algebra R' (B j)] [∀ j, IsScalarTower R R' (B j)]
variable (G' : DoubleChartGlue R' I' A B) (G : DoubleChartGlue R I A B)

/-- **The chart-level base-change comparison**
`Spf (A_{p.1} ⊗̂_{R'} B_{p.2}) ⟶ Spf (A_{p.1} ⊗̂_R B_{p.2})`, which is
`CompletedTensorProduct.schemeBaseChange` read as a morphism of locally ringed spaces. -/
def chartBaseChange (hI : I.FG) (hII' : I.map (algebraMap R R') = I') (p : JX × JY) :
    doubleChartObj R' I' A B p ⟶ doubleChartObj R I A B p :=
  locallyRingedSpaceMap (CompletedTensorProduct.idealOfDefinition R I (A p.1) (B p.2))
    (CompletedTensorProduct.idealOfDefinition R' I' (A p.1) (B p.2))
    (CompletedTensorProduct.baseChangeHom (A := A p.1) (B := B p.2) hI hII')
    (CompletedTensorProduct.le_comap_baseChangeHom hI hII')

/-- **The overlap square**: the one hypothesis the glued base change needs, and the only thing this
file does not prove. At `p ≠ p'` the chart comparisons at `p` and at `p'` must agree on the
source's overlap of the two charts. -/
def IsBaseChangeOverlapCompatible (hI : I.FG) (hII' : I.map (algebraMap R R') = I') : Prop :=
  ∀ (p p' : JX × JY) (hne : p ≠ p'),
    G'.f p p' hne ≫ chartBaseChange hI hII' p ≫ G.ι hI p =
      G'.t p p' hne ≫ G'.f p' p hne.symm ≫ chartBaseChange hI hII' p' ≫ G.ι hI p'

/-- **The base change of a glued fibre product**, `X ×_{Spf I'} Y ⟶ X ×_{Spf I} Y`, assembled from
the chart comparisons of `FormalSchemes.CompletedTensorBaseChange`. -/
def baseChange (hI' : I'.FG) (hI : I.FG) (hII' : I.map (algebraMap R R') = I')
    (h : G'.IsBaseChangeOverlapCompatible G hI hII') :
    (G'.fibreProduct hI').toLocallyRingedSpace ⟶ (G.fibreProduct hI).toLocallyRingedSpace :=
  G'.map G hI' hI (chartBaseChange hI hII') h

/-- **The glued base change restricts to the chart comparison on every chart.** -/
@[reassoc (attr := simp)]
theorem ι_baseChange (hI' : I'.FG) (hI : I.FG) (hII' : I.map (algebraMap R R') = I')
    (h : G'.IsBaseChangeOverlapCompatible G hI hII') (p : JX × JY) :
    G'.ι hI' p ≫ G'.baseChange G hI' hI hII' h = chartBaseChange hI hII' p ≫ G.ι hI p :=
  G'.ι_map G hI' hI _ h p

/-- **Uniqueness of the glued base change** among morphisms restricting to the chart comparisons.
-/
theorem baseChange_ext (hI' : I'.FG) (hI : I.FG) (hII' : I.map (algebraMap R R') = I')
    (h : G'.IsBaseChangeOverlapCompatible G hI hII')
    {m : (G'.fibreProduct hI').toLocallyRingedSpace ⟶ (G.fibreProduct hI).toLocallyRingedSpace}
    (hm : ∀ p, G'.ι hI' p ≫ m = chartBaseChange hI hII' p ≫ G.ι hI p) :
    m = G'.baseChange G hI' hI hII' h :=
  G'.map_ext G hI' hI hm

section Scheme

variable [TopologicalSpace R] [IsAdicRing I]
variable [∀ i, TopologicalSpace (A i)] [∀ i, IsAdicRing (I.map (algebraMap R (A i)))]
variable [∀ j, TopologicalSpace (B j)] [∀ j, IsAdicRing (I.map (algebraMap R (B j)))]
variable [∀ p : JX × JY, IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (A p.1) (B p.2))]
variable
  [∀ p : JX × JY, IsAdicRing (CompletedTensorProduct.idealOfDefinition R' I' (A p.1) (B p.2))]

/-- **The chart-level comparison is `CompletedTensorProduct.schemeBaseChange`**, so by
`CompletedTensorProduct.schemeBaseChange_isClosedImmersion` every chart leg of
`AlgebraicGeometry.DoubleChartGlue.baseChange` is a closed immersion of affine formal schemes.
Whether the glued morphism inherits anything from that is not settled here. -/
theorem chartBaseChange_eq_schemeBaseChange (hI : I.FG) (hII' : I.map (algebraMap R R') = I')
    (p : JX × JY) :
    chartBaseChange (A := A) (B := B) hI hII' p =
      (CompletedTensorProduct.schemeBaseChange (A := A p.1) (B := B p.2) hI hII').toLRSHom :=
  rfl

end Scheme

end BaseChange

end DoubleChartGlue

/-! ### Every datum's fibre product is one of these -/

namespace BothChartedFibreDatum

variable {R I} {hI : I.FG}

/-- The geometric glue carried by a two-sided charted fibre-product datum. -/
def toDoubleChartGlue (D : BothChartedFibreDatum R I hI) :
    letI := D.commRingA
    letI := D.algebraA
    letI := D.commRingB
    letI := D.algebraB
    DoubleChartGlue R I D.A D.B :=
  letI := D.commRingA
  letI := D.algebraA
  letI := D.commRingB
  letI := D.algebraB
  { V := D.V, f := D.f, hf := D.hf, t := D.t, t_inv := D.t_inv, t' := D.t',
    t_fac := D.t_fac, cocycle := D.cocycle }

/-- **The glued fibre product of a datum is the glued object of its carried glue**, by `rfl`. This
is the content of the structure above:
`AlgebraicGeometry.BothChartedFibreDatum.generalFibreProduct` reads off a datum its chart algebras
and its eight geometric fields, and nothing else — not `gX`, `gY`, `τX` or `τY`, which
`AlgebraicGeometry.BothChartedFibreDatum` carries as documentation of intent. -/
theorem generalFibreProduct_eq (D : BothChartedFibreDatum R I hI) :
    letI := D.commRingA
    letI := D.algebraA
    letI := D.commRingB
    letI := D.algebraB
    D.generalFibreProduct = D.toDoubleChartGlue.fibreProduct hI := rfl

end BothChartedFibreDatum

end AlgebraicGeometry

end
