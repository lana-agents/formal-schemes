import FormalSchemes.Gluing
import FormalSchemes.LocallyRingedSpaceGlueDesc

set_option linter.style.header false

/-!
# Gluing morphisms out of a glued formal scheme

Given a `FormalScheme.GlueData` `D` with glued formal scheme `T := D.gluedFormalScheme`, a family
of morphisms `k i : U i ⟶ Y` from the pieces to a common target `Y` that **agree on the overlaps**
glues to a single morphism `T ⟶ Y`. This is the morphism-level companion of the object-level
`gluedFormalScheme`: the glued space is the multicoequalizer of the gluing diagram
(`CategoryTheory.GlueData.glued = multicoequalizer D.diagram`), so a morphism out of it is exactly a
compatible cocone.

**Everything here is a wrapper over `FormalSchemes.LocallyRingedSpaceGlueDesc`**, which states the
same three results for a bare `AlgebraicGeometry.LocallyRingedSpace.GlueData`. Nothing in the
construction uses the formal-scheme condition on the pieces, so there is no second proof: `ι` of a
`FormalScheme.GlueData` is by definition `ι` of its underlying locally ringed space glue datum, and
`(D.gluedFormalScheme).toLocallyRingedSpace` is that datum's `glued`. The wrappers exist because the
Tate cluster spells its glued objects formally, and their statements are unchanged.

The compatibility condition is the one imposed by the gluing diagram
(`CategoryTheory.GlueData.diagram`, whose two legs on the overlap `V(i, j)` are `f i j` and
`t i j ≫ f j i`):
```
f i j ≫ k i = t i j ≫ f j i ≫ k j    for all i, j.
```

## The condition is owed only off the diagonal

Most of this tree's glue data are assembled by `CategoryTheory.GlueData.ofGlueData'` from a
`CategoryTheory.GlueData'`, which carries transitions only at pairs of **distinct** indices and
whose assembled `f i i` is an `eqToHom`. So the condition displayed above, which
`FormalScheme.GlueData.glueMorphisms` asks for at every pair, has content only off the diagonal:
`CategoryTheory.GlueData.ofGlueData'_f_comp` supplies the whole family from the distinct-index
case, and `CategoryTheory.GlueData.ofGlueData'_f_comp_of` reads an assembled condition back into
the vocabulary the `CategoryTheory.GlueData'` carries.
`CategoryTheory.GlueData.ofGlueData'_ι_comp` is that converse at the one family every consumer in
this tree actually supplies, the assembled datum's own `ι`, whose hypothesis is
`CategoryTheory.GlueData.glue_condition` and holds outright — so it asks for no hypothesis at all,
only the two indices and a proof that they differ.

These three are about Mathlib's `CategoryTheory.GlueData'` alone — no formal scheme and no locally
ringed space occurs in any of them — and they live here rather than lower down because this is the
module that states the condition they are about. The third asks in addition that the glued object
exist (`HasMulticoequalizer`), since `ι` is a morphism into it.

## Main definitions

* `CategoryTheory.GlueData.ofGlueData'_f_comp`: the overlap condition of an assembled
  `CategoryTheory.GlueData` follows from the same condition at **distinct** indices, and
  `CategoryTheory.GlueData.ofGlueData'_f_comp_of` is the converse.
* `CategoryTheory.GlueData.ofGlueData'_ι_comp`: the converse at the canonical family `ι`, where
  the hypothesis is discharged by `CategoryTheory.GlueData.glue_condition`.
* `FormalScheme.GlueData.glueMorphisms`: the glued morphism `T ⟶ Y`.
* `FormalScheme.GlueData.ι_glueMorphisms`: it restricts to `k i` along each `ι i`.
* `FormalScheme.GlueData.hom_ext`: two morphisms out of `T` agreeing on every piece are equal.

This is the combinator required to assemble the structural morphism `T ⟶ Spf R` of the Tate chain
(issue 208) out of the per-patch structural morphisms, and more generally any morphism out of a
non-affine formal scheme built by gluing.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4.
* Mathlib `CategoryTheory.GlueData`, `CategoryTheory.Limits.multicoequalizer`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

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

open scoped Classical in
/-- **The converse: the assembled overlap condition gives back the carried one.** A family `k`
satisfying `f i j ≫ k i = t i j ≫ f j i ≫ k j` at *every* pair of indices of
`CategoryTheory.GlueData.ofGlueData'` satisfies the same condition at **distinct** indices in the
vocabulary the `CategoryTheory.GlueData'` carries.

This is the direction a consumer of an already-assembled glue datum needs — the assembled condition
is what `CategoryTheory.GlueData.glue_condition` supplies, and the carried condition is what a
statement about the carried overlap objects can be written in. Proving it here rather than at the
assembled datum is not a matter of taste: at the assembled datum the index type is reached only
through the definition, so the category algebra that follows the unfolding is rejected at
`instances` transparency, while here the two indices already carry the index type the
`CategoryTheory.GlueData'` supplies. -/
theorem GlueData.ofGlueData'_f_comp_of {C : Type u} [Category.{v} C] (D : GlueData'.{v} C)
    {Y : C} (k : ∀ i, D.U i ⟶ Y)
    (h : ∀ i j : D.J, (GlueData.ofGlueData' D).f i j ≫ k i =
      (GlueData.ofGlueData' D).t i j ≫ (GlueData.ofGlueData' D).f j i ≫ k j)
    (i j : D.J) (hij : i ≠ j) :
    D.f i j hij ≫ k i = D.t i j hij ≫ D.f j i hij.symm ≫ k j := by
  have key := h i j
  simp only [GlueData.ofGlueData', GlueData'.f', dif_neg hij, dif_neg (Ne.symm hij),
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at key
  exact (cancel_epi (eqToHom (dif_neg hij))).mp key

/-- **The converse at the canonical family, where there is nothing left to supply.** The glue
inclusions `ι` of an assembled `CategoryTheory.GlueData.ofGlueData'` satisfy the overlap condition
at **distinct** indices in the vocabulary the `CategoryTheory.GlueData'` carries.

This is `CategoryTheory.GlueData.ofGlueData'_f_comp_of` at `k := ι`, and it is the only family this
tree's consumers ever pass: the general lemma's hypothesis is then
`CategoryTheory.GlueData.glue_condition`, which holds outright, so the specialisation takes no
hypothesis. It also absorbs an orientation flip — Mathlib states
`CategoryTheory.GlueData.glue_condition` as `t i j ≫ f j i ≫ ι j = f i j ≫ ι i`, the opposite way
round from the hypothesis above — so a consumer neither supplies the family nor `.symm`s the
condition.

The general form is kept and this one is proved from it: it is where the `dite` unfolding is
actually done, and a `k` other than `ι` is the general case. No consumer on this tree supplies
such a `k` — `AlgebraicGeometry.DoubleChartGlue.f_comp_ι`
(`FormalSchemes.GeneralFibreProductBaseChange`), the one that spells its family out rather than
leaving it to unification, supplies the canonical `ι` under another name. -/
theorem GlueData.ofGlueData'_ι_comp {C : Type u} [Category.{v} C] (D : GlueData'.{v} C)
    [HasMulticoequalizer (GlueData.ofGlueData' D).diagram] (i j : D.J) (hij : i ≠ j) :
    D.f i j hij ≫ (GlueData.ofGlueData' D).ι i =
      D.t i j hij ≫ D.f j i hij.symm ≫ (GlueData.ofGlueData' D).ι j :=
  GlueData.ofGlueData'_f_comp_of D _
    (fun i j => ((GlueData.ofGlueData' D).glue_condition i j).symm) i j hij

end CategoryTheory

namespace AlgebraicGeometry

namespace FormalScheme.GlueData

variable (D : FormalScheme.GlueData.{u}) {Y : LocallyRingedSpace.{u}}

/-- Abbreviation for the underlying `CategoryTheory.GlueData` of locally ringed spaces. -/
private abbrev cgd : CategoryTheory.GlueData LocallyRingedSpace.{u} :=
  D.toLocallyRingedSpaceGlueData.toGlueData

/-- **Gluing a family of morphisms out of the glued formal scheme.** Given morphisms
`k i : U i ⟶ Y` from the pieces to a common target that agree on the overlaps
(`f i j ≫ k i = t i j ≫ f j i ≫ k j`), the induced morphism `T ⟶ Y` out of the glued formal
scheme.

This is `AlgebraicGeometry.LocallyRingedSpace.GlueData.desc` at the underlying glue datum: the
formal-scheme condition on the pieces plays no part in the construction. Definitionally it is
still `Multicoequalizer.desc D.cgd.diagram Y k _`, which is what the `simp` lemmas of consumers
that unfold it rely on. -/
def glueMorphisms
    (k : ∀ i, D.cgd.U i ⟶ Y)
    (h : ∀ i j, D.cgd.f i j ≫ k i = D.cgd.t i j ≫ D.cgd.f j i ≫ k j) :
    (D.gluedFormalScheme).toLocallyRingedSpace ⟶ Y :=
  D.toLocallyRingedSpaceGlueData.desc k h

@[reassoc (attr := simp)]
theorem ι_glueMorphisms
    (k : ∀ i, D.cgd.U i ⟶ Y)
    (h : ∀ i j, D.cgd.f i j ≫ k i = D.cgd.t i j ≫ D.cgd.f j i ≫ k j)
    (i : D.toLocallyRingedSpaceGlueData.J) :
    D.ι i ≫ D.glueMorphisms k h = k i :=
  D.toLocallyRingedSpaceGlueData.ι_desc k h i

/-- **Uniqueness of the glued morphism**: two morphisms out of the glued formal scheme that agree
after restriction along every `ι i` are equal (the `ι i` are jointly epimorphic). -/
theorem hom_ext {f g : (D.gluedFormalScheme).toLocallyRingedSpace ⟶ Y}
    (h : ∀ i, D.ι i ≫ f = D.ι i ≫ g) : f = g :=
  D.toLocallyRingedSpaceGlueData.hom_ext h

end FormalScheme.GlueData

end AlgebraicGeometry
