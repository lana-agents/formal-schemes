import FormalSchemes.GlueDataSectionGlue
import FormalSchemes.GlueDataImageInter

set_option linter.style.header false

/-!
# The compatibility condition on a patch-wise family, read on the glue datum's overlaps

`AlgebraicGeometry.FormalScheme.GlueData.exists_ι_c_app_eq_iff_isCompatible`
(`FormalSchemes.GlueDataSectionGlue`) describes `Γ (X, W)` for a glued formal scheme `X` as the
patch-wise families `t i : Γ (D.U i, (D.ι i)⁻¹ W)` that are **compatible**. Its module docstring
records what it leaves undone: the compatibility there is
`TopCat.Presheaf.IsCompatible`, a condition on opens of the *glued* space, stated for the family
transported by `AlgebraicGeometry.FormalScheme.GlueData.ιSectionIso`. Nothing said which two maps
the patches themselves have to agree under, or over which open.

This file answers that. The two maps are the two legs `D.f i j` and `D.t i j ≫ D.f j i` out of the
overlap object `D.V (i, j)`, and the open is the preimage of `W` under either of them — the same
open, because `CategoryTheory.GlueData.glue_condition` says the two legs agree after `D.ι`:

```
D.t i j ≫ D.f j i ≫ D.ι j = D.f i j ≫ D.ι i
```

So `AlgebraicGeometry.FormalScheme.GlueData.IsOverlapCompatible` mentions only the glue datum's own
data. No sheaf, no cover, and no open of the glued space appears in it.

## What is here

* `AlgebraicGeometry.FormalScheme.GlueData.range_f_comp_ι`: two patches meet exactly along the
  image of their overlap, `range (D.f i j ≫ D.ι i) = range (D.ι i) ∩ range (D.ι j)`. The
  containment `⊆` half is `glue_condition`; the reverse is
  `AlgebraicGeometry.LocallyRingedSpace.GlueData.range_ι_inter_subset`
  (`FormalSchemes.GlueDataImageInter`).
* `AlgebraicGeometry.FormalScheme.GlueData.ιCover_inf` and
  `AlgebraicGeometry.FormalScheme.GlueData.isIso_c_app_ιCover_inf`: consequently the overlap of two
  members of the cover `GlueData.ιCover` is `W` met with the range of `D.f i j ≫ D.ι i`, and the
  `c`-component of that morphism is an isomorphism there. **This is the whole point**: a section of
  the glued space over `ιCover W i ⊓ ιCover W j` is nothing but a section of `D.V (i, j)`.
* `AlgebraicGeometry.FormalScheme.GlueData.c_app_ιSectionIso_hom`: the dictionary
  `GlueData.ιSectionIso` read in the other direction — pulling its value back along `D.ι i`
  returns the section one started with.
* `AlgebraicGeometry.FormalScheme.GlueData.c_app_f_comp_ι_restrict_left` and
  `AlgebraicGeometry.FormalScheme.GlueData.c_app_f_comp_ι_restrict_right`: the two computations the
  translation rests on. Each says what the pullback along `D.f i j ≫ D.ι i` does to one side of
  `TopCat.Presheaf.IsCompatible`, and the answer is the corresponding leg applied to `t i`
  resp. `t j`.
* `AlgebraicGeometry.FormalScheme.GlueData.IsOverlapCompatible`: **the condition.**
* `AlgebraicGeometry.FormalScheme.GlueData.isCompatible_iff_isOverlapCompatible`: it is equivalent
  to `TopCat.Presheaf.IsCompatible` for the transported family, and
  `AlgebraicGeometry.FormalScheme.GlueData.exists_ι_c_app_eq_iff_isOverlapCompatible`,
  `AlgebraicGeometry.FormalScheme.GlueData.existsUnique_ι_c_app_eq_of_isOverlapCompatible`: hence a
  patch-wise family is the family of pullbacks of a (unique) section of `Γ (X, W)` exactly when it
  satisfies it.

## What this does not do

It does not simplify the condition at any particular glue datum. For a datum whose `D.V (i, j)` is
empty for most pairs — a chain, say — the condition at those pairs is vacuous and the condition at
`i = j` is trivial, so only finitely many pairs carry content; none of that is proved here, because
none of it is true for a general glue datum.

## References

* [The Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA) — gluing sheaves.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
-/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry CategoryTheory.Limits
open TopCat.Presheaf

noncomputable section

namespace AlgebraicGeometry.LocallyRingedSpace

/-- **Naturality of a `c`-component at a pair of opens with the same preimage.** Restricting a
section from `B` to `A ≤ B` and then pulling back along `ψ` is pulling back and then transporting,
and when `ψ⁻¹ A` and `ψ⁻¹ B` are *equal* the transport is the `eqToHom` between them.

The composite-morphism spelling of the naturality square is definitional but `simp` will not reach
it, so it is read on elements by hand — the same step as in
`AlgebraicGeometry.LocallyRingedSpace.restrict_eq_of_c_app_eq`
(`FormalSchemes.GlueDataSectionExt`). Identifying the resulting restriction map with the `eqToHom`
is `AlgebraicGeometry.LocallyRingedSpace.presheaf_map_congr`: the two are maps between the same
pair of opens, and opens form a preorder. -/
theorem c_app_map_homOfLE_of_map_eq {Z X : LocallyRingedSpace.{u}} (ψ : Z ⟶ X)
    {A B : Opens X} (hAB : A ≤ B)
    (h : (Opens.map ψ.base).obj A = (Opens.map ψ.base).obj B)
    (u : X.presheaf.obj (op B)) :
    (ψ.c.app (op A)).hom ((X.presheaf.map (homOfLE hAB).op).hom u) =
      (Z.presheaf.map (eqToHom (congrArg op h.symm))).hom ((ψ.c.app (op B)).hom u) := by
  have hnat := ψ.c.naturality (homOfLE hAB).op
  have key : ∀ v : X.presheaf.obj (op B),
      (ψ.c.app (op A)).hom ((X.presheaf.map (homOfLE hAB).op).hom v) =
        ((ψ.base _* Z.presheaf).map (homOfLE hAB).op).hom ((ψ.c.app (op B)).hom v) := fun v =>
    congrArg (fun φ : X.presheaf.obj (op B) ⟶ _ => φ.hom v) hnat
  rw [key]
  exact ConcreteCategory.congr_hom
    (presheaf_map_congr Z.presheaf ((Opens.map ψ.base).map (homOfLE hAB)).op
      (eqToHom (congrArg op h.symm))) _

/-- **Three successive restrictions are one.** Any three composable restriction maps of a presheaf
on a space compose to *the* map between their outer opens, whichever one that is: the homs of
`Opens Z` are a preorder, so there is at most one. The iterated form of
`AlgebraicGeometry.LocallyRingedSpace.presheaf_map_comp_apply`
(`FormalSchemes.ActionInvariantExtension`), and what lets a chain of `eqToHom` transports built by
different lemmas be collapsed in one step without naming any of them. -/
theorem presheaf_map_three_apply {Z : TopCat.{u}} (F : (Opens Z)ᵒᵖ ⥤ CommRingCat.{u})
    {A B C E : (Opens Z)ᵒᵖ} (m₁ : A ⟶ B) (m₂ : B ⟶ C) (m₃ : C ⟶ E) (m : A ⟶ E)
    (y : ToType (F.obj A)) :
    (F.map m₃) ((F.map m₂) ((F.map m₁) y)) = (F.map m) y := by
  rw [presheaf_map_comp_apply, presheaf_map_comp_apply]
  exact ConcreteCategory.congr_hom (presheaf_map_congr F _ m) y

end AlgebraicGeometry.LocallyRingedSpace

namespace AlgebraicGeometry.FormalScheme

variable (D : FormalScheme.GlueData.{u})

/-! ### Two patches meet along their overlap -/

/-- **The range of the overlap inclusion is the intersection of the two patch ranges.** The
containment `⊆` is `CategoryTheory.GlueData.glue_condition`, which exhibits `D.f i j ≫ D.ι i` as
factoring through `D.ι j` as well; the containment `⊇` is
`AlgebraicGeometry.LocallyRingedSpace.GlueData.range_ι_inter_subset`
(`FormalSchemes.GlueDataImageInter`), which is `TopCat.GlueData.image_inter` transported across the
carrier comparison isomorphism. -/
theorem GlueData.range_f_comp_ι (i j : D.toLocallyRingedSpaceGlueData.J) :
    Set.range (D.toLocallyRingedSpaceGlueData.f i j ≫ D.ι i).base =
      Set.range (D.ι i).base ∩ Set.range (D.ι j).base := by
  refine subset_antisymm ?_ (D.toLocallyRingedSpaceGlueData.range_ι_inter_subset i j)
  rintro _ ⟨v, rfl⟩
  refine ⟨⟨(D.toLocallyRingedSpaceGlueData.f i j).base v, rfl⟩,
    ⟨(D.toLocallyRingedSpaceGlueData.t i j ≫ D.toLocallyRingedSpaceGlueData.f j i).base v, ?_⟩⟩
  exact congrArg (fun m : D.toLocallyRingedSpaceGlueData.V (i, j) ⟶
    (D.gluedFormalScheme).toLocallyRingedSpace => m.base v)
    (D.toLocallyRingedSpaceGlueData.glue_condition i j)

/-- **Two members of the cover `GlueData.ιCover` meet along the overlap.** The `Opens` form of
`GlueData.range_f_comp_ι`; the shape on the right is the one
`AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.c_iso'` asks for, after
`AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.inf_opensFunctor_top`. -/
theorem GlueData.ιCover_inf (W : Opens (D.gluedFormalScheme).toLocallyRingedSpace)
    (i j : D.toLocallyRingedSpaceGlueData.J) :
    D.ιCover W i ⊓ D.ιCover W j =
      W ⊓ (PresheafedSpace.IsOpenImmersion.opensFunctor
        (D.toLocallyRingedSpaceGlueData.f i j ≫ D.ι i).toHom).obj ⊤ := by
  ext y
  constructor
  · rintro ⟨⟨hW, hi⟩, ⟨-, hj⟩⟩
    obtain ⟨a, -, ha⟩ := hi
    obtain ⟨b, -, hb⟩ := hj
    have hmem : y ∈ Set.range (D.toLocallyRingedSpaceGlueData.f i j ≫ D.ι i).base := by
      rw [D.range_f_comp_ι i j]
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    obtain ⟨v, hv⟩ := hmem
    exact ⟨hW, v, trivial, hv⟩
  · rintro ⟨hW, v, -, rfl⟩
    have hmem : (D.toLocallyRingedSpaceGlueData.f i j ≫ D.ι i).base v ∈
        Set.range (D.ι i).base ∩ Set.range (D.ι j).base := by
      rw [← D.range_f_comp_ι i j]; exact ⟨v, rfl⟩
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hmem
    exact ⟨⟨hW, a, trivial, ha⟩, ⟨hW, b, trivial, hb⟩⟩

/-- **The `c`-component of the overlap inclusion is invertible over `ιCover W i ⊓ ιCover W j`.**
`AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.c_iso'` at `GlueData.ιCover_inf`. Like
`AlgebraicGeometry.FormalScheme.GlueData.isIso_c_app_ιCover` this is a `theorem` and not an
`instance`, for the same reason: the `IsIso` is stated at the locally ringed space spelling of the
`c`-component, and instance search does not see through
`AlgebraicGeometry.LocallyRingedSpace.Hom.toShHom`. -/
theorem GlueData.isIso_c_app_ιCover_inf
    (W : Opens (D.gluedFormalScheme).toLocallyRingedSpace)
    (i j : D.toLocallyRingedSpaceGlueData.J) :
    IsIso ((D.toLocallyRingedSpaceGlueData.f i j ≫ D.ι i).c.app
      (op (D.ιCover W i ⊓ D.ιCover W j))) :=
  PresheafedSpace.IsOpenImmersion.c_iso'
    (D.toLocallyRingedSpaceGlueData.f i j ≫ D.ι i).toHom _
    ((D.ιCover_inf W i j).trans (PresheafedSpace.IsOpenImmersion.inf_opensFunctor_top
      (D.toLocallyRingedSpaceGlueData.f i j ≫ D.ι i).toHom W))

/-! ### The opens the overlap sees -/

/-- **The overlap does not see the difference between `W` and the part of `W` the patch `i` meets.**
`AlgebraicGeometry.FormalScheme.GlueData.map_ιCover` pulled back one step further, along
`D.f i j`. -/
theorem GlueData.map_f_comp_ι_ιCover (W : Opens (D.gluedFormalScheme).toLocallyRingedSpace)
    (i j : D.toLocallyRingedSpaceGlueData.J) :
    (Opens.map (D.toLocallyRingedSpaceGlueData.f i j ≫ D.ι i).base).obj (D.ιCover W i) =
      (Opens.map (D.toLocallyRingedSpaceGlueData.f i j ≫ D.ι i).base).obj W := by
  ext v
  exact ⟨fun h => h.1, fun h => ⟨h, (D.toLocallyRingedSpaceGlueData.f i j).base v, trivial, rfl⟩⟩

/-- **The same for the patch `j`.** The overlap lands in the range of `D.ι j` too, by
`CategoryTheory.GlueData.glue_condition`; that is the only difference from
`GlueData.map_f_comp_ι_ιCover`. -/
theorem GlueData.map_f_comp_ι_ιCover_right
    (W : Opens (D.gluedFormalScheme).toLocallyRingedSpace)
    (i j : D.toLocallyRingedSpaceGlueData.J) :
    (Opens.map (D.toLocallyRingedSpaceGlueData.f i j ≫ D.ι i).base).obj (D.ιCover W j) =
      (Opens.map (D.toLocallyRingedSpaceGlueData.f i j ≫ D.ι i).base).obj W := by
  ext v
  refine ⟨fun h => h.1, fun h => ⟨h,
    (D.toLocallyRingedSpaceGlueData.t i j ≫ D.toLocallyRingedSpaceGlueData.f j i).base v,
    trivial, ?_⟩⟩
  exact congrArg (fun m : D.toLocallyRingedSpaceGlueData.V (i, j) ⟶
    (D.gluedFormalScheme).toLocallyRingedSpace => m.base v)
    (D.toLocallyRingedSpaceGlueData.glue_condition i j)

/-- **And for their meet.** This is the open every statement below is read over: the overlap sees
`ιCover W i ⊓ ιCover W j` as all of `(D.f i j ≫ D.ι i)⁻¹ W`. -/
theorem GlueData.map_f_comp_ι_ιCover_inf
    (W : Opens (D.gluedFormalScheme).toLocallyRingedSpace)
    (i j : D.toLocallyRingedSpaceGlueData.J) :
    (Opens.map (D.toLocallyRingedSpaceGlueData.f i j ≫ D.ι i).base).obj
        (D.ιCover W i ⊓ D.ιCover W j) =
      (Opens.map (D.toLocallyRingedSpaceGlueData.f i j ≫ D.ι i).base).obj W := by
  ext v
  refine ⟨fun h => h.1.1, fun h => ⟨⟨h, (D.toLocallyRingedSpaceGlueData.f i j).base v,
    trivial, rfl⟩, h, (D.toLocallyRingedSpaceGlueData.t i j ≫
      D.toLocallyRingedSpaceGlueData.f j i).base v, trivial, ?_⟩⟩
  exact congrArg (fun m : D.toLocallyRingedSpaceGlueData.V (i, j) ⟶
    (D.gluedFormalScheme).toLocallyRingedSpace => m.base v)
    (D.toLocallyRingedSpaceGlueData.glue_condition i j)

/-- **The two legs of the overlap pull `W` back to the same open.**
`CategoryTheory.GlueData.glue_condition`, read through `Opens.map`. This is the equality that makes
`GlueData.IsOverlapCompatible` a statement about two sections of the *same* ring. -/
theorem GlueData.map_glue_condition_obj
    (W : Opens (D.gluedFormalScheme).toLocallyRingedSpace)
    (i j : D.toLocallyRingedSpaceGlueData.J) :
    (Opens.map ((D.toLocallyRingedSpaceGlueData.t i j ≫
        D.toLocallyRingedSpaceGlueData.f j i) ≫ D.ι j).base).obj W =
      (Opens.map (D.toLocallyRingedSpaceGlueData.f i j ≫ D.ι i).base).obj W :=
  congrArg (fun m : D.toLocallyRingedSpaceGlueData.V (i, j) ⟶
    (D.gluedFormalScheme).toLocallyRingedSpace => (Opens.map m.base).obj W)
    ((Category.assoc _ _ _).trans (D.toLocallyRingedSpaceGlueData.glue_condition i j))

/-! ### The dictionary, in the other direction -/

/-- **Pulling the dictionary's value back along the patch inclusion returns the section.** The
converse reading of `AlgebraicGeometry.FormalScheme.GlueData.ιSectionIso_hom_c_app`, and the only
property of `GlueData.ιSectionIso` used below.

It is immediate from the definition — the `Iso` is a transport followed by the inverse of
`(D.ι i).c.app`, so composing with that `c`-component again cancels — but the transport has to be
recognised as a `CategoryTheory.Functor.map` of an `eqToHom` first, which is what the `hmap` step
does. -/
theorem GlueData.c_app_ιSectionIso_hom (W : Opens (D.gluedFormalScheme).toLocallyRingedSpace)
    (i : D.toLocallyRingedSpaceGlueData.J)
    (x : (D.toLocallyRingedSpaceGlueData.U i).presheaf.obj
      (op ((Opens.map (D.ι i).base).obj W))) :
    ((D.ι i).c.app (op (D.ιCover W i))).hom ((D.ιSectionIso W i).hom.hom x) =
      ((D.toLocallyRingedSpaceGlueData.U i).presheaf.map
        (eqToHom (congrArg op (D.map_ιCover W i).symm))).hom x := by
  haveI := D.isIso_c_app_ιCover W i
  have hL : (D.ιSectionIso W i).hom =
      ((D.toLocallyRingedSpaceGlueData.U i).presheaf.mapIso
        (eqToIso (D.map_ιCover W i)).op).hom ≫
          (asIso ((D.ι i).c.app (op (D.ιCover W i)))).inv := rfl
  have hmap : ((D.toLocallyRingedSpaceGlueData.U i).presheaf.mapIso
      (eqToIso (D.map_ιCover W i)).op).hom =
      (D.toLocallyRingedSpaceGlueData.U i).presheaf.map
        (eqToHom (congrArg op (D.map_ιCover W i).symm)) := by
    simp
  rw [hL, ConcreteCategory.comp_apply, ← hmap]
  exact (asIso ((D.ι i).c.app (op (D.ιCover W i)))).inv_hom_id_apply _

/-! ### The two sides of `IsCompatible`, read on the overlap -/

/-- **The left-hand side of `TopCat.Presheaf.IsCompatible`, pulled back to the overlap, is
`D.f i j` applied to `t i`.** The four steps are: naturality along
`ιCover W i ⊓ ιCover W j ≤ ιCover W i` (`c_app_map_homOfLE_of_map_eq`); factoring the pullback along
`D.f i j ≫ D.ι i` (`AlgebraicGeometry.LocallyRingedSpace.c_app_comp_of_eq`); the dictionary
(`GlueData.c_app_ιSectionIso_hom`); and moving the dictionary's transport past `D.f i j`
(`AlgebraicGeometry.PresheafedSpace.c_app_map_eqToHom`). The three transports they leave behind are
collapsed in one step by `presheaf_map_three_apply`.

Every step is chained with `Eq.trans` and `congrArg` rather than `rw`: the goal reaches the glued
space's `AlgebraicGeometry.PresheafedSpace.presheaf` through
`AlgebraicGeometry.FormalScheme.GlueData.gluedFormalScheme` and the hypotheses reach it through
that formal scheme's underlying locally ringed space. The two spellings print identically and are
definitionally equal but are not syntactically equal, so `rw` reports that it cannot find the
pattern. -/
theorem GlueData.c_app_f_comp_ι_restrict_left
    (W : Opens (D.gluedFormalScheme).toLocallyRingedSpace)
    (i j : D.toLocallyRingedSpaceGlueData.J)
    (x : (D.toLocallyRingedSpaceGlueData.U i).presheaf.obj
      (op ((Opens.map (D.ι i).base).obj W)))
    (hΩ : (Opens.map (D.toLocallyRingedSpaceGlueData.f i j ≫ D.ι i).base).obj
        (D.ιCover W i ⊓ D.ιCover W j) =
      (Opens.map (D.toLocallyRingedSpaceGlueData.f i j ≫ D.ι i).base).obj W) :
    (((D.toLocallyRingedSpaceGlueData.f i j ≫ D.ι i).c.app
        (op (D.ιCover W i ⊓ D.ιCover W j))).hom
      (((D.gluedFormalScheme).presheaf.map (homOfLE inf_le_left).op).hom
        ((D.ιSectionIso W i).hom.hom x))) =
      ((D.toLocallyRingedSpaceGlueData.V (i, j)).presheaf.map
        (eqToHom (congrArg op hΩ.symm))).hom
        (((D.toLocallyRingedSpaceGlueData.f i j).c.app
          (op ((Opens.map (D.ι i).base).obj W))).hom x) := by
  have hiL : (Opens.map (D.toLocallyRingedSpaceGlueData.f i j ≫ D.ι i).base).obj
        (D.ιCover W i ⊓ D.ιCover W j) =
      (Opens.map (D.toLocallyRingedSpaceGlueData.f i j ≫ D.ι i).base).obj (D.ιCover W i) :=
    hΩ.trans (D.map_f_comp_ι_ιCover W i j).symm
  have h1 := LocallyRingedSpace.c_app_map_homOfLE_of_map_eq
    (D.toLocallyRingedSpaceGlueData.f i j ≫ D.ι i) (inf_le_left) hiL
    ((D.ιSectionIso W i).hom.hom x)
  have h2 := LocallyRingedSpace.c_app_comp_of_eq
    (D.toLocallyRingedSpaceGlueData.f i j) (D.ι i) rfl (D.ιCover W i)
    ((D.ιSectionIso W i).hom.hom x)
  have h3 := D.c_app_ιSectionIso_hom W i x
  have h4 := PresheafedSpace.c_app_map_eqToHom
    (D.toLocallyRingedSpaceGlueData.f i j).toShHom.hom (D.map_ιCover W i).symm x
  refine h1.trans ?_
  refine Eq.trans (congrArg _ h2) ?_
  refine Eq.trans (congrArg _ (congrArg _ (congrArg _ h3))) ?_
  refine Eq.trans (congrArg _ (congrArg _ h4)) ?_
  exact LocallyRingedSpace.presheaf_map_three_apply _ _ _ _ _ _

/-- **The right-hand side of `TopCat.Presheaf.IsCompatible`, pulled back to the overlap, is
`D.t i j ≫ D.f j i` applied to `t j`.** Same four steps as
`GlueData.c_app_f_comp_ι_restrict_left`, with the factorisation of `D.f i j ≫ D.ι i` through
`D.ι j` supplied by `hglue` — which is `CategoryTheory.GlueData.glue_condition` reassociated — in
place of the `rfl` used there. -/
theorem GlueData.c_app_f_comp_ι_restrict_right
    (W : Opens (D.gluedFormalScheme).toLocallyRingedSpace)
    (i j : D.toLocallyRingedSpaceGlueData.J)
    (y : (D.toLocallyRingedSpaceGlueData.U j).presheaf.obj
      (op ((Opens.map (D.ι j).base).obj W)))
    (hglue : (D.toLocallyRingedSpaceGlueData.f i j ≫ D.ι i) =
      (D.toLocallyRingedSpaceGlueData.t i j ≫ D.toLocallyRingedSpaceGlueData.f j i) ≫ D.ι j)
    (hR : (Opens.map (D.toLocallyRingedSpaceGlueData.f i j ≫ D.ι i).base).obj
        (D.ιCover W i ⊓ D.ιCover W j) =
      (Opens.map ((D.toLocallyRingedSpaceGlueData.t i j ≫
        D.toLocallyRingedSpaceGlueData.f j i) ≫ D.ι j).base).obj W) :
    (((D.toLocallyRingedSpaceGlueData.f i j ≫ D.ι i).c.app
        (op (D.ιCover W i ⊓ D.ιCover W j))).hom
      (((D.gluedFormalScheme).presheaf.map (homOfLE inf_le_right).op).hom
        ((D.ιSectionIso W j).hom.hom y))) =
      ((D.toLocallyRingedSpaceGlueData.V (i, j)).presheaf.map
        (eqToHom (congrArg op hR.symm))).hom
        (((D.toLocallyRingedSpaceGlueData.t i j ≫
            D.toLocallyRingedSpaceGlueData.f j i).c.app
          (op ((Opens.map (D.ι j).base).obj W))).hom y) := by
  have hjR : (Opens.map (D.toLocallyRingedSpaceGlueData.f i j ≫ D.ι i).base).obj
        (D.ιCover W i ⊓ D.ιCover W j) =
      (Opens.map (D.toLocallyRingedSpaceGlueData.f i j ≫ D.ι i).base).obj (D.ιCover W j) := by
    rw [D.map_f_comp_ι_ιCover_right W i j]
    exact hR.trans (congrArg (fun m : D.toLocallyRingedSpaceGlueData.V (i, j) ⟶
      (D.gluedFormalScheme).toLocallyRingedSpace => (Opens.map m.base).obj W) hglue.symm)
  have h1 := LocallyRingedSpace.c_app_map_homOfLE_of_map_eq
    (D.toLocallyRingedSpaceGlueData.f i j ≫ D.ι i) (inf_le_right) hjR
    ((D.ιSectionIso W j).hom.hom y)
  have h2 := LocallyRingedSpace.c_app_comp_of_eq
    (D.toLocallyRingedSpaceGlueData.t i j ≫ D.toLocallyRingedSpaceGlueData.f j i) (D.ι j)
    hglue (D.ιCover W j) ((D.ιSectionIso W j).hom.hom y)
  have h3 := D.c_app_ιSectionIso_hom W j y
  have h4 := PresheafedSpace.c_app_map_eqToHom
    (D.toLocallyRingedSpaceGlueData.t i j ≫
      D.toLocallyRingedSpaceGlueData.f j i).toShHom.hom (D.map_ιCover W j).symm y
  refine h1.trans ?_
  refine Eq.trans (congrArg _ h2) ?_
  refine Eq.trans (congrArg _ (congrArg _ (congrArg _ h3))) ?_
  refine Eq.trans (congrArg _ (congrArg _ h4)) ?_
  exact LocallyRingedSpace.presheaf_map_three_apply _ _ _ _ _ _

/-! ### The overlap condition -/

/-- **The overlap condition on a patch-wise family.** For every pair of indices, the two legs
`D.f i j` and `D.t i j ≫ D.f j i` out of the overlap object `D.V (i, j)` carry `t i` and `t j` to
the same section, over the preimage of `W` — one open, by `GlueData.map_glue_condition_obj`, which
is where the `eqToHom` comes from.

Only the glue datum's own data appears: no sheaf condition, no cover, and no open of the glued
space. `GlueData.isCompatible_iff_isOverlapCompatible` identifies it with
`TopCat.Presheaf.IsCompatible` for the family transported by `GlueData.ιSectionIso`. -/
def GlueData.IsOverlapCompatible (W : Opens (D.gluedFormalScheme).toLocallyRingedSpace)
    (t : ∀ i, (D.toLocallyRingedSpaceGlueData.U i).presheaf.obj
      (op ((Opens.map (D.ι i).base).obj W))) : Prop :=
  ∀ i j, ((D.toLocallyRingedSpaceGlueData.f i j).c.app
      (op ((Opens.map (D.ι i).base).obj W))).hom (t i) =
    ((D.toLocallyRingedSpaceGlueData.V (i, j)).presheaf.map
      (eqToHom (congrArg op (D.map_glue_condition_obj W i j)))).hom
      (((D.toLocallyRingedSpaceGlueData.t i j ≫
        D.toLocallyRingedSpaceGlueData.f j i).c.app
        (op ((Opens.map (D.ι j).base).obj W))).hom (t j))

/-- **The overlap condition is the compatibility condition.** Both directions are the same
computation: pull the equation over `ιCover W i ⊓ ιCover W j` back along `D.f i j ≫ D.ι i`, whose
`c`-component there is an isomorphism (`GlueData.isIso_c_app_ιCover_inf`) — so nothing is lost —
and read the two sides by `GlueData.c_app_f_comp_ι_restrict_left` and
`GlueData.c_app_f_comp_ι_restrict_right`. What is left is an equation between two transports of the
two legs' values, and `AlgebraicGeometry.PresheafedSpace.map_eqToHom_eq_iff`
(`FormalSchemes.ActionQuotientSections`) cancels them. -/
theorem GlueData.isCompatible_iff_isOverlapCompatible
    (W : Opens (D.gluedFormalScheme).toLocallyRingedSpace)
    (t : ∀ i, (D.toLocallyRingedSpaceGlueData.U i).presheaf.obj
      (op ((Opens.map (D.ι i).base).obj W))) :
    IsCompatible (D.gluedFormalScheme).presheaf (D.ιCover W)
        (fun i => (D.ιSectionIso W i).hom.hom (t i)) ↔ D.IsOverlapCompatible W t := by
  have hglue : ∀ i j : D.toLocallyRingedSpaceGlueData.J,
      (D.toLocallyRingedSpaceGlueData.f i j ≫ D.ι i) =
        (D.toLocallyRingedSpaceGlueData.t i j ≫
          D.toLocallyRingedSpaceGlueData.f j i) ≫ D.ι j := fun i j =>
    ((Category.assoc _ _ _).trans (D.toLocallyRingedSpaceGlueData.glue_condition i j)).symm
  constructor
  · intro h i j
    have hΩ := D.map_f_comp_ι_ιCover_inf W i j
    have hR := hΩ.trans (D.map_glue_condition_obj W i j).symm
    have hbl := D.c_app_f_comp_ι_restrict_left W i j (t i) hΩ
    have hbr := D.c_app_f_comp_ι_restrict_right W i j (t j) (hglue i j) hR
    have hb := congrArg (fun z => (((D.toLocallyRingedSpaceGlueData.f i j ≫ D.ι i).c.app
      (op (D.ιCover W i ⊓ D.ιCover W j))).hom z)) (h i j)
    exact (PresheafedSpace.map_eqToHom_eq_iff _ hΩ.symm hR.symm _ _).1
      (hbl.symm.trans (hb.trans hbr))
  · intro h i j
    haveI := D.isIso_c_app_ιCover_inf W i j
    have hΩ := D.map_f_comp_ι_ιCover_inf W i j
    have hR := hΩ.trans (D.map_glue_condition_obj W i j).symm
    have hbl := D.c_app_f_comp_ι_restrict_left W i j (t i) hΩ
    have hbr := D.c_app_f_comp_ι_restrict_right W i j (t j) (hglue i j) hR
    refine ConcreteCategory.injective_of_mono_of_preservesPullback
      ((D.toLocallyRingedSpaceGlueData.f i j ≫ D.ι i).c.app
        (op (D.ιCover W i ⊓ D.ιCover W j))) ?_
    exact hbl.trans (((PresheafedSpace.map_eqToHom_eq_iff _ hΩ.symm hR.symm _ _).2
      (h i j)).trans hbr.symm)

/-- **`Γ (X, W)` is exactly the families satisfying the overlap condition.**
`AlgebraicGeometry.FormalScheme.GlueData.exists_ι_c_app_eq_iff_isCompatible`
(`FormalSchemes.GlueDataSectionGlue`) with its hypothesis replaced by the condition on the glue
datum's own overlaps. -/
theorem GlueData.exists_ι_c_app_eq_iff_isOverlapCompatible
    (W : Opens (D.gluedFormalScheme).toLocallyRingedSpace)
    (t : ∀ i, (D.toLocallyRingedSpaceGlueData.U i).presheaf.obj
      (op ((Opens.map (D.ι i).base).obj W))) :
    (∃ s : (D.gluedFormalScheme).presheaf.obj (op W),
        ∀ i, ((D.ι i).c.app (op W)).hom s = t i) ↔ D.IsOverlapCompatible W t :=
  (D.exists_ι_c_app_eq_iff_isCompatible W t).trans (D.isCompatible_iff_isOverlapCompatible W t)

/-- **And the section it comes from is unique.**
`AlgebraicGeometry.FormalScheme.GlueData.existsUnique_ι_c_app_eq` with the same replacement. -/
theorem GlueData.existsUnique_ι_c_app_eq_of_isOverlapCompatible
    (W : Opens (D.gluedFormalScheme).toLocallyRingedSpace)
    (t : ∀ i, (D.toLocallyRingedSpaceGlueData.U i).presheaf.obj
      (op ((Opens.map (D.ι i).base).obj W)))
    (h : D.IsOverlapCompatible W t) :
    ∃! s : (D.gluedFormalScheme).presheaf.obj (op W),
      ∀ i, ((D.ι i).c.app (op W)).hom s = t i :=
  D.existsUnique_ι_c_app_eq W t ((D.isCompatible_iff_isOverlapCompatible W t).2 h)

end AlgebraicGeometry.FormalScheme
