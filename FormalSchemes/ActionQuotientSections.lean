import FormalSchemes.ActionQuotientColimit
import FormalSchemes.CoequalizerSections
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.HasColimits

set_option linter.style.header false

/-!
# The sections of a locally ringed space coequalizer, and of an action quotient

`FormalSchemes.CoequalizerSections` describes the sections of a coequalizer of **presheafed**
spaces: a section of the target over `π⁻¹ V` descends to the coequalizer exactly when its two
pullbacks agree. It says in so many words that it does not reach `LocallyRingedSpace`, and that
the missing step is the comparison isomorphism for the two forgetful functors together with the
fact that `Opens.map` along it is a bijection on opens.

This file runs that step. `CategoryTheory.actionQuotient` — the object whose structure sheaf the
stalk lemma for a free, properly discontinuous action is about — is a coequalizer in
`LocallyRingedSpace`, so the description has to hold there and not one category down.

## The obstacle, and how it is got around

`Limits.coequalizer f g` in `LocallyRingedSpace` is **not** definitionally the coequalizer of the
underlying presheafed spaces. The instance that wins typeclass resolution is the one coming from
`AlgebraicGeometry.LocallyRingedSpace.instHasColimits`, not
`AlgebraicGeometry.LocallyRingedSpace.coequalizerCoforkIsColimit`, so even
`(Limits.coequalizer f g).toSheafedSpace = Limits.coequalizer f.toShHom g.toShHom` fails to
elaborate by `rfl`. What is available is that both forgetful functors preserve coequalizers, and
`coequalizerIsoPresheafedSpace` assembles the two comparison isomorphisms into one.

Transporting a statement about *sections* across an isomorphism of presheafed spaces moves the
open as well as the section, which is what makes it more than a rewrite. Two devices keep it to a
dozen lines. First, `exists_c_app_eq_iff_of_iso` is phrased at the open
`(Opens.map e.hom.base).obj V'` rather than at an arbitrary `V`, so that
`exists_map_coequalizerIso_hom_base_obj` plus an `obtain ⟨V', rfl⟩` puts the goal in exactly that
shape and the two types agree definitionally. Second, the presheafed-space description takes the
equality of opens `(Opens.map g.base).obj (π⁻¹ V) = (Opens.map f.base).obj (π⁻¹ V)` as an explicit
argument; that makes it a `∀`-statement in which the projection may be rewritten with a
type-correct motive, which it is not when the equality is supplied by a fixed proof term.

## Main results

* `AlgebraicGeometry.PresheafedSpace.exists_c_app_eq_iff_of_iso`: the image of `p.c.app` is
  unchanged by composing `p` with an isomorphism, at the transported open.
* `AlgebraicGeometry.PresheafedSpace.exists_c_app_eq_iff_c_app_eq`: the two-term form of
  `exists_c_app_eq_iff_map_eq`, with a single `eqToHom` and the equality of opens as an argument.
* `AlgebraicGeometry.LocallyRingedSpace.coequalizerIsoPresheafedSpace` and
  `π_comp_coequalizerIsoPresheafedSpace_hom`: the comparison isomorphism, and that it carries the
  projection to the projection.
* `AlgebraicGeometry.LocallyRingedSpace.exists_c_app_eq_iff_c_app_eq`: **the headline** — a section
  of `Y` over `π⁻¹ V` descends to the locally ringed space coequalizer if and only if its two
  pullbacks agree.
* `AlgebraicGeometry.LocallyRingedSpace.injective_coequalizer_π_c_app`: it descends from at most
  one section.
* `CategoryTheory.exists_actionQuotientπ_c_app_eq_iff`: the same for `actionQuotientπ a`, which is
  the form the stalk lemma will consume.

## What this does not do

It does not turn "the two pullbacks agree" into "invariant under every `a g`". That is a separate
step: the common source of the two legs is the coproduct `∐_{g : G} X`, and detecting a section of
it by the coproduct legs needs the same comparison isomorphism run for the coproduct, together
with `AlgebraicGeometry.PresheafedSpace.colimit_section_ext`. Nor does it prove the stalk lemma,
whose remaining content is the collapse of the invariant sections over a separating open — the
step at which `AlgebraicGeometry.LocallyRingedSpace.IsProperlyDiscontinuousOn` finally enters,
and the only one of the four that is not bookkeeping.

## References

* [The Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] {D : Type*} [Category D] (F : C ⥤ D)
variable {A B : C} (f g : A ⟶ B) [HasCoequalizer f g] [HasCoequalizer (F.map f) (F.map g)]
  [PreservesColimit (parallelPair f g) F]

/-- **A colimit-preserving functor carries the coequalizer projection to the coequalizer
projection**, once the comparison isomorphism is put in. This is
`ι_comp_coequalizerComparison` with the comparison map read as the inverse of
`PreservesCoequalizer.iso`, which is the direction a transport of sections wants. -/
theorem map_π_comp_preservesCoequalizerIso_inv :
    F.map (coequalizer.π f g) ≫ (PreservesCoequalizer.iso F f g).inv =
      coequalizer.π (F.map f) (F.map g) := by
  rw [Iso.comp_inv_eq, PreservesCoequalizer.iso_hom, ι_comp_coequalizerComparison]

end CategoryTheory.Limits

namespace AlgebraicGeometry.PresheafedSpace

/-- **Two sections transported to a common open agree exactly when one is the transport of the
other.** Both transports are isomorphisms, so this is bookkeeping; it is stated because it is what
turns the three-open form of `exists_c_app_eq_iff_map_eq` into a two-open one. -/
theorem map_eqToHom_eq_iff {Z : TopCat.{u}} (F : (Opens Z)ᵒᵖ ⥤ CommRingCat.{u})
    {A B D : Opens Z} (hA : A = D) (hB : B = D)
    (x : ToType (F.obj (op A))) (y : ToType (F.obj (op B))) :
    (F.map (eqToHom (congrArg op hA))) x = (F.map (eqToHom (congrArg op hB))) y ↔
      x = (F.map (eqToHom (congrArg op (hB.trans hA.symm)))) y := by
  subst hA; subst hB; simp

/-- **Composing with an isomorphism does not change which sections descend.** For `e : W ≅ W'`,
the comparison map of `p ≫ e.hom` at `V'` is the comparison map of `p` at `e.hom⁻¹ V'` precomposed
with `e.hom.c.app`, which is an isomorphism; so the two have the same image.

The open on the right is written as `(Opens.map e.hom.base).obj V'` rather than as an arbitrary
open of `W`, because that is the shape in which the section `s` has the same type on both sides. -/
theorem exists_c_app_eq_iff_of_iso {Y W W' : PresheafedSpace.{u} CommRingCat.{u}}
    (p : Y ⟶ W) (e : W ≅ W') (V' : Opens W'.carrier)
    (s : ToType (Y.presheaf.obj (op ((Opens.map (p ≫ e.hom).base).obj V')))) :
    (∃ t, ((p ≫ e.hom).c.app (op V')) t = s) ↔
      ∃ t, (p.c.app (op ((Opens.map e.hom.base).obj V'))) t = s := by
  haveI : IsIso (e.hom.c.app (op V')) :=
    @NatIso.isIso_app_of_isIso _ _ _ _ _ _ e.hom.c (c_isIso_of_iso e.hom) (op V')
  have hcomp : (p ≫ e.hom).c.app (op V') =
      e.hom.c.app (op V') ≫ p.c.app (op ((Opens.map e.hom.base).obj V')) := rfl
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨(e.hom.c.app (op V')) t,
      ((ConcreteCategory.congr_hom hcomp t).trans (ConcreteCategory.comp_apply _ _ t)).symm⟩
  · rintro ⟨t, rfl⟩
    refine ⟨(inv (e.hom.c.app (op V'))) t, ?_⟩
    exact ((ConcreteCategory.congr_hom hcomp _).trans (ConcreteCategory.comp_apply _ _ _)).trans
      (congrArg _ (IsIso.inv_hom_id_apply (e.hom.c.app (op V')) t))

/-- **The injectivity half transports the same way**: `e.hom.c.app` is surjective, so injectivity
of the comparison map of `p ≫ e.hom` gives injectivity of that of `p`. -/
theorem injective_c_app_of_iso {Y W W' : PresheafedSpace.{u} CommRingCat.{u}}
    (p : Y ⟶ W) (e : W ≅ W') (V' : Opens W'.carrier)
    (hinj : Function.Injective ((p ≫ e.hom).c.app (op V'))) :
    Function.Injective (p.c.app (op ((Opens.map e.hom.base).obj V'))) := by
  haveI : IsIso (e.hom.c.app (op V')) :=
    @NatIso.isIso_app_of_isIso _ _ _ _ _ _ e.hom.c (c_isIso_of_iso e.hom) (op V')
  have hcomp : (p ≫ e.hom).c.app (op V') =
      e.hom.c.app (op V') ≫ p.c.app (op ((Opens.map e.hom.base).obj V')) := rfl
  have hsurj : Function.Surjective (e.hom.c.app (op V')) :=
    (ConcreteCategory.bijective_of_isIso _).2
  intro x y hxy
  obtain ⟨x', rfl⟩ := hsurj x
  obtain ⟨y', rfl⟩ := hsurj y
  refine congrArg _ (hinj (a₁ := x') (a₂ := y') ?_)
  refine ((ConcreteCategory.congr_hom hcomp x').trans
    (ConcreteCategory.comp_apply _ _ x')).trans (hxy.trans ?_)
  exact ((ConcreteCategory.congr_hom hcomp y').trans
    (ConcreteCategory.comp_apply _ _ y')).symm

section Coequalizer

variable {X Y : PresheafedSpace.{u} CommRingCat.{u}} (f g : X ⟶ Y)
variable (V : Opens (Limits.coequalizer f g).carrier)

/-- The two pullbacks of `π⁻¹ V` along the legs of a coequalizer are the same open, because both
composites with `π` are the colimit leg at `zero`. -/
theorem preimage_coequalizer_π_eq :
    (Opens.map g.base).obj ((Opens.map (Limits.coequalizer.π f g).base).obj V) =
      (Opens.map f.base).obj ((Opens.map (Limits.coequalizer.π f g).base).obj V) :=
  (preimage_preimage_coequalizer_π_right f g V).trans
    (preimage_preimage_coequalizer_π_left f g V).symm

/-- **The sections of a coequalizer of presheafed spaces, in two-open form.** The same statement as
`exists_c_app_eq_iff_map_eq`, with the two pullbacks compared on the open of the `f` leg instead of
both being transported to the colimit leg at `zero`.

The equality of opens is an explicit argument rather than
`preimage_coequalizer_π_eq f g V`, so that the resulting `∀`-statement can be rewritten along an
equation between projections with a type-correct motive — which is what the locally ringed space
transport below needs. -/
theorem exists_c_app_eq_iff_c_app_eq
    (h : (Opens.map g.base).obj ((Opens.map (Limits.coequalizer.π f g).base).obj V) =
      (Opens.map f.base).obj ((Opens.map (Limits.coequalizer.π f g).base).obj V))
    (s : ToType (Y.presheaf.obj (op ((Opens.map (Limits.coequalizer.π f g).base).obj V)))) :
    (∃ t, ((Limits.coequalizer.π f g).c.app (op V)) t = s) ↔
      (f.c.app (op ((Opens.map (Limits.coequalizer.π f g).base).obj V))) s =
        (X.presheaf.map (eqToHom (congrArg op h)))
          ((g.c.app (op ((Opens.map (Limits.coequalizer.π f g).base).obj V))) s) := by
  rw [exists_c_app_eq_iff_map_eq]
  exact map_eqToHom_eq_iff X.presheaf (preimage_preimage_coequalizer_π_left f g V)
    (preimage_preimage_coequalizer_π_right f g V) _ _

end Coequalizer

end AlgebraicGeometry.PresheafedSpace

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X Y : LocallyRingedSpace.{u}} (f g : X ⟶ Y)

/-- **The comparison isomorphism.** The underlying presheafed space of the locally ringed space
coequalizer is the presheafed space coequalizer — not definitionally, but through the two
`PreservesCoequalizer.iso`s, since `LocallyRingedSpace.forgetToSheafedSpace` and
`SheafedSpace.forgetToPresheafedSpace` both preserve coequalizers. -/
def coequalizerIsoPresheafedSpace :
    (Limits.coequalizer f g).toPresheafedSpace ≅
      Limits.coequalizer f.toShHom.hom g.toShHom.hom :=
  SheafedSpace.forgetToPresheafedSpace.mapIso
      (PreservesCoequalizer.iso LocallyRingedSpace.forgetToSheafedSpace f g).symm ≪≫
    (PreservesCoequalizer.iso SheafedSpace.forgetToPresheafedSpace f.toShHom g.toShHom).symm

set_option linter.style.setOption false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- The `SheafedSpace`/`PresheafedSpace` layer is an `InducedCategory`, so the goal is not
-- type-correct at `instances` transparency and `rw` refuses to match without this; the same two
-- options `SheafedSpace.mono_coequalizer_π_c_app` needs, for the same reason.
/-- **The comparison isomorphism carries the projection to the projection.** -/
theorem π_comp_coequalizerIsoPresheafedSpace_hom :
    (Limits.coequalizer.π f g).toShHom.hom ≫ (coequalizerIsoPresheafedSpace f g).hom =
      Limits.coequalizer.π f.toShHom.hom g.toShHom.hom := by
  change SheafedSpace.forgetToPresheafedSpace.map
      (LocallyRingedSpace.forgetToSheafedSpace.map (Limits.coequalizer.π f g)) ≫ _ = _
  rw [coequalizerIsoPresheafedSpace, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.symm_hom, ← Functor.map_comp_assoc, map_π_comp_preservesCoequalizerIso_inv]
  exact map_π_comp_preservesCoequalizerIso_inv SheafedSpace.forgetToPresheafedSpace
    f.toShHom g.toShHom

/-- The coequalizer condition, read on the underlying presheafed spaces. -/
theorem toShHom_hom_comp_π :
    f.toShHom.hom ≫ (Limits.coequalizer.π f g).toShHom.hom =
      g.toShHom.hom ≫ (Limits.coequalizer.π f g).toShHom.hom :=
  congrArg (fun m : X ⟶ Limits.coequalizer f g => m.toShHom.hom)
    (Limits.coequalizer.condition f g)

/-- The two pullbacks of `π⁻¹ V` along the legs are the same open. -/
theorem preimage_coequalizer_π_eq (V : Opens (Limits.coequalizer f g).toTopCat) :
    (Opens.map g.toShHom.hom.base).obj
        ((Opens.map (Limits.coequalizer.π f g).toShHom.hom.base).obj V) =
      (Opens.map f.toShHom.hom.base).obj
        ((Opens.map (Limits.coequalizer.π f g).toShHom.hom.base).obj V) := by
  rw [← Opens.map_comp_obj, ← Opens.map_comp_obj, ← PresheafedSpace.comp_base,
    ← PresheafedSpace.comp_base, toShHom_hom_comp_π]

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
/-- **Every open of the coequalizer is the comparison isomorphism's image of one downstairs.** The
`rfl` pattern this supports is what makes the transport below definitional rather than an
`eqToHom` chase. -/
theorem exists_map_coequalizerIso_hom_base_obj (V : Opens (Limits.coequalizer f g).toTopCat) :
    ∃ V' : Opens (Limits.coequalizer f.toShHom.hom g.toShHom.hom).carrier,
      (Opens.map (coequalizerIsoPresheafedSpace f g).hom.base).obj V' = V :=
  ⟨(Opens.map (coequalizerIsoPresheafedSpace f g).inv.base).obj V, by
    rw [← Opens.map_comp_obj, ← PresheafedSpace.comp_base,
      (coequalizerIsoPresheafedSpace f g).hom_inv_id]
    simp⟩

set_option linter.style.setOption false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The sections of a coequalizer of locally ringed spaces, exactly.** A section `s` of `Y` over
`π⁻¹ V` is the pullback of a section of the coequalizer over `V` **if and only if** its two
pullbacks along the legs `f` and `g` agree.

The proof is the presheafed space statement transported along `coequalizerIsoPresheafedSpace`:
`obtain ⟨V', rfl⟩` puts `V` in the shape `exists_c_app_eq_iff_of_iso` wants, and the projection is
rewritten inside a `∀`-statement, which is type-correct because the equality of opens is one of
its binders. -/
theorem exists_c_app_eq_iff_c_app_eq (V : Opens (Limits.coequalizer f g).toTopCat)
    (h : (Opens.map g.toShHom.hom.base).obj
        ((Opens.map (Limits.coequalizer.π f g).toShHom.hom.base).obj V) =
      (Opens.map f.toShHom.hom.base).obj
        ((Opens.map (Limits.coequalizer.π f g).toShHom.hom.base).obj V))
    (s : ToType (Y.presheaf.obj
      (op ((Opens.map (Limits.coequalizer.π f g).toShHom.hom.base).obj V)))) :
    (∃ t, ((Limits.coequalizer.π f g).toShHom.hom.c.app (op V)) t = s) ↔
      (f.toShHom.hom.c.app
          (op ((Opens.map (Limits.coequalizer.π f g).toShHom.hom.base).obj V))) s =
        (X.presheaf.map (eqToHom (congrArg op h)))
          ((g.toShHom.hom.c.app
            (op ((Opens.map (Limits.coequalizer.π f g).toShHom.hom.base).obj V))) s) := by
  obtain ⟨V', rfl⟩ := exists_map_coequalizerIso_hom_base_obj f g V
  refine Iff.trans (PresheafedSpace.exists_c_app_eq_iff_of_iso
    (Limits.coequalizer.π f g).toShHom.hom (coequalizerIsoPresheafedSpace f g) V' s).symm ?_
  have H := fun h' s' => PresheafedSpace.exists_c_app_eq_iff_c_app_eq
    f.toShHom.hom g.toShHom.hom V' h' s'
  rw [← π_comp_coequalizerIsoPresheafedSpace_hom f g] at H
  exact H h s

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
/-- **A section of a coequalizer of locally ringed spaces is determined by its pullback along the
projection.** The injectivity half, transported the same way. -/
theorem injective_coequalizer_π_c_app (V : Opens (Limits.coequalizer f g).toTopCat) :
    Function.Injective ((Limits.coequalizer.π f g).toShHom.hom.c.app (op V)) := by
  obtain ⟨V', rfl⟩ := exists_map_coequalizerIso_hom_base_obj f g V
  refine PresheafedSpace.injective_c_app_of_iso _ (coequalizerIsoPresheafedSpace f g) V' ?_
  rw [π_comp_coequalizerIsoPresheafedSpace_hom]
  exact PresheafedSpace.injective_coequalizer_π_c_app _ _ _

/-- **The coequalizer of `f` with itself has exactly the sections of `Y`.** Both halves are used,
and the condition of the descent criterion is satisfied by every section when the two legs
coincide. The universal property predicts this independently — `coequalizer f f` is `Y` — so it is
the check that the description above is not vacuous. -/
theorem bijective_coequalizer_self_π_c_app (V : Opens (Limits.coequalizer f f).toTopCat) :
    Function.Bijective ((Limits.coequalizer.π f f).toShHom.hom.c.app (op V)) := by
  refine ⟨injective_coequalizer_π_c_app f f V, fun s => ?_⟩
  refine (exists_c_app_eq_iff_c_app_eq f f V (preimage_coequalizer_π_eq f f V) s).mpr ?_
  simp

end AlgebraicGeometry.LocallyRingedSpace

namespace CategoryTheory

open AlgebraicGeometry

variable {G : Type u} [Monoid G] {X : LocallyRingedSpace.{u}} (a : G →* Aut X)
variable [Limits.HasCoproduct fun _ : G => X]
  [Limits.HasCoequalizer (actionQuotientLeft a) (actionQuotientRight G X)]

/-- **The sections of an action quotient are the equalised sections.** The specialisation of
`AlgebraicGeometry.LocallyRingedSpace.exists_c_app_eq_iff_c_app_eq` to
`CategoryTheory.actionQuotientπ`, which is the projection the stalk lemma for a free, properly
discontinuous action is about. It holds by definition, `actionQuotient a` being the coequalizer of
the two legs.

Turning the right-hand side into "invariant under every `a g`" is a further step, and is not done
here; see the module docstring. -/
theorem exists_actionQuotientπ_c_app_eq_iff (V : Opens (actionQuotient a).toTopCat)
    (h : (Opens.map (actionQuotientRight G X).toShHom.hom.base).obj
        ((Opens.map (actionQuotientπ a).toShHom.hom.base).obj V) =
      (Opens.map (actionQuotientLeft a).toShHom.hom.base).obj
        ((Opens.map (actionQuotientπ a).toShHom.hom.base).obj V))
    (s : ToType (X.presheaf.obj (op ((Opens.map (actionQuotientπ a).toShHom.hom.base).obj V)))) :
    (∃ t, ((actionQuotientπ a).toShHom.hom.c.app (op V)) t = s) ↔
      ((actionQuotientLeft a).toShHom.hom.c.app
          (op ((Opens.map (actionQuotientπ a).toShHom.hom.base).obj V))) s =
        ((∐ fun _ : G => X).presheaf.map (eqToHom (congrArg op h)))
          (((actionQuotientRight G X).toShHom.hom.c.app
            (op ((Opens.map (actionQuotientπ a).toShHom.hom.base).obj V))) s) :=
  LocallyRingedSpace.exists_c_app_eq_iff_c_app_eq _ _ V h s

end CategoryTheory
