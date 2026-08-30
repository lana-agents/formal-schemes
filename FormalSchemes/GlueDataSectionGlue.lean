import FormalSchemes.GlueDataSectionExt
import FormalSchemes.ActionInvariantExtension

set_option linter.style.header false

/-!
# Sections of a glued formal scheme glue, patch by patch

`AlgebraicGeometry.FormalScheme.GlueData.eq_of_ι_c_app_eq` (`FormalSchemes.GlueDataSectionExt`)
is the **separation** half of the sheaf axiom for a glued formal scheme: a section over an open `W`
is determined by its pullbacks along the patch inclusions `D.ι i`. Its module docstring records
that it says nothing about which patch-wise families arise that way. This file supplies the
**existence** half, and with it the description of `Γ (X, W)` as the compatible families.

The tool is `TopCat.Sheaf.existsUnique_gluing'`, applied to the glued space's own structure sheaf
along the cover of `W` by the parts `W ⊓ (range of D.ι i)`. The tree's only gluing statement so
far, `TopCat.Sheaf.existsUnique_gluing_of_disjoint'` (`FormalSchemes.DisjointGluing`), requires
pairwise-**disjoint** opens, which the patches of a chain are not; nothing here needs disjointness.

## What is here

* `AlgebraicGeometry.FormalScheme.GlueData.ιCover`: the part of `W` that the patch `i` sees, and
  `AlgebraicGeometry.FormalScheme.GlueData.le_iSup_ιCover`, that these cover `W` — the only place
  `AlgebraicGeometry.FormalScheme.GlueData.ι_jointly_surjective` is used.
* `AlgebraicGeometry.FormalScheme.GlueData.ιSectionIso`: **the dictionary.** Sections of the patch
  `D.U i` over `(D.ι i)⁻¹ W` and sections of the glued space over `ιCover W i` are the same ring,
  because `D.ι i` is an open immersion with that range. This is what lets a patch-wise family be
  fed to a sheaf-theoretic gluing statement, which knows only about opens of the glued space.
* `AlgebraicGeometry.FormalScheme.GlueData.ιSectionIso_hom_c_app`: the dictionary carries the
  pullback of a global-ish section to its restriction — the compatibility of the two descriptions.
* `AlgebraicGeometry.FormalScheme.GlueData.existsUnique_ι_c_app_eq`: **the existence half.** A
  patch-wise family whose transported sections agree on overlaps is the family of pullbacks of a
  unique section over `W`.
* `AlgebraicGeometry.FormalScheme.GlueData.exists_ι_c_app_eq_iff_isCompatible`: the two halves
  together — a family comes from a section **iff** it is compatible.

## What this does not do

It does not translate the compatibility hypothesis into the glue datum's own transition data
`D.f i j` and `D.t i j`. `TopCat.Presheaf.IsCompatible` is stated for the transported family, on
opens of the glued space; turning it into a condition on the patches alone is a further step and is
not attempted here.

## References

* [The Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA) — gluing sheaves.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
-/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry CategoryTheory.Limits
open TopCat.Presheaf

noncomputable section

namespace AlgebraicGeometry.FormalScheme

variable (D : FormalScheme.GlueData.{u})

/-! ### The cover of an open by the patch ranges -/

/-- **The part of `W` that the patch `i` sees**: the intersection of `W` with the range of the
patch inclusion `D.ι i`. These cover `W` (`GlueData.le_iSup_ιCover`) and the `c`-component of
`D.ι i` is an isomorphism over each of them (`GlueData.isIso_c_app_ιCover`), which is the whole
reason this is the right cover to glue along. -/
def GlueData.ιCover (W : Opens (D.gluedFormalScheme).toLocallyRingedSpace)
    (i : D.toLocallyRingedSpaceGlueData.J) :
    Opens (D.gluedFormalScheme).toLocallyRingedSpace :=
  W ⊓ (PresheafedSpace.IsOpenImmersion.opensFunctor (D.ι i).toHom).obj ⊤

theorem GlueData.ιCover_le (W : Opens (D.gluedFormalScheme).toLocallyRingedSpace)
    (i : D.toLocallyRingedSpaceGlueData.J) : D.ιCover W i ≤ W := inf_le_left

/-- **The patch does not see the difference between `W` and the part of `W` it meets.** The
preimage of the range of `D.ι i` is everything, so intersecting with it changes nothing upstairs.
This equality of opens is what the dictionary `GlueData.ιSectionIso` is built on. -/
theorem GlueData.map_ιCover (W : Opens (D.gluedFormalScheme).toLocallyRingedSpace)
    (i : D.toLocallyRingedSpaceGlueData.J) :
    (Opens.map (D.ι i).base).obj (D.ιCover W i) = (Opens.map (D.ι i).base).obj W := by
  ext y
  exact ⟨fun h => h.1, fun h => ⟨h, y, trivial, rfl⟩⟩

/-- **The `c`-component of a patch inclusion is invertible over the part of `W` it meets.**
`PresheafedSpace.IsOpenImmersion.c_iso'`, whose hypothesis is
`AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.inf_opensFunctor_top`
(`FormalSchemes.GlueDataSectionExt`).

This is a `theorem` and not an `instance` on purpose: the `IsIso` it produces is stated at the
locally ringed space spelling `(D.ι i).c`, and instance search does not see through
`AlgebraicGeometry.LocallyRingedSpace.Hom.toShHom` to the presheafed-space spelling that
`PresheafedSpace.IsOpenImmersion.c_iso'` registers. Every use below introduces it with `haveI`. -/
theorem GlueData.isIso_c_app_ιCover (W : Opens (D.gluedFormalScheme).toLocallyRingedSpace)
    (i : D.toLocallyRingedSpaceGlueData.J) :
    IsIso ((D.ι i).c.app (op (D.ιCover W i))) :=
  PresheafedSpace.IsOpenImmersion.c_iso' (D.ι i).toHom _
    (PresheafedSpace.IsOpenImmersion.inf_opensFunctor_top (D.ι i).toHom W)

/-- **The parts cover.** Every point of `W` lies on some patch, by
`AlgebraicGeometry.FormalScheme.GlueData.ι_jointly_surjective`; this is the covering hypothesis of
`TopCat.Sheaf.existsUnique_gluing'`. -/
theorem GlueData.le_iSup_ιCover (W : Opens (D.gluedFormalScheme).toLocallyRingedSpace) :
    W ≤ ⨆ i, D.ιCover W i := by
  intro x hx
  obtain ⟨i, y, rfl⟩ := D.ι_jointly_surjective x
  exact Opens.mem_iSup.2 ⟨i, hx, y, trivial, rfl⟩

/-! ### The dictionary between patch sections and sections of the glued space -/

/-- **Sections of the patch over `(D.ι i)⁻¹ W` are sections of the glued space over the part of
`W` that the patch meets.** The two rings are identified by the `c`-component of `D.ι i`, which is
an isomorphism there, after the harmless rewrite `GlueData.map_ιCover` of the open upstairs.

It is stated as an `Iso` rather than as an `inv`-of-a-morphism so that
`CategoryTheory.Iso.inv_hom_id_apply` is available; the `IsIso` instance is not found by search
(see `GlueData.isIso_c_app_ιCover`), so an anonymous constructor over `inv` would have to carry a
`haveI` into every consumer. -/
def GlueData.ιSectionIso (W : Opens (D.gluedFormalScheme).toLocallyRingedSpace)
    (i : D.toLocallyRingedSpaceGlueData.J) :
    (D.toLocallyRingedSpaceGlueData.U i).presheaf.obj (op ((Opens.map (D.ι i).base).obj W)) ≅
      (D.gluedFormalScheme).presheaf.obj (op (D.ιCover W i)) :=
  haveI := D.isIso_c_app_ιCover W i
  (D.toLocallyRingedSpaceGlueData.U i).presheaf.mapIso (eqToIso (D.map_ιCover W i)).op ≪≫
    (asIso ((D.ι i).c.app (op (D.ιCover W i)))).symm

theorem GlueData.injective_ιSectionIso (W : Opens (D.gluedFormalScheme).toLocallyRingedSpace)
    (i : D.toLocallyRingedSpaceGlueData.J) :
    Function.Injective (D.ιSectionIso W i).hom.hom :=
  ConcreteCategory.injective_of_mono_of_preservesPullback _

/-- **The dictionary turns a pullback into a restriction.** For a section `s` over `W`, the
transport of its pullback `(D.ι i)^* s` is the restriction of `s` to the part of `W` that the
patch `i` meets.

This is the one compatibility the whole file rests on, and it is naturality of `(D.ι i).c` along
`ιCover W i ≤ W` — read on elements, then cancelled against the isomorphism. The pushforward's
structure map and the `eqToIso` of `GlueData.map_ιCover` are two morphisms between the same pair
of opens, hence equal, which is the `Subsingleton.elim` step. -/
theorem GlueData.ιSectionIso_hom_c_app (W : Opens (D.gluedFormalScheme).toLocallyRingedSpace)
    (i : D.toLocallyRingedSpaceGlueData.J)
    (s : (D.gluedFormalScheme).presheaf.obj (op W)) :
    (D.ιSectionIso W i).hom.hom (((D.ι i).c.app (op W)).hom s) =
      (D.gluedFormalScheme).presheaf.map (homOfLE (D.ιCover_le W i)).op s := by
  haveI := D.isIso_c_app_ιCover W i
  apply ConcreteCategory.injective_of_mono_of_preservesPullback
    ((D.ι i).c.app (op (D.ιCover W i)))
  have hnat := (D.ι i).c.naturality (homOfLE (D.ιCover_le W i)).op
  have key : ∀ u : (D.gluedFormalScheme).presheaf.obj (op W),
      ((D.ι i).c.app (op (D.ιCover W i))).hom
          (((D.gluedFormalScheme).presheaf.map (homOfLE (D.ιCover_le W i)).op).hom u) =
        ((((D.ι i).base _* (D.toLocallyRingedSpaceGlueData.U i).presheaf)).map
          (homOfLE (D.ιCover_le W i)).op).hom (((D.ι i).c.app (op W)).hom u) := fun u =>
    congrArg (fun φ : (D.gluedFormalScheme).presheaf.obj (op W) ⟶ _ => φ.hom u) hnat
  rw [key]
  have hL : (D.ιSectionIso W i).hom =
      ((D.toLocallyRingedSpaceGlueData.U i).presheaf.mapIso
        (eqToIso (D.map_ιCover W i)).op).hom ≫
          (asIso ((D.ι i).c.app (op (D.ιCover W i)))).inv := rfl
  have hmap : (((D.ι i).base _* (D.toLocallyRingedSpaceGlueData.U i).presheaf)).map
      (homOfLE (D.ιCover_le W i)).op =
      (D.toLocallyRingedSpaceGlueData.U i).presheaf.map
        (eqToIso (D.map_ιCover W i)).op.hom :=
    congrArg (D.toLocallyRingedSpaceGlueData.U i).presheaf.map (Subsingleton.elim _ _)
  rw [hmap, hL, ConcreteCategory.comp_apply]
  exact (asIso ((D.ι i).c.app (op (D.ιCover W i)))).inv_hom_id_apply _

/-! ### The existence half -/

/-- **The family of pullbacks of a section is compatible.** Immediate from
`GlueData.ιSectionIso_hom_c_app`: the transported family is the family of restrictions of a single
section, and two successive restrictions depend only on the composite inclusion
(`AlgebraicGeometry.LocallyRingedSpace.presheaf_map_comp_apply` and
`AlgebraicGeometry.LocallyRingedSpace.presheaf_map_congr`,
`FormalSchemes.ActionInvariantExtension`). -/
theorem GlueData.isCompatible_c_app
    (W : Opens (D.gluedFormalScheme).toLocallyRingedSpace)
    (s : (D.gluedFormalScheme).presheaf.obj (op W)) :
    IsCompatible (D.gluedFormalScheme).presheaf (D.ιCover W)
      (fun i => (D.ιSectionIso W i).hom.hom (((D.ι i).c.app (op W)).hom s)) := by
  intro i j
  beta_reduce
  rw [D.ιSectionIso_hom_c_app, D.ιSectionIso_hom_c_app]
  exact (LocallyRingedSpace.presheaf_map_comp_apply _ _ _ s).trans
    ((ConcreteCategory.congr_hom (LocallyRingedSpace.presheaf_map_congr _ _ _) s).trans
      (LocallyRingedSpace.presheaf_map_comp_apply _ _ _ s).symm)

/-- **A compatible patch-wise family is the family of pullbacks of a unique section.** This is the
existence half of the sheaf axiom for a glued formal scheme, at an arbitrary open `W`.

Existence is `TopCat.Sheaf.existsUnique_gluing'` on the glued space's structure sheaf, along the
cover `GlueData.le_iSup_ιCover`, with the family transported by `GlueData.ιSectionIso`; the
identification of the glued section's pullbacks with the given family is
`GlueData.ιSectionIso_hom_c_app` plus injectivity of the dictionary. Uniqueness is
`AlgebraicGeometry.FormalScheme.GlueData.eq_of_ι_c_app_eq` (`FormalSchemes.GlueDataSectionExt`)
rather than the uniqueness clause of the Mathlib statement — the two are the same fact, and citing
the separation half keeps the two halves visibly complementary.

No disjointness hypothesis, in contrast with
`TopCat.Sheaf.existsUnique_gluing_of_disjoint'` (`FormalSchemes.DisjointGluing`). -/
theorem GlueData.existsUnique_ι_c_app_eq
    (W : Opens (D.gluedFormalScheme).toLocallyRingedSpace)
    (t : ∀ i, (D.toLocallyRingedSpaceGlueData.U i).presheaf.obj
      (op ((Opens.map (D.ι i).base).obj W)))
    (h : IsCompatible (D.gluedFormalScheme).presheaf (D.ιCover W)
      (fun i => (D.ιSectionIso W i).hom.hom (t i))) :
    ∃! s : (D.gluedFormalScheme).presheaf.obj (op W),
      ∀ i, ((D.ι i).c.app (op W)).hom s = t i := by
  obtain ⟨s, hs, -⟩ := (D.gluedFormalScheme).toSheafedSpace.sheaf.existsUnique_gluing'
    (D.ιCover W) W (fun i => homOfLE (D.ιCover_le W i)) (D.le_iSup_ιCover W) _ h
  refine ⟨s, fun i => ?_, fun s' hs' => ?_⟩
  · refine D.injective_ιSectionIso W i ?_
    rw [D.ιSectionIso_hom_c_app W i s]
    exact hs i
  · refine FormalScheme.GlueData.eq_of_ι_c_app_eq D W s' s (fun i => ?_)
    rw [hs' i]
    refine (D.injective_ιSectionIso W i ?_).symm
    rw [D.ιSectionIso_hom_c_app W i s]
    exact hs i

/-- **`Γ (X, W)` is exactly the compatible patch-wise families.** The two halves of the sheaf
axiom, in one statement: a family of sections of the patches over the preimages of `W` is the
family of pullbacks of a section of the glued space **iff** its transports agree on overlaps.

The forward direction is `GlueData.isCompatible_c_app`, the reverse
`GlueData.existsUnique_ι_c_app_eq`. -/
theorem GlueData.exists_ι_c_app_eq_iff_isCompatible
    (W : Opens (D.gluedFormalScheme).toLocallyRingedSpace)
    (t : ∀ i, (D.toLocallyRingedSpaceGlueData.U i).presheaf.obj
      (op ((Opens.map (D.ι i).base).obj W))) :
    (∃ s : (D.gluedFormalScheme).presheaf.obj (op W),
        ∀ i, ((D.ι i).c.app (op W)).hom s = t i) ↔
      IsCompatible (D.gluedFormalScheme).presheaf (D.ιCover W)
        (fun i => (D.ιSectionIso W i).hom.hom (t i)) := by
  refine ⟨fun ⟨s, hs⟩ => ?_, fun h => ?_⟩
  · have := D.isCompatible_c_app W s
    simpa only [hs] using this
  · obtain ⟨s, hs, -⟩ := D.existsUnique_ι_c_app_eq W t h
    exact ⟨s, hs⟩

end AlgebraicGeometry.FormalScheme
