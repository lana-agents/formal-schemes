import FormalSchemes.ActionInvariantExtension
import FormalSchemes.ActionQuotientRestrictSections

set_option linter.style.header false

/-!
# The restriction of an action quotient to an open of the quotient is an action quotient

Let `a : G →* Aut X` act on a locally ringed space, let `π : X ⟶ Q` exhibit `Q` as the quotient
(`CategoryTheory.IsActionQuotient`), and let `V` be an open of `Q`. The open `π ⁻¹ V` is invariant,
`a` restricts to it (`AlgebraicGeometry.LocallyRingedSpace.restrictAction`), and
`AlgebraicGeometry.LocallyRingedSpace.restrictπ` is the restricted projection `X|_{π ⁻¹ V} ⟶ Q|_V`.
This file proves that the restricted projection is again an action quotient, in
`AlgebraicGeometry.LocallyRingedSpace` itself. That is the statement three deliveries on the
node-chart row each named as missing, `FormalSchemes.ActionQuotientRestrict` proved after
`AlgebraicGeometry.LocallyRingedSpace.forgetToTop`, and
`FormalSchemes.ActionQuotientRestrictSections` supplied the section-level input for.

## The route

Not by building the descent of an invariant morphism by hand. `X|_{π ⁻¹ V}` already has a quotient,
namely the coequalizer `CategoryTheory.actionQuotient` of the restricted action, so the restricted
projection induces a comparison morphism
`AlgebraicGeometry.LocallyRingedSpace.restrictπComparison` out of it, and the whole content is that
the comparison is an isomorphism; the universal property then transports along it
(`CategoryTheory.IsActionQuotient.ofIso`). The two halves of "isomorphism" are exactly the two
halves the predecessors left:

* the **base map** is an isomorphism because both projections are action quotients *in `TopCat`* —
  `AlgebraicGeometry.LocallyRingedSpace.isActionQuotient_forgetToTop` for the coequalizer and
  `AlgebraicGeometry.LocallyRingedSpace.isActionQuotient_forgetToTop_restrictπ` for the restriction
  — so the comparison is the canonical isomorphism of
  `CategoryTheory.IsActionQuotient.uniqueUpToIso`, by uniqueness of the descent;
* the **comparison maps on sections** are isomorphisms because both projections have the same image
  and are injective there: the coequalizer side is
  `CategoryTheory.exists_actionQuotientπ_c_app_eq_iff_forall` transported by
  `CategoryTheory.IsActionQuotient.exists_c_app_eq_iff_forall`, and the restriction side is
  `AlgebraicGeometry.LocallyRingedSpace.exists_c_app_restrictπ_eq_iff_forall`.

Bringing those two descriptions together needs the translation that
`FormalSchemes.ActionQuotientRestrictSections` deliberately avoided and did not supply: its
statements are about sections of `X` and invariance under `a`, and the coequalizer's are about
sections of `X|_{π ⁻¹ V}` and invariance under
`AlgebraicGeometry.LocallyRingedSpace.restrictAction`. That translation is
`AlgebraicGeometry.LocallyRingedSpace.isInvariantSection_ofRestrict_c_app_iff` below, and it is the
one genuinely new piece of bookkeeping in this file.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.isActionQuotient_restrictπ`: **the headline.** For any
  action quotient `π : X ⟶ Q` and any open `V` of `Q`, the restricted projection
  `X|_{π ⁻¹ V} ⟶ Q|_V` is an action quotient for the restricted action.
* `AlgebraicGeometry.LocallyRingedSpace.restrictπComparison` and
  `AlgebraicGeometry.LocallyRingedSpace.isIso_restrictπComparison`: the comparison morphism from
  the coequalizer of the restricted action, and that it is an isomorphism; with its two halves
  `AlgebraicGeometry.LocallyRingedSpace.isIso_base_restrictπComparison` and
  `AlgebraicGeometry.LocallyRingedSpace.isIso_c_app_restrictπComparison`.
* `AlgebraicGeometry.LocallyRingedSpace.isInvariantSection_ofRestrict_c_app_iff`: **the
  translation.** A section of `X` over an invariant open `W ≤ U` is invariant under `a` exactly
  when its image in `X|_U` is invariant under the restricted action.
* `AlgebraicGeometry.LocallyRingedSpace.isInvariantSection_iff_forall`: the tree's
  `AlgebraicGeometry.LocallyRingedSpace.IsInvariantSection`, whose equality of opens is a
  hypothesis binder, read off a single `AlgebraicGeometry.LocallyRingedSpace.IsInvariantOpen`
  witness — the shape in which every sections description on the tree states its right-hand side.
* `AlgebraicGeometry.LocallyRingedSpace.exists_c_app_restrictπ_eq_iff_isInvariantSection`: the
  sections description of the restricted projection, phrased on `X|_{π ⁻¹ V}` and on invariance
  under the restricted action — the form the comparison consumes, and the form a successor working
  inside the restriction wants.
* `AlgebraicGeometry.LocallyRingedSpace.exists_le_preimage_eq`: every open of `Q|_V` is the
  preimage of an open of `Q` contained in `V`, which is what lets the `W ≤ V` statements of
  `FormalSchemes.ActionQuotientRestrictSections` be applied at an arbitrary open of the
  restriction.
* `AlgebraicGeometry.LocallyRingedSpace.isIso_of_isIso_base_of_isIso_c_app`: a morphism of locally
  ringed spaces with an invertible base map and invertible comparison maps is an isomorphism.

## What is *not* proved here

**Anything about the node chart, the Tate curve, or `AlgebraicGeometry.FormalScheme`.** This file
is at `AlgebraicGeometry.LocallyRingedSpace` level and names no ring, ideal, spectrum or formal
scheme. It produces no chart at the node locus and settles nothing on the node-chart row; the
invariant-sections route to a chart now has its restriction step, and the geometric step that route
needs is a different problem.

**Any statement about `AlgebraicGeometry.FormalScheme.LocallyFG`.** The measurement asked for by
the row is in the implementation notes.

## Implementation notes

**`AlgebraicGeometry.FormalScheme.LocallyFG` has no bearing on anything here, and the file measures
that rather than asserting it**: no declaration below mentions `AlgebraicGeometry.FormalScheme`, and
the import closure of this leaf is 82 project modules, containing neither
`FormalSchemes.OpenFormalSubscheme` — where `AlgebraicGeometry.FormalScheme.restrictOpen` and its
`LocallyFG` hypothesis live — nor `FormalSchemes.ActionQuotientFormalScheme`. This confirms at a
third and larger closure what `FormalSchemes.ActionQuotientRestrict` and
`FormalSchemes.ActionQuotientRestrictSections` measured at 72 and 77, and it does **not** contradict
`FormalSchemes.ActionQuotientFormalScheme`'s "not removable" paragraph, which is about producing an
affine chart inside a separating open and is correct about its own subject.

`CategoryTheory.IsActionQuotient.ofIso` is **not** here: it is a statement of the categorical
interface and it is in `FormalSchemes.ActionQuotient`, beside
`CategoryTheory.IsActionQuotient.uniqueUpToIso`, which it generalises in the direction this file
needs. That file has a reverse closure of 77 modules, so the placement is not free; it is chosen
because a general categorical lemma parked in a `AlgebraicGeometry.LocallyRingedSpace` leaf is the
stranding the node-chart rows were filed about, and because `uniqueUpToIso` without `ofIso` is an
interface with a hole in it.

**`AlgebraicGeometry.LocallyRingedSpace.isIso_of_isIso_base_of_isIso_c_app` overlaps with a chain
that is already written out inline**, in `FormalSchemes.CofinalSheafComparisonIso`'s
`AlgebraicGeometry.Spf.isIso_locallyRingedSpaceMapId`: `NatIso.isIso_of_isIso_app`, then
`AlgebraicGeometry.PresheafedSpace.isIso_of_components`, then two reflections. It is **not**
rerouted through this one: the two modules are incomparable in the import order — this leaf's
closure is 82 modules and does not contain `FormalSchemes.CofinalSheafComparisonIso`, whose own
closure is 37 and does not contain this leaf's imports — so removing the overlap means rehoming one
of them, which is a dedup question and not this file's.

Every transport between two opens that are equal but not definitionally so is discharged by
`AlgebraicGeometry.LocallyRingedSpace.presheaf_map_congr`
(`FormalSchemes.ActionInvariantExtension`), `Opens` being a thin category.

That import is also where the predicate `AlgebraicGeometry.LocallyRingedSpace.IsInvariantSection`
comes from, rather than a second one being defined here; together the two cost four modules of
closure. **The price of reusing it is the group hypothesis**: the restriction constructions of
`FormalSchemes.ActionQuotientRestrict` are stated for a monoid, and everything in the invariance
section below would be too, but `IsInvariantSection` is declared under `[Group G]`. Nothing
consumes a monoid form — the file's own theorems need a group from
`AlgebraicGeometry.LocallyRingedSpace.isActionQuotient_forgetToTop` onwards — so the hypothesis is
carried rather than the predicate generalised; generalising it is a one-line change in
`FormalSchemes.ActionInvariantExtension`, whose reverse closure is 49 modules, and it should be
made when something wants it and not before.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
* [The Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ).
-/

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.LocallyRingedSpace

namespace AlgebraicGeometry.LocallyRingedSpace

section Basic

/-- **Every open of a restriction comes from an open below the restricting one.** The witness is
the image of `O` under the open-map functor of the embedding, which is contained in `V` because
every point of it lies in `V`, and pulls back to `O` because the embedding is injective. -/
theorem exists_le_preimage_eq (Y : LocallyRingedSpace.{u}) (V : Opens Y.toTopCat)
    (O : Opens (Y.restrict V.isOpenEmbedding).toTopCat) :
    ∃ W : Opens Y.toTopCat, W ≤ V ∧
      (Opens.map (Y.ofRestrict V.isOpenEmbedding).base).obj W = O := by
  refine ⟨V.isOpenEmbedding.isOpenMap.functor.obj O, ?_, ?_⟩
  · rintro _ ⟨y, _, rfl⟩
    exact y.2
  · ext y
    exact ⟨fun ⟨z, hz, hzy⟩ => (Subtype.val_injective hzy) ▸ hz, fun hy => ⟨y, hy, rfl⟩⟩

/-- **A morphism of locally ringed spaces with an invertible base map and invertible comparison
maps is an isomorphism.** `AlgebraicGeometry.PresheafedSpace.isIso_of_components` reflected back
along the two forgetful functors, both of which reflect isomorphisms. -/
theorem isIso_of_isIso_base_of_isIso_c_app {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    (hb : IsIso f.base) (hc : ∀ O : (Opens Y.toTopCat)ᵒᵖ, IsIso (f.c.app O)) : IsIso f := by
  haveI hb' : IsIso f.toShHom.hom.base := hb
  haveI hc' : ∀ O, IsIso (f.toShHom.hom.c.app O) := hc
  haveI : IsIso f.toShHom.hom.c := NatIso.isIso_of_isIso_app _
  haveI : IsIso f.toShHom.hom := PresheafedSpace.isIso_of_components _
  haveI : IsIso (SheafedSpace.forgetToPresheafedSpace.map
    (LocallyRingedSpace.forgetToSheafedSpace.map f)) := this
  haveI : IsIso (LocallyRingedSpace.forgetToSheafedSpace.map f) :=
    isIso_of_reflects_iso _ SheafedSpace.forgetToPresheafedSpace
  exact isIso_of_reflects_iso _ LocallyRingedSpace.forgetToSheafedSpace

end Basic

section Invariance

variable {G : Type v} [Group G] {X : LocallyRingedSpace.{u}} {a : G →* Aut X}
variable {U W : Opens X.toTopCat}

/-- **Invariance of a section, on an open already known to be invariant.**
`AlgebraicGeometry.LocallyRingedSpace.IsInvariantSection` (`FormalSchemes.ActionInvariantExtension`)
carries the equality of opens as a hypothesis binder, so that it can be discharged from whichever
proof of it a caller has; this reads it off a single `IsInvariantOpen` witness, which is the shape
in which `CategoryTheory.exists_actionQuotientπ_c_app_eq_iff_forall`,
`CategoryTheory.IsActionQuotient.exists_c_app_eq_iff_forall` and
`AlgebraicGeometry.LocallyRingedSpace.exists_c_app_restrictπ_eq_iff_forall` all state their
right-hand sides. Both directions are proof irrelevance and nothing else. -/
theorem isInvariantSection_iff_forall (hW : IsInvariantOpen a W)
    (s : ToType (X.presheaf.obj (op W))) :
    IsInvariantSection a s ↔
      ∀ g : G, ((a g).hom.c.app (op W)) s =
        (X.presheaf.map (eqToHom (congrArg op (hW g).symm))) s :=
  ⟨fun h g => h g (hW g).symm, fun h g _ => h g⟩

/-- **Invariance is carried along a transport between equal opens.** -/
theorem isInvariantSection_map_eqToHom_iff {A B : Opens X.toTopCat} (e : A = B)
    (s : ToType (X.presheaf.obj (op A))) :
    IsInvariantSection a ((X.presheaf.map (eqToHom (congrArg op e))) s) ↔
      IsInvariantSection a s := by
  subst e
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

/-- **The image of an invariant open in an invariant open subspace is invariant** for the restricted
action. This is `AlgebraicGeometry.LocallyRingedSpace.preimage_restrictOpensHom_eq` at `a g`,
followed by invariance of `W` itself; no hypothesis relating `W` and `U` is needed. -/
theorem IsInvariantOpen.map_ofRestrict (hU : IsInvariantOpen a U) (hW : IsInvariantOpen a W) :
    IsInvariantOpen (restrictAction a U hU)
      ((Opens.map (X.ofRestrict U.isOpenEmbedding).base).obj W) := by
  intro g
  rw [restrictAction_hom, ← preimage_restrictOpensHom_eq (a g).hom U U (hU.image_hom_subset g) W,
    hW g]

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
/-- **The translation between the two notions of invariance.** For invariant opens `W ≤ U`, a
section of `X` over `W` is invariant under `a` exactly when its image in `X|_U` is invariant under
the restricted action.

This is the statement `FormalSchemes.ActionQuotientRestrictSections` records as not proved
anywhere, and it is what lets the sections description of the restricted projection be compared
with the sections description of the coequalizer of the restricted action. The proof is
`AlgebraicGeometry.LocallyRingedSpace.restrictOpensHom_c_app` at `a g` — the restricted
automorphism read on sections — together with naturality of the comparison map of the inclusion;
`W ≤ U` enters only through
`AlgebraicGeometry.LocallyRingedSpace.isIso_ofRestrict_c_app`, which makes that comparison map
injective. -/
theorem isInvariantSection_ofRestrict_c_app_iff (hU : IsInvariantOpen a U)
    (hW : IsInvariantOpen a W) (hWU : W ≤ U) (s : ToType (X.presheaf.obj (op W))) :
    IsInvariantSection (restrictAction a U hU)
        (((X.ofRestrict U.isOpenEmbedding).c.app (op W)) s) ↔
      IsInvariantSection a s := by
  rw [isInvariantSection_iff_forall (hU.map_ofRestrict hW), isInvariantSection_iff_forall hW]
  refine forall_congr' fun g => ?_
  have h1 := ConcreteCategory.congr_hom
    (restrictOpensHom_c_app (a g).hom U U (hU.image_hom_subset g) W) s
  have h2 := ConcreteCategory.congr_hom
    ((X.ofRestrict U.isOpenEmbedding).c.naturality (eqToHom (congrArg op (hW g).symm))) s
  simp only [ConcreteCategory.comp_apply] at h1 h2
  have hcomp : ((TopCat.Presheaf.pushforward CommRingCat (X.ofRestrict U.isOpenEmbedding).base).obj
        (X.restrict U.isOpenEmbedding).presheaf).map (eqToHom (congrArg op (hW g).symm)) ≫
      (X.restrict U.isOpenEmbedding).presheaf.map (eqToHom (congrArg op
        (preimage_restrictOpensHom_eq (a g).hom U U (hU.image_hom_subset g) W))) =
      (X.restrict U.isOpenEmbedding).presheaf.map
        (eqToHom (congrArg op ((hU.map_ofRestrict hW) g).symm)) := by
    simp only [eqToHom_map, eqToHom_trans]
  have h3 := ConcreteCategory.congr_hom hcomp
    (((X.ofRestrict U.isOpenEmbedding).c.app (op W)) s)
  simp only [ConcreteCategory.comp_apply] at h3
  rw [← h2] at h3
  have hinj : Function.Injective
      (fun r : ToType (X.presheaf.obj (op ((Opens.map (a g).hom.base).obj W))) =>
        ((X.restrict U.isOpenEmbedding).presheaf.map (eqToHom (congrArg op
          (preimage_restrictOpensHom_eq (a g).hom U U (hU.image_hom_subset g) W))))
          (((X.ofRestrict U.isOpenEmbedding).c.app
            (op ((Opens.map (a g).hom.base).obj W))) r)) := by
    haveI : IsIso ((X.ofRestrict U.isOpenEmbedding).c.app
        (op ((Opens.map (a g).hom.base).obj W))) :=
      isIso_ofRestrict_c_app X U _ (by rw [hW g]; exact hWU)
    intro r₁ r₂ hr
    exact (ConcreteCategory.bijective_of_isIso _).1
      ((ConcreteCategory.bijective_of_isIso _).1 hr)
  constructor
  · intro hinv
    exact hinj ((h1.symm.trans hinv).trans h3.symm)
  · intro hinv
    rw [hinv] at h1
    exact h1.trans h3

end Invariance

section Quotient

variable {G : Type v} [Group G] [Small.{u} G] {X Q : LocallyRingedSpace.{u}}
variable {a : G →* Aut X} {π : X ⟶ Q}

/-- **The comparison morphism** from the coequalizer of the restricted action to `Q|_V`, induced by
the restricted projection through the universal property of the coequalizer. Everything below is
the proof that it is an isomorphism. -/
def restrictπComparison (h : IsActionQuotient a π) (V : Opens Q.toTopCat) :
    actionQuotient (restrictAction a _ (isInvariantOpen_preimage h.isInvariant V)) ⟶
      Q.restrict V.isOpenEmbedding :=
  (isActionQuotient_actionQuotientπ _).desc (restrictπ π V)
    (isActionInvariant_restrictπ h.isInvariant V)

/-- The comparison morphism factors the restricted projection through the coequalizer. -/
@[reassoc (attr := simp)]
theorem actionQuotientπ_comp_restrictπComparison (h : IsActionQuotient a π)
    (V : Opens Q.toTopCat) :
    actionQuotientπ (restrictAction a _ (isInvariantOpen_preimage h.isInvariant V)) ≫
        restrictπComparison h V = restrictπ π V :=
  (isActionQuotient_actionQuotientπ _).fac _ _

/-- The two ways of pulling an open of `Q|_V` back to `X|_{π ⁻¹ V}` — along the restricted
projection, and along the coequalizer projection after the comparison — give the same open. -/
theorem preimage_restrictπComparison (h : IsActionQuotient a π) (V : Opens Q.toTopCat)
    (O : Opens (Q.restrict V.isOpenEmbedding).toTopCat) :
    (Opens.map (restrictπ π V).base).obj O =
      (Opens.map (actionQuotientπ (restrictAction a _
          (isInvariantOpen_preimage h.isInvariant V))).base).obj
        ((Opens.map (restrictπComparison h V).base).obj O) :=
  congrArg (fun m : _ ⟶ Q.restrict V.isOpenEmbedding => (Opens.map m.base).obj O)
    (actionQuotientπ_comp_restrictπComparison h V).symm

/-- **The factorisation read on sections.** Pulling a section of `Q|_V` back along the comparison
and then along the coequalizer projection is pulling it back along the restricted projection, up to
the transport of opens. -/
theorem restrictπComparison_c_app (h : IsActionQuotient a π) (V : Opens Q.toTopCat)
    (O : Opens (Q.restrict V.isOpenEmbedding).toTopCat) :
    (restrictπComparison h V).c.app (op O) ≫
        (actionQuotientπ (restrictAction a _ (isInvariantOpen_preimage h.isInvariant V))).c.app
          (op ((Opens.map (restrictπComparison h V).base).obj O)) =
      (restrictπ π V).c.app (op O) ≫
        (X.restrict ((Opens.map π.base).obj V).isOpenEmbedding).presheaf.map
          (eqToHom (congrArg op (preimage_restrictπComparison h V O))) := by
  have hfac : (actionQuotientπ (restrictAction a _
        (isInvariantOpen_preimage h.isInvariant V))).toShHom.hom ≫
      (restrictπComparison h V).toShHom.hom = (restrictπ π V).toShHom.hom :=
    congrArg (fun m : _ ⟶ Q.restrict V.isOpenEmbedding => m.toShHom.hom)
      (actionQuotientπ_comp_restrictπComparison h V)
  have hsq := PresheafedSpace.congr_app hfac (op O)
  rw [PresheafedSpace.comp_c_app] at hsq
  exact hsq.trans
    (congrArg (fun m => (restrictπ π V).c.app (op O) ≫ m) (presheaf_map_congr _ _ _))

/-- **The comparison morphism is an isomorphism on underlying spaces.** Both projections are action
quotients of topological spaces for the same action, so the comparison is the canonical isomorphism
between two quotients — `CategoryTheory.IsActionQuotient.uniqueUpToIso` — by uniqueness of the
descent. -/
theorem isIso_base_restrictπComparison (h : IsActionQuotient a π) (V : Opens Q.toTopCat) :
    IsIso (restrictπComparison h V).base := by
  have h1 := isActionQuotient_forgetToTop
    (isActionQuotient_actionQuotientπ (restrictAction a _ (isInvariantOpen_preimage
      h.isInvariant V)))
  have h2 := isActionQuotient_forgetToTop_restrictπ h V
  have he : forgetToTop.map (actionQuotientπ (restrictAction a _ (isInvariantOpen_preimage
        h.isInvariant V))) ≫ forgetToTop.map (restrictπComparison h V)
      = forgetToTop.map (restrictπ π V) := by
    rw [← Functor.map_comp]
    exact congrArg forgetToTop.map (actionQuotientπ_comp_restrictπComparison h V)
  have hkey : forgetToTop.map (restrictπComparison h V) = (h1.uniqueUpToIso h2).hom :=
    h1.uniq _ h2.isInvariant _ he
  have hb : (restrictπComparison h V).base = forgetToTop.map (restrictπComparison h V) := rfl
  rw [hb, hkey]
  infer_instance

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
/-- **The sections of `Q|_V` over `W`, described inside the restriction.** For an open `W ≤ V` of
`Q`, a section of `X|_{π ⁻¹ V}` over the preimage of `W` is the pullback of a section of `Q|_V`
exactly when it is invariant under the restricted action.

`AlgebraicGeometry.LocallyRingedSpace.exists_c_app_restrictπ_eq_iff_forall` is the same statement
phrased on `X` and on invariance under `a`; this is that statement moved inside the restriction by
`AlgebraicGeometry.LocallyRingedSpace.isInvariantSection_ofRestrict_c_app_iff`, which is the form
the comparison with the coequalizer needs and the form a successor working inside `X|_{π ⁻¹ V}`
will want. -/
theorem exists_c_app_restrictπ_eq_iff_isInvariantSection (h : IsActionQuotient a π)
    (V W : Opens Q.toTopCat) (hWV : W ≤ V)
    (t : ToType ((X.restrict ((Opens.map π.base).obj V).isOpenEmbedding).presheaf.obj
      (op ((Opens.map (restrictπ π V).base).obj
        ((Opens.map (Q.ofRestrict V.isOpenEmbedding).base).obj W))))) :
    (∃ r, ((restrictπ π V).c.app
        (op ((Opens.map (Q.ofRestrict V.isOpenEmbedding).base).obj W))) r = t) ↔
      IsInvariantSection (restrictAction a _ (isInvariantOpen_preimage h.isInvariant V)) t := by
  haveI hJiso : IsIso ((X.ofRestrict ((Opens.map π.base).obj V).isOpenEmbedding).c.app
      (op ((Opens.map π.base).obj W))) := isIso_ofRestrict_c_app X _ _ (fun x hx => hWV hx)
  obtain ⟨s, rfl⟩ : ∃ s, ((X.restrict ((Opens.map π.base).obj V).isOpenEmbedding).presheaf.map
      (eqToHom (congrArg op (preimage_restrictOpensHom_eq π ((Opens.map π.base).obj V) V
        (by rintro _ ⟨x, hx, rfl⟩; exact hx) W))))
      (((X.ofRestrict ((Opens.map π.base).obj V).isOpenEmbedding).c.app
        (op ((Opens.map π.base).obj W))) s) = t := by
    obtain ⟨v, hv⟩ := (ConcreteCategory.bijective_of_isIso
      ((X.restrict ((Opens.map π.base).obj V).isOpenEmbedding).presheaf.map
        (eqToHom (congrArg op (preimage_restrictOpensHom_eq π ((Opens.map π.base).obj V) V
          (by rintro _ ⟨x, hx, rfl⟩; exact hx) W))))).2 t
    obtain ⟨s, hs⟩ := (ConcreteCategory.bijective_of_isIso
      ((X.ofRestrict ((Opens.map π.base).obj V).isOpenEmbedding).c.app
        (op ((Opens.map π.base).obj W)))).2 v
    exact ⟨s, by rw [hs, hv]⟩
  rw [exists_c_app_restrictπ_eq_iff_forall h V W hWV s]
  refine (((isInvariantSection_map_eqToHom_iff
    (a := restrictAction a _ (isInvariantOpen_preimage h.isInvariant V))
    (preimage_restrictOpensHom_eq π ((Opens.map π.base).obj V) V
      (by rintro _ ⟨x, hx, rfl⟩; exact hx) W) _).trans
    (isInvariantSection_ofRestrict_c_app_iff (isInvariantOpen_preimage h.isInvariant V)
      (isInvariantOpen_preimage h.isInvariant W) (fun x hx => hWV hx) s)).trans
    (isInvariantSection_iff_forall (isInvariantOpen_preimage h.isInvariant W) s)).symm

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
/-- **The comparison morphism is an isomorphism on sections.** An arbitrary open of `Q|_V` is the
preimage of an open `W ≤ V` (`AlgebraicGeometry.LocallyRingedSpace.exists_le_preimage_eq`), and
over such an open the two projections have the same image — the invariant sections, by
`AlgebraicGeometry.LocallyRingedSpace.exists_c_app_restrictπ_eq_iff_isInvariantSection` on one side
and `CategoryTheory.IsActionQuotient.exists_c_app_eq_iff_forall` on the other — and both are
injective. -/
theorem isIso_c_app_restrictπComparison (h : IsActionQuotient a π) (V : Opens Q.toTopCat)
    (O : (Opens (Q.restrict V.isOpenEmbedding).toTopCat)ᵒᵖ) :
    IsIso ((restrictπComparison h V).c.app O) := by
  obtain ⟨O⟩ := O
  obtain ⟨W, hWV, rfl⟩ := exists_le_preimage_eq Q V O
  obtain ⟨E, hEiso, hsq, htrans⟩ :
      ∃ E, IsIso E ∧
        ((restrictπComparison h V).c.app
              (op ((Opens.map (Q.ofRestrict V.isOpenEmbedding).base).obj W)) ≫
            (actionQuotientπ (restrictAction a _
                (isInvariantOpen_preimage h.isInvariant V))).c.app
              (op ((Opens.map (restrictπComparison h V).base).obj
                ((Opens.map (Q.ofRestrict V.isOpenEmbedding).base).obj W)))
          = (restrictπ π V).c.app
              (op ((Opens.map (Q.ofRestrict V.isOpenEmbedding).base).obj W)) ≫ E) ∧
        ∀ v, IsInvariantSection (restrictAction a _ (isInvariantOpen_preimage h.isInvariant V))
              (E v) ↔
            IsInvariantSection (restrictAction a _
              (isInvariantOpen_preimage h.isInvariant V)) v :=
    ⟨_, inferInstance, restrictπComparison_c_app h V _,
      fun v => isInvariantSection_map_eqToHom_iff
        (a := restrictAction a _ (isInvariantOpen_preimage h.isInvariant V))
        (preimage_restrictπComparison h V
          ((Opens.map (Q.ofRestrict V.isOpenEmbedding).base).obj W)) v⟩
  haveI := hEiso
  have hRinj := (isActionQuotient_actionQuotientπ (restrictAction a _
      (isInvariantOpen_preimage h.isInvariant V))).injective_c_app
      ((Opens.map (restrictπComparison h V).base).obj
        ((Opens.map (Q.ofRestrict V.isOpenEmbedding).base).obj W))
  have hSinj := injective_c_app_restrictπ h V W hWV
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro x y hxy
    have h1 := ConcreteCategory.congr_hom hsq x
    have h2 := ConcreteCategory.congr_hom hsq y
    simp only [ConcreteCategory.comp_apply] at h1 h2
    refine hSinj ((ConcreteCategory.bijective_of_isIso E).1 ?_)
    rw [← h1, ← h2, hxy]
  · intro u
    have hinvw := (isInvariantSection_iff_forall (isInvariantOpen_preimage
      (isActionQuotient_actionQuotientπ (restrictAction a _
        (isInvariantOpen_preimage h.isInvariant V))).isInvariant _) _).mpr
      (((isActionQuotient_actionQuotientπ (restrictAction a _
        (isInvariantOpen_preimage h.isInvariant V))).exists_c_app_eq_iff_forall _ _).mp ⟨u, rfl⟩)
    obtain ⟨v, hv⟩ := (ConcreteCategory.bijective_of_isIso E).2
      (((actionQuotientπ (restrictAction a _ (isInvariantOpen_preimage h.isInvariant V))).c.app
        (op ((Opens.map (restrictπComparison h V).base).obj
          ((Opens.map (Q.ofRestrict V.isOpenEmbedding).base).obj W)))) u)
    rw [← hv] at hinvw
    obtain ⟨t, ht⟩ := (exists_c_app_restrictπ_eq_iff_isInvariantSection h V W hWV v).mpr
      ((htrans v).mp hinvw)
    refine ⟨t, hRinj ?_⟩
    have h1 := ConcreteCategory.congr_hom hsq t
    simp only [ConcreteCategory.comp_apply] at h1
    rw [ht] at h1
    exact h1.trans hv

/-- **The comparison morphism is an isomorphism.** -/
theorem isIso_restrictπComparison (h : IsActionQuotient a π) (V : Opens Q.toTopCat) :
    IsIso (restrictπComparison h V) :=
  isIso_of_isIso_base_of_isIso_c_app _ (isIso_base_restrictπComparison h V)
    (isIso_c_app_restrictπComparison h V)

/-- **The restriction of an action quotient to an open of the quotient is an action quotient.** For
`π : X ⟶ Q` exhibiting `Q` as `X / G` and an open `V` of `Q`, the restricted projection
`X|_{π ⁻¹ V} ⟶ Q|_V` exhibits `Q|_V` as the quotient of `X|_{π ⁻¹ V}` by the restricted action.

The universal property is transported from the coequalizer of the restricted action along the
comparison isomorphism, by `CategoryTheory.IsActionQuotient.ofIso`. -/
def isActionQuotient_restrictπ (h : IsActionQuotient a π) (V : Opens Q.toTopCat) :
    IsActionQuotient (restrictAction a _ (isInvariantOpen_preimage h.isInvariant V))
      (restrictπ π V) :=
  haveI := isIso_restrictπComparison h V
  (isActionQuotient_actionQuotientπ _).ofIso (asIso (restrictπComparison h V))
    (actionQuotientπ_comp_restrictπComparison h V)

end Quotient

end AlgebraicGeometry.LocallyRingedSpace
