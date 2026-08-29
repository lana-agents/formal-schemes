import FormalSchemes.RelativeTopFiniteTypeBasis

set_option linter.style.header false

/-!
# Morphisms of formal schemes topologically of finite type, at an arbitrary target

`AlgebraicGeometry.FormalScheme.IsRelativelyTopFiniteType R I f`
(`FormalSchemes.RelativeTopFiniteType`) is **base-affine**: its `f` runs into
`FormalScheme.Spf I`. EGA I, 10.13 is a statement about an arbitrary morphism `f : X ⟶ Y`, and
this file is that notion together with the structural theorem that makes it usable — its charts
form a neighbourhood basis, so it does not depend on the covers it was born with.

## The definition, and why it needs no fibre product

EGA's condition is "an affine cover `{V_i}` of `Y`, and for each `i` an affine cover of
`f⁻¹(V_i)` by `Spf` of algebras of finite type over `V_i`". The preimage never has to be *formed*:
what is taken as the definition here is the preimage-free "a cover `𝒰` of `X` each of whose charts
factors through some chart of `Y`", and a factorisation is a composite. So `IsTopFiniteTypeHom`
needs only `FormalScheme.OpenCover` and `Category.comp`, and in particular none of the
fibre-product layer that `FormalSchemes.RelativeTopFiniteType`'s "remaining follow-up" paragraph
anticipated.

**Only one direction of that rephrasing is free**, and the docstring should not claim more than
the file proves. EGA's form gives this one immediately: take the union over `i` of the affine
covers of `f⁻¹(V_i)`. The converse — from a chart of `X` lying over `V_{i(j)}`, produce an affine
neighbourhood of a point of `f⁻¹(V_i)` that is tf-type over `V_i` — needs a neighbourhood basic in
`V_i` and in `V_{i(j)}` at once. That neighbourhood now exists,
`FormalSpectrum.exists_basicOpenChart_le_affine_inter` (`FormalSchemes.TwoChartBasicOpen`), but it
is returned as an equality of *ranges*, and re-reading a chart across it needs the ring-level
identification recorded under "What is *not* proved" below. So the two forms are still not proved
equivalent on this tree, and the same gap blocks that equivalence and the composition law.

`FormalScheme.OpenCover` (`FormalSchemes.OpenCover`) is index-type-polymorphic with a per-index
`obj`, so the charts of `𝒱` may sit over *different* base rings; the base ring is quantified
inside the predicate, once per chart, not fixed for the whole morphism.

## The one deviation from the base-affine notion: `I.FG`

Each chart of the target carries `hI : I.FG`. In the base-affine notion the base ideal is a
parameter, so `I.FG` can be — and is — a hypothesis of every theorem that needs it
(`IsRelativelyTopFiniteType.nonempty_relTfTypeChart`, `IsLocallyTopFiniteType.trans`,
`tateCurveModel_isRelativelyTopFiniteType_base`, …). Here the base ideal is *existentially bound
per chart*, so a hypothesis outside the predicate cannot reach it, and the refinement below
genuinely needs it: `L.FG` comes from `I.FG` through `IsTopologicallyFiniteType.fg`, and
`FormalSpectrum.isOpenImmersion_basicOpenChart` and `IsTopologicallyFiniteType.awayCompletion`
both consume it. Every consumer of the base-affine notion on this tree already supplies `I.FG`, so
this costs nothing at the reduction `IsRelativelyTopFiniteType.isTopFiniteTypeHom`, which takes it
as a hypothesis.

## Main definitions

* `FormalScheme.IsTopFiniteTypeHomOn f 𝒱 𝒰`: the per-cover condition — every chart of `𝒰`
  factors, through affine identifications, as the structural morphism of a tf-type algebra
  followed by a chart of `𝒱`.
* `FormalScheme.IsTopFiniteTypeHom f`: `f` is topologically of finite type — such covers exist.
* `FormalScheme.TfTypeHomChart f 𝒱 U x`: a chart of `X` around `x`, inside `U`, tf-type over a
  named chart of `𝒱`. The general-target analogue of `FormalScheme.RelTfTypeChart`.

## Main results

* `IsRelativelyTopFiniteType.isTopFiniteTypeHom`: the base-affine notion implies the general one.
  This is the easy half of conservativity; see "What is not proved" below for the other half.
* `IsTopFiniteTypeHom.of_iso`, `IsTopFiniteTypeHom.comp_iso`: invariance under an isomorphism of
  the source and of the target.
* `isTopFiniteTypeHomOn_id` and `isTopFiniteTypeHom_id`: **identities are topologically of finite
  type**, for any formal scheme admitting an affine cover with finitely generated ideals of
  definition, the first against that named cover on both sides.
* `nonempty_tfTypeHomChart_of_cover`: **the structural theorem.** Tf-type charts over a chart of
  `𝒱` form a neighbourhood basis of `X`. The general-target analogue of
  `IsRelativelyTopFiniteType.nonempty_relTfTypeChart`, and the reason the notion is a notion
  rather than a definition that elaborates.
* `IsTopFiniteTypeHom.exists_refinement`: every open cover of `X` is refined by one witnessing
  `IsTopFiniteTypeHom f` — **against the same cover of `Y`**, which is what makes the refinement
  usable for composition later.

## What is *not* proved, and the precise lemma that blocks it

Two things, and it is worth being exact about them because
`FormalSchemes.RelativeTopFiniteTypeTrans` named both as blockers and this file removes only part
of the first.

* **Composition.** `f : X ⟶ Y`, `g : Y ⟶ Z`, both tf-type, gives two covers of `Y` — `𝒱` from
  `f` and `𝒱'` from `g` — and they must be refined against each other. `exists_refinement`
  refines the `X`-side against any cover *keeping the same `𝒱`*, so the `X`-side is not the
  obstacle; the `Y`-side is.

  **Both geometric ingredients of the `Y`-side refinement have since landed**, and this paragraph
  no longer names either of them as missing. `FormalSpectrum.exists_basicOpenChart_le_affine_inter`
  and `FormalSpectrum.exists_basicOpenChart_inter_iso` (`FormalSchemes.TwoChartBasicOpen`) are the
  formal-scheme analogue of `AlgebraicGeometry.exists_basicOpen_le_affine_inter`: for two affine
  charts of a formal scheme and a point of their intersection, a common refinement, returned as an
  equality of ranges together with an isomorphism of the two refined charts commuting with their
  inclusions. `AlgebraicGeometry.IsTopologicallyFiniteType.awayCompletion_baseChange`
  (`FormalSchemes.AwayBaseChangeTopFiniteType`) then re-reads an `X`-chart tf-type over `(R, I)` as
  tf-type over the shrunk base `(R{1/c}^, I{1/c}^)`.

  **What still blocks the composition law is not geometric.** `IsTopFiniteTypeHomOn` factorises
  through `AlgebraicGeometry.IsTopologicallyFiniteType.structHom`, which is `Spf` applied to an
  `algebraMap`; so the refinement's isomorphism of *formal schemes* has to be `Spf` of a ring
  isomorphism carrying one ideal of definition **onto** the other. `Spf` is full only onto the
  *continuous* morphisms (`AdicRingCat.spfHomEquiv`, `FormalSchemes.SpfFullyFaithful`), and the
  strict containment that notion demands is not an isomorphism invariant: two ideals of definition
  inducing the same topology on a ring — `L` and `L ^ 2` — present the same formal spectrum. Two
  affine charts of one formal scheme, arriving from two independent witnesses, are therefore
  related on their overlap only up to equivalence of ideals of definition, while the predicate is
  stated at a fixed ideal. Closing the gap means proving `IsTopologicallyFiniteType` invariant
  under replacing the base ideal by an equivalent one, and recovering a ring isomorphism from an
  isomorphism of formal spectra up to that equivalence; neither is on this tree.

  The composition law **over a shared middle chart**, where the identification never has to be
  manufactured, is `AlgebraicGeometry.FormalScheme.IsTfTypeTower.isTopFiniteTypeHomOn`
  (`FormalSchemes.TopFiniteTypeHomComp`).
* **Conservativity**, i.e. that at `Y = FormalScheme.Spf I` the general notion implies the
  base-affine one. Unchanged by this file: it needs an *arbitrary* affine open of `Spf I` to be
  tf-type over `(R, I)`, of which the tree has only the basic-open case
  (`IsTopologicallyFiniteType.awayCompletion`, `FormalSchemes.AwayTopFiniteType`).

So `IsTopFiniteTypeHom` is landed with its neighbourhood basis and its reduction from the affine
case, and EGA I 10.13's composition law holds for it only in the shared-middle-chart form of
`FormalSchemes.TopFiniteTypeHomComp`. Nothing here should be read as saying §10.13 is finished.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
-/

noncomputable section

open CategoryTheory TopologicalSpace Topology

universe u

namespace AlgebraicGeometry.FormalScheme

variable {X Y : FormalScheme.{u}}

/-! ### The predicate -/

/-- The per-cover condition behind `IsTopFiniteTypeHom`: every chart of `𝒰` is, through affine
identifications, the structural morphism `Spf L ⟶ Spf I` of an algebra `A` topologically of
finite type over an adic ring `(R, I)` with `I` finitely generated, followed by a chart of `𝒱`.

Named separately from `IsTopFiniteTypeHom` so that a caller who has produced the covers — as
`exists_refinement` does — can hand back the per-chart data rather than only the predicate the
caller already had. -/
def IsTopFiniteTypeHomOn (f : X ⟶ Y) (𝒱 : OpenCover Y) (𝒰 : OpenCover X) : Prop :=
  ∀ j : 𝒰.J, ∃ (i : 𝒱.J)
    (R : Type u) (_ : CommRing R) (_ : TopologicalSpace R) (I : Ideal R) (_ : IsAdicRing I)
    (_ : I.FG)
    (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : Algebra R A)
    (L : Ideal A) (_ : IsAdicRing L) (h : IsTopologicallyFiniteType R I A L)
    (e : 𝒰.obj j ≅ FormalScheme.Spf L) (e' : 𝒱.obj i ≅ FormalScheme.Spf I),
    𝒰.map j ≫ f = e.hom ≫ IsTopologicallyFiniteType.structHom h ≫ e'.inv ≫ 𝒱.map i

/-- A morphism `f : X ⟶ Y` of formal schemes is **topologically of finite type** if there are open
covers `𝒱` of `Y` and `𝒰` of `X` such that every chart of `𝒰` factors through a chart of `𝒱` by
the structural morphism of a topologically finitely generated algebra (EGA I, 10.13).

The general-target form of `IsRelativelyTopFiniteType`, which is this predicate with `Y` forced to
be `FormalScheme.Spf I` and `𝒱` forced to be the self-cover; see
`IsRelativelyTopFiniteType.isTopFiniteTypeHom`. -/
def IsTopFiniteTypeHom (f : X ⟶ Y) : Prop :=
  ∃ (𝒱 : OpenCover Y) (𝒰 : OpenCover X), IsTopFiniteTypeHomOn f 𝒱 𝒰

/-! ### The reduction from the base-affine notion -/

section BaseAffine

variable {R : Type u} [CommRing R] {I : Ideal R} [TopologicalSpace R] [IsAdicRing I]

/-- **The base-affine notion implies the general one**: a morphism `f : X ⟶ Spf R` that is
topologically of finite type over `(R, I)` in the sense of `IsRelativelyTopFiniteType` is
topologically of finite type as a morphism.

The target cover is the one-object self-cover `OpenCover.self` and the target identification is
`Iso.refl`, so the two compatibility conditions differ by a `Category.id_comp`. This is the easy
half of conservativity; the converse needs an arbitrary affine open of `Spf R` to be tf-type over
`(R, I)`, which the tree does not have — see the module docstring. -/
theorem IsRelativelyTopFiniteType.isTopFiniteTypeHom {f : X ⟶ FormalScheme.Spf I} (hI : I.FG)
    (h : IsRelativelyTopFiniteType R I f) : IsTopFiniteTypeHom f := by
  obtain ⟨𝒰, h𝒰⟩ := h
  refine ⟨OpenCover.self (FormalScheme.Spf I), 𝒰, fun j => ?_⟩
  obtain ⟨A, _, _, _, L, _, hA, e, hcomp⟩ := h𝒰 j
  exact ⟨PUnit.unit, R, inferInstance, inferInstance, I, inferInstance, hI, A, inferInstance,
    inferInstance, inferInstance, L, inferInstance, hA, e, Iso.refl _, by
      simpa [OpenCover.self] using hcomp⟩

/-- The structural morphism `Spf L ⟶ Spf R` of a tf-type algebra is topologically of finite type
as a morphism — the affine local model instantiating the predicate. -/
theorem _root_.AlgebraicGeometry.IsTopologicallyFiniteType.isTopFiniteTypeHom
    {A : Type u} [CommRing A] [TopologicalSpace A] [Algebra R A] {L : Ideal A} [IsAdicRing L]
    (hI : I.FG) (h : IsTopologicallyFiniteType R I A L) :
    IsTopFiniteTypeHom (IsTopologicallyFiniteType.structHom h) :=
  IsRelativelyTopFiniteType.isTopFiniteTypeHom hI
    (IsTopologicallyFiniteType.isRelativelyTopFiniteType h)

end BaseAffine

/-! ### Isomorphism invariance, and identities -/

/-- **Invariance under an isomorphism of the source.** Transport the cover of `X` along `e.inv`;
the target cover, the identifications and the base rings are all unchanged, and the extra
compatibility obligation is `e.inv_hom_id`.

The general-target analogue of `IsRelativelyTopFiniteType.of_iso`, with the same proof. -/
theorem IsTopFiniteTypeHom.of_iso {X' : FormalScheme.{u}} {f : X ⟶ Y}
    (h : IsTopFiniteTypeHom f) (e : X' ≅ X) : IsTopFiniteTypeHom (e.hom ≫ f) := by
  obtain ⟨𝒱, 𝒰, h𝒰⟩ := h
  have hinv : IsIso e.inv.toLRSHom :=
    inferInstanceAs (IsIso (forgetToLocallyRingedSpace.map e.inv))
  refine ⟨𝒱, {
    J := 𝒰.J
    obj := 𝒰.obj
    map := fun j => 𝒰.map j ≫ e.inv
    f := fun x => 𝒰.f (e.hom.toLRSHom.base x)
    covers := fun x => ?_
    isOpenImmersion := fun j =>
      inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
        ((𝒰.map j).toLRSHom ≫ e.inv.toLRSHom)) }, fun j => ?_⟩
  · obtain ⟨y, hy⟩ := 𝒰.covers (e.hom.toLRSHom.base x)
    refine ⟨y, ?_⟩
    change e.inv.toLRSHom.base ((𝒰.map (𝒰.f (e.hom.toLRSHom.base x))).toLRSHom.base y) = x
    rw [hy]
    change (e.hom ≫ e.inv).toLRSHom.base x = x
    rw [e.hom_inv_id]
    rfl
  · obtain ⟨i, R, _, _, I, _, hI, A, _, _, _, L, _, hA, e₁, e₂, hcomp⟩ := h𝒰 j
    refine ⟨i, R, inferInstance, inferInstance, I, inferInstance, hI, A, inferInstance,
      inferInstance, inferInstance, L, inferInstance, hA, e₁, e₂, ?_⟩
    rw [show (𝒰.map j ≫ e.inv) ≫ e.hom ≫ f = 𝒰.map j ≫ (e.inv ≫ e.hom) ≫ f by
      simp only [Category.assoc], e.inv_hom_id, Category.id_comp]
    exact hcomp

/-- **Invariance under an isomorphism of the target.** Transport the cover of `Y` along `e.hom`;
the cover of `X`, the identifications and the base rings are all unchanged, and the compatibility
is the original one post-composed with `e.hom`. -/
theorem IsTopFiniteTypeHom.comp_iso {Y' : FormalScheme.{u}} {f : X ⟶ Y}
    (h : IsTopFiniteTypeHom f) (e : Y ≅ Y') : IsTopFiniteTypeHom (f ≫ e.hom) := by
  obtain ⟨𝒱, 𝒰, h𝒰⟩ := h
  have hhom : IsIso e.hom.toLRSHom :=
    inferInstanceAs (IsIso (forgetToLocallyRingedSpace.map e.hom))
  refine ⟨{
    J := 𝒱.J
    obj := 𝒱.obj
    map := fun i => 𝒱.map i ≫ e.hom
    f := fun y => 𝒱.f (e.inv.toLRSHom.base y)
    covers := fun y => ?_
    isOpenImmersion := fun i =>
      inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
        ((𝒱.map i).toLRSHom ≫ e.hom.toLRSHom)) }, 𝒰, fun j => ?_⟩
  · obtain ⟨z, hz⟩ := 𝒱.covers (e.inv.toLRSHom.base y)
    refine ⟨z, ?_⟩
    change e.hom.toLRSHom.base ((𝒱.map (𝒱.f (e.inv.toLRSHom.base y))).toLRSHom.base z) = y
    rw [hz]
    change (e.inv ≫ e.hom).toLRSHom.base y = y
    rw [e.inv_hom_id]
    rfl
  · obtain ⟨i, R, _, _, I, _, hI, A, _, _, _, L, _, hA, e₁, e₂, hcomp⟩ := h𝒰 j
    refine ⟨i, R, inferInstance, inferInstance, I, inferInstance, hI, A, inferInstance,
      inferInstance, inferInstance, L, inferInstance, hA, e₁, e₂, ?_⟩
    rw [← Category.assoc, hcomp]
    simp only [Category.assoc]

section Identity

variable {R : Type u} [CommRing R] {I : Ideal R} [TopologicalSpace R] [IsAdicRing I]

/-- **The structural morphism of a complete adic ring over itself is the identity.** Both sides
are `FormalSpectrum.locallyRingedSpaceMap` — of `algebraMap R R` on the left, which is
`RingHom.id R` — so this is `FormalSpectrum.locallyRingedSpaceMap_id` after
`Algebra.algebraMap_self`, glued by `FormalSpectrum.locallyRingedSpaceMap_congr`, which is needed
because `locallyRingedSpaceMap` carries a proof *about* the homomorphism being rewritten. -/
theorem _root_.AlgebraicGeometry.IsTopologicallyFiniteType.structHom_self :
    IsTopologicallyFiniteType.structHom (IsTopologicallyFiniteType.self (R := R) (I := I)) =
      𝟙 (FormalScheme.Spf I) := by
  refine Hom.ext' (Eq.trans ?_ (FormalSpectrum.locallyRingedSpaceMap_id I))
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _
    (Algebra.algebraMap_self : algebraMap R R = RingHom.id R)

end Identity

/-- **The identity is topologically of finite type against a given affine cover, on both sides.**
Each chart is tf-type over itself by `IsTopologicallyFiniteType.self`, and the compatibility
collapses because that algebra's structural morphism is the identity (`structHom_self`).

Stated at the cover rather than as the existential `isTopFiniteTypeHom_id` below because a caller
composing with `𝟙 X` needs the per-chart data against a *named* cover — see
`FormalSchemes.TopFiniteTypeHomComp`, where it is what exhibits a chart inclusion as a finite-type
morphism. -/
theorem isTopFiniteTypeHomOn_id (𝒰 : OpenCover X)
    (h𝒰 : ∀ j, ∃ (R : Type u) (_ : CommRing R) (_ : TopologicalSpace R) (I : Ideal R)
      (_ : IsAdicRing I) (_ : I.FG), Nonempty (𝒰.obj j ≅ FormalScheme.Spf I)) :
    IsTopFiniteTypeHomOn (𝟙 X) 𝒰 𝒰 := by
  intro j
  obtain ⟨R, _, _, I, _, hI, ⟨e⟩⟩ := h𝒰 j
  refine ⟨j, R, inferInstance, inferInstance, I, inferInstance, hI, R, inferInstance,
    inferInstance, inferInstance, I, inferInstance, IsTopologicallyFiniteType.self, e, e, ?_⟩
  rw [IsTopologicallyFiniteType.structHom_self, Category.id_comp, ← Category.assoc,
    e.hom_inv_id, Category.id_comp, Category.comp_id]

/-- **Identities are topologically of finite type**, for any formal scheme admitting an affine
cover whose ideals of definition are finitely generated: `isTopFiniteTypeHomOn_id` with both covers
taken to be the given one.

Together with `IsRelativelyTopFiniteType.isTopFiniteTypeHom` this is the evidence that the
predicate is not vacuous. The other half of the category-theoretic sanity check — that the
composite of two tf-type morphisms is tf-type — is *not* proved here; see the module docstring for
what blocks it, and `FormalSchemes.TopFiniteTypeHomComp` for the case that is available. -/
theorem isTopFiniteTypeHom_id (𝒰 : OpenCover X)
    (h𝒰 : ∀ j, ∃ (R : Type u) (_ : CommRing R) (_ : TopologicalSpace R) (I : Ideal R)
      (_ : IsAdicRing I) (_ : I.FG), Nonempty (𝒰.obj j ≅ FormalScheme.Spf I)) :
    IsTopFiniteTypeHom (𝟙 X) :=
  ⟨𝒰, 𝒰, isTopFiniteTypeHomOn_id 𝒰 h𝒰⟩

/-! ### The refinement crux -/

section Refinement

variable {R : Type u} [CommRing R] {I : Ideal R} [TopologicalSpace R] [IsAdicRing I]
variable {A : Type u} [CommRing A] [Algebra R A] {L : Ideal A} [TopologicalSpace A] [IsAdicRing L]
variable {f : X ⟶ Y}

/-- **The refinement step, with the target chart carried as a variable tail.** If a chart
`m : Spf A ⟶ X` sits over a morphism `t : Spf R ⟶ Y` by `A`'s structural morphism, then so does
its basic-open refinement `Spf A{1/g}^ ⟶ Spf A ⟶ X`.

`FormalScheme.basicOpenChartHom_comp` (`FormalSchemes.RelativeTopFiniteTypeBasis`) is this
statement at `Y = Spf R` and `t = 𝟙`; the only new content is that a tail composes on the right of
both sides, which is `Category.assoc` around `basicOpenChartHom_comp_structHom`. Stated at a
variable `m` and a variable `f` for the reason recorded there — instantiating first makes the
`Hom.mk`/`toLRSHom` unfolding step time out at `isDefEq`, and at variables it is `rfl`. -/
theorem basicOpenChartHom_comp_target (g : A)
    [IsAdicRing (FormalSpectrum.awayCompletionIdeal L g)]
    (m : FormalScheme.Spf L ⟶ X) (t : FormalScheme.Spf I ⟶ Y)
    (h : IsTopologicallyFiniteType R I A L)
    (h' : IsTopologicallyFiniteType R I (FormalSpectrum.awayCompletion L g)
      (FormalSpectrum.awayCompletionIdeal L g))
    (hm : m ≫ f = IsTopologicallyFiniteType.structHom h ≫ t) :
    (Hom.mk (FormalSpectrum.basicOpenChart L g ≫ m.toLRSHom) :
        FormalScheme.Spf (FormalSpectrum.awayCompletionIdeal L g) ⟶ X) ≫ f =
      IsTopologicallyFiniteType.structHom h' ≫ t := by
  have hsplit : (Hom.mk (FormalSpectrum.basicOpenChart L g ≫ m.toLRSHom) :
        FormalScheme.Spf (FormalSpectrum.awayCompletionIdeal L g) ⟶ X) =
      (Hom.mk (FormalSpectrum.basicOpenChart L g) :
        FormalScheme.Spf (FormalSpectrum.awayCompletionIdeal L g) ⟶ FormalScheme.Spf L) ≫ m :=
    rfl
  rw [hsplit, Category.assoc, hm, ← Category.assoc, basicOpenChartHom_comp_structHom g h h']

end Refinement

/-! ### Charts of a tf-type morphism, and that they form a neighbourhood basis -/

/-- A **tf-type chart of a morphism**: an affine open immersion `Spf L ↪ X` around `x`, contained
in `U`, whose ring is topologically of finite type over an adic ring `(R, I)` with `I` finitely
generated, together with a named chart `i` of `𝒱` that it sits over.

The general-target analogue of `FormalScheme.RelTfTypeChart`. Two differences, both forced. The
base ring is a *field* of the structure rather than a parameter, because at a general target it
varies from chart to chart. And the chart of `𝒱` is recorded as an index plus an identification,
rather than as a bare morphism `Spf I ⟶ Y`, so that a family of charts reassembles into a witness
for `IsTopFiniteTypeHomOn f 𝒱 _` against *the same* `𝒱` — see
`OpenCover.ofTfTypeHomCharts_isTopFiniteTypeHomOn`. A bare morphism would not, because the
targets of a family of charts cover only the image of `X`, not `Y`. -/
structure TfTypeHomChart (f : X ⟶ Y) (𝒱 : OpenCover Y) (U : Set X) (x : X) where
  /-- The base ring of the target chart. -/
  R : Type u
  /-- Its commutative ring structure. -/
  [commRing : CommRing R]
  /-- Its topology. -/
  [topR : TopologicalSpace R]
  /-- The ideal of definition of the target chart. -/
  I : Ideal R
  /-- `(R, I)` is an adic ring, so `Spf I` is an affine formal scheme. -/
  [adicI : IsAdicRing I]
  /-- The ideal of definition is finitely generated — see the module docstring. -/
  fgI : I.FG
  /-- The index of the chart of `𝒱` this chart sits over. -/
  i : 𝒱.J
  /-- The identification of that chart of `𝒱` with `Spf I`. -/
  targetIso : 𝒱.obj i ≅ FormalScheme.Spf I
  /-- The chart of `X`, tf-type over `(R, I)`, around `x` and inside `U`. -/
  chart : TfTypeChart R I X U x
  /-- The chart commutes with `f` over its own structural morphism and the chart of `𝒱`. -/
  structCompat : (Hom.mk chart.map : FormalScheme.Spf chart.L ⟶ X) ≫ f =
    IsTopologicallyFiniteType.structHom chart.tfType ≫ targetIso.inv ≫ 𝒱.map i

attribute [instance] TfTypeHomChart.commRing TfTypeHomChart.topR TfTypeHomChart.adicI

variable {f : X ⟶ Y}

/-- **Tf-type charts of a morphism form a neighbourhood basis.** Given covers witnessing that
`f` is topologically of finite type, every point `x` in an open `U` admits a tf-type chart
contained in `U` and sitting over a chart of `𝒱`.

The general-target analogue of `IsRelativelyTopFiniteType.nonempty_relTfTypeChart`, and the same
proof: the chart's identification `e` cancels by `e.inv_hom_id` before the refinement starts,
leaving a chart `m` sitting over the fixed tail `t = e'.inv ≫ 𝒱.map i`, and what the basic-open
refinement then has to preserve is `basicOpenChartHom_comp_target`. **The index `i` and the tail
are unchanged by the refinement**, which is what lets the refined family be read against the same
`𝒱`.

Stated at the unpacked cover data rather than at `IsTopFiniteTypeHom f`, because a caller
refining a family of charts needs them all over one `𝒱`, and the existential in
`IsTopFiniteTypeHom` would hand out a fresh one per point. -/
theorem nonempty_tfTypeHomChart_of_cover {𝒱 : OpenCover Y} {𝒰 : OpenCover X}
    (h𝒰 : IsTopFiniteTypeHomOn f 𝒱 𝒰) (x : X) (U : Set X) (hU : IsOpen U) (hxU : x ∈ U) :
    Nonempty (TfTypeHomChart f 𝒱 U x) := by
  obtain ⟨i, R, _, _, I, _, hI, A, _, _, _, L, _, hL, e, e', hcomp⟩ := h𝒰 (𝒰.f x)
  haveI : IsIso e.inv.toLRSHom :=
    inferInstanceAs (IsIso (forgetToLocallyRingedSpace.map e.inv))
  have hmf : (e.inv ≫ 𝒰.map (𝒰.f x)) ≫ f =
      IsTopologicallyFiniteType.structHom hL ≫ e'.inv ≫ 𝒱.map i := by
    rw [Category.assoc, hcomp, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  let m : FormalSpectrum.locallyRingedSpaceObj L ⟶ X.toLocallyRingedSpace :=
    (e.inv ≫ 𝒰.map (𝒰.f x)).toLRSHom
  haveI hm : LocallyRingedSpace.IsOpenImmersion m :=
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
      (e.inv.toLRSHom ≫ (𝒰.map (𝒰.f x)).toLRSHom))
  obtain ⟨y, hy⟩ := 𝒰.covers x
  have hxm : x ∈ Set.range m.base := by
    refine ⟨e.hom.toLRSHom.base y, ?_⟩
    change (e.hom ≫ e.inv ≫ 𝒰.map (𝒰.f x)).toLRSHom.base y = x
    rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
    exact hy
  obtain ⟨x₀, hx₀⟩ := hxm
  have hopen : IsOpen (m.base ⁻¹' U) := hU.preimage m.base.hom.continuous
  have hmem : x₀ ∈ m.base ⁻¹' U := by
    simp only [Set.mem_preimage, hx₀]; exact hxU
  obtain ⟨v, ⟨g, rfl⟩, hx₀v, hvsub⟩ :=
    (FormalSpectrum.isTopologicalBasis_basicOpen L).exists_subset_of_mem_open hmem hopen
  have hLfg : L.FG := IsTopologicallyFiniteType.fg hL hI
  haveI : IsAdicRing (FormalSpectrum.awayCompletionIdeal L g) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal L g hLfg
  haveI : LocallyRingedSpace.IsOpenImmersion (FormalSpectrum.basicOpenChart L g) :=
    FormalSpectrum.isOpenImmersion_basicOpenChart L g hLfg
  have hrange : Set.range (FormalSpectrum.basicOpenChart L g).base =
      (FormalSpectrum.basicOpen L g : Set (FormalSpectrum L)) :=
    FormalSpectrum.range_basicOpenChart_base L g hLfg
  refine ⟨{ R := R
            I := I
            fgI := hI
            i := i
            targetIso := e'
            chart :=
              { A := FormalSpectrum.awayCompletion L g
                L := FormalSpectrum.awayCompletionIdeal L g
                tfType := IsTopologicallyFiniteType.awayCompletion g hI hL
                map := FormalSpectrum.basicOpenChart L g ≫ m
                mem := ?_
                subset := ?_ }
            structCompat := ?_ }⟩
  · have hx₀mem : x₀ ∈ Set.range (FormalSpectrum.basicOpenChart L g).base := by
      rw [hrange]; exact hx₀v
    obtain ⟨w, hw⟩ := hx₀mem
    refine ⟨w, ?_⟩
    simp only [LocallyRingedSpace.comp_base, TopCat.comp_app]
    rw [hw]; exact hx₀
  · rw [LocallyRingedSpace.comp_base]
    intro z hz
    simp only [TopCat.comp_app, Set.mem_range] at hz
    obtain ⟨w, rfl⟩ := hz
    have hw : (FormalSpectrum.basicOpenChart L g).base w ∈
        (FormalSpectrum.basicOpen L g : Set (FormalSpectrum L)) := by
      rw [← hrange]; exact ⟨w, rfl⟩
    exact hvsub hw
  · exact basicOpenChartHom_comp_target g (e.inv ≫ 𝒰.map (𝒰.f x)) (e'.inv ≫ 𝒱.map i) hL
      (IsTopologicallyFiniteType.awayCompletion g hI hL) hmf

/-! ### Assembling a cover from charts, and the refinement -/

/-- The cover of `X` assembled from a **supplied** family of tf-type charts of `f`, indexed by the
points of `X`.

The family is an argument rather than an internal choice, for the reason recorded in
`FormalSchemes.TopFiniteTypeBasis`: a cover whose charts are picked by `Classical.choice` cannot
carry any property the caller did not think to put into the chart type. Unlike
`OpenCover.ofRelTfTypeCharts` this cannot be routed through `OpenCover.ofTfTypeCharts`, which fixes
one base ring for the whole family. -/
def OpenCover.ofTfTypeHomCharts {𝒱 : OpenCover Y} (U : X → Set X)
    (charts : ∀ x : X, TfTypeHomChart f 𝒱 (U x) x) : OpenCover X where
  J := X
  obj x := FormalScheme.Spf (charts x).chart.L
  map x := Hom.mk (charts x).chart.map
  f x := x
  covers x := (charts x).chart.mem
  isOpenImmersion x := (charts x).chart.isOpenImmersion

/-- Each piece of `ofTfTypeHomCharts` lands inside the open set the family was built against —
the containment that makes it a *refinement*. -/
theorem OpenCover.ofTfTypeHomCharts_range_subset {𝒱 : OpenCover Y} (U : X → Set X)
    (charts : ∀ x : X, TfTypeHomChart f 𝒱 (U x) x) (x : X) :
    Set.range ((OpenCover.ofTfTypeHomCharts U charts).map x).toLRSHom.base ⊆ U x :=
  (charts x).chart.subset

/-- **A cover assembled from tf-type charts witnesses `IsTopFiniteTypeHomOn` against the same
cover of `Y` the charts were taken over.** The identification demanded of each piece is `Iso.refl`,
because the piece is `Spf` of its own ring, and the compatibility is then the chart's own
`structCompat`. -/
theorem OpenCover.ofTfTypeHomCharts_isTopFiniteTypeHomOn {𝒱 : OpenCover Y} (U : X → Set X)
    (charts : ∀ x : X, TfTypeHomChart f 𝒱 (U x) x) :
    IsTopFiniteTypeHomOn f 𝒱 (OpenCover.ofTfTypeHomCharts U charts) := fun x =>
  ⟨(charts x).i, (charts x).R, inferInstance, inferInstance, (charts x).I, inferInstance,
    (charts x).fgI, (charts x).chart.A, inferInstance, inferInstance, inferInstance,
    (charts x).chart.L, inferInstance, (charts x).chart.tfType, Iso.refl _, (charts x).targetIso,
    (charts x).structCompat.trans (Category.id_comp _).symm⟩

/-- **Any open cover of `X` is refined by one witnessing that `f : X ⟶ Y` is topologically of
finite type — over the same cover of `Y`.**

The cover of `Y` is produced, not consumed, and it is the one the hypothesis supplied: the
refinement moves only the `X`-side. That is what a composition law would need from this half, and
it is why the statement returns `𝒱` rather than quantifying over it. The first conjunct is
`IsTopFiniteTypeHomOn` rather than `IsTopFiniteTypeHom`, so a caller gets the per-piece data and
not just the predicate it already had. -/
theorem IsTopFiniteTypeHom.exists_refinement {f : X ⟶ Y} (hf : IsTopFiniteTypeHom f)
    (𝒲 : OpenCover X) :
    ∃ (𝒱 : OpenCover Y) (𝒰 : OpenCover X), IsTopFiniteTypeHomOn f 𝒱 𝒰 ∧
      ∀ j, ∃ i, Set.range ((𝒰.map j).toLRSHom.base) ⊆
        Set.range ((𝒲.map i).toLRSHom.base) := by
  obtain ⟨𝒱, 𝒰, h𝒰⟩ := hf
  have hchart : ∀ x : X, Nonempty
      (TfTypeHomChart f 𝒱 (Set.range ((𝒲.map (𝒲.f x)).toLRSHom.base)) x) := fun x =>
    nonempty_tfTypeHomChart_of_cover h𝒰 x _
      ((𝒲.isOpenImmersion (𝒲.f x)).base_open.isOpen_range) (𝒲.covers x)
  let charts : ∀ x : X, TfTypeHomChart f 𝒱 (Set.range ((𝒲.map (𝒲.f x)).toLRSHom.base)) x :=
    fun x => (hchart x).some
  exact ⟨𝒱, OpenCover.ofTfTypeHomCharts _ charts,
    OpenCover.ofTfTypeHomCharts_isTopFiniteTypeHomOn _ charts,
    fun x => ⟨𝒲.f x, OpenCover.ofTfTypeHomCharts_range_subset _ charts x⟩⟩

end AlgebraicGeometry.FormalScheme
