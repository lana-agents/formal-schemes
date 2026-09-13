import FormalSchemes.GeneralSeparatedScheme
import FormalSchemes.OpenFormalSubscheme

set_option linter.style.header false

/-!
# Separatedness of a morphism of formal schemes, at an arbitrary target

`FormalScheme.IsSeparatedOverSpf` (`FormalSchemes.GeneralSeparatedScheme`) is a statement about a
formal scheme and a structural morphism to an **affine** formal scheme: its target is
`FormalSpectrum.locallyRingedSpaceObj I`, and there is no `f : X ⟶ Y` notion anywhere on the tree.
EGA I §10.15's own subject is a **morphism**, so this file supplies

```
FormalScheme.IsSeparatedHom hX hY (g : X ⟶ Y)
```

at an arbitrary target, by the same step `FormalSchemes.TopFiniteTypeHom` took for §10.13 when it
replaced `FormalScheme.IsRelativelyTopFiniteType` by `FormalScheme.IsTopFiniteTypeHom`.

## Why this is a generalisation and not a construction

The obvious worry is that separatedness of `g : X ⟶ Y` is a condition on the diagonal `X ⟶ X ×_Y X`,
and that a self-fibre-product over a **non-affine** `Y` does not exist on this tree:
`BothChartedFibreDatumXY` is a datum over `Spf R` and nothing else is available. That worry is real,
and it is *not* answered the way §10.13's was. `FormalScheme.IsTopFiniteTypeHom` avoids the preimage
by a **factorisation** — a cover of `X` each of whose charts factors through a chart of `Y` — and a
factorisation is just a composite, so it can be written at any target. **That dodge is unavailable
here**: separatedness is not chart-local on the source, because the object whose diagonal is at
issue has the *target* in it.

What works instead is the different classical fact that separatedness is **local on the target**.
Cover `Y` by opens `V` each of which is affine — `Y.restrictOpen hY V ≅ Spf I` — and ask, for each
of them, that the restricted morphism `X|_{g⁻¹V} ⟶ Y|_V ≅ Spf I` be separated in the affine-base
sense that already exists. Every fibre product this needs is over an affine base, so no new one is
built, and the whole of the restriction calculus it consumes is already on the tree in
`FormalSchemes.OpenFormalSubscheme`: `FormalScheme.restrictOpenMap` is `X|_{g⁻¹V} ⟶ Y|_V`,
`FormalScheme.restrictOpenIso` compares it with any open immersion of the same range, and
`FormalScheme.isSeparatedOverSpf_iff_of_iso` transports the per-chart conclusion.

## The shape of the definition, and what was rejected

The cover is a bare index type together with a family of **opens** of `Y` whose union is everything,
not a `FormalScheme.OpenCover Y`. `FormalScheme.OpenCover` packages open *immersions* `obj j ⟶ Y`
from formal schemes; the per-chart clause here needs the **open** `V j` itself, to form the preimage
`(Opens.map g.base).obj (V j)` and to name `Y.restrictOpen hY (V j)` as the target of
`FormalScheme.restrictOpenMap`. Going through `FormalScheme.OpenCover` would mean taking the range
of each chart as an open, then producing `obj j ≅ Y.restrictOpen hY (range)` — which is
`FormalScheme.restrictOpenIso` — only to feed it straight back in. That is strictly more data for
the same content, and it is data that `FormalScheme.IsSeparatedHom.of_iso` and
`FormalScheme.IsSeparatedHom.comp_iso` would then have to carry. Locality on the target is a
statement about opens of the target; the definition says that and nothing more.

The per-chart morphism is `FormalScheme.restrictOpenMap` rather than
`FormalScheme.restrictOpenSchemeMap` for the same reason `FormalScheme.IsSeparatedOverSpf` takes a
`LocallyRingedSpace` morphism rather than a `FormalScheme.Hom`: the affine identification `e` and
the predicate it feeds both live at `LocallyRingedSpace`, so the `FormalScheme`-level spelling would
only add a `Hom.mk`/`FormalScheme.Hom.toLRSHom` round trip at every use.

The two `FormalScheme.LocallyFG` hypotheses are not a restriction added here —
`FormalScheme.restrictOpen` needs them to produce a formal scheme at all — and they are `Prop`s, so
by definitional proof irrelevance `IsSeparatedHom hX hY g` does not depend on which proofs are
supplied.

## Main definitions and results

* `AlgebraicGeometry.FormalScheme.IsSeparatedHom`: **`g : X ⟶ Y` is separated** (EGA I §10.15)
  when `Y` has a cover by opens `V` with `Y|_V` affine on which the restricted morphism is separated
  in the affine-base sense.
* `AlgebraicGeometry.FormalScheme.isSeparatedHom_of_isSeparatedOverSpf`: **conservativity, easy
  direction** — a formal scheme separated over `Spf R` in the sense of
  `FormalScheme.IsSeparatedOverSpf` has separated structural morphism. The cover is the one-element
  cover at `V = ⊤`.
* `AlgebraicGeometry.FormalScheme.IsSeparatedHom.of_iso` and
  `AlgebraicGeometry.FormalScheme.IsSeparatedHom.comp_iso`: **invariance under an isomorphism of the
  source and of the target.** The target half is the new content: the base-affine predicate cannot
  state it, because its target is not a variable.

## What is *not* proved here

* **Conservativity's hard direction.** `IsSeparatedHom hX (locallyFG_Spf hI) g` at an affine
  target does *not* obviously give back `IsSeparatedOverSpf hI X g.toLRSHom`: the cover `V` of
  `Spf I` is arbitrary, so each chart clause only supplies separatedness over whatever presents its
  own `V j`, and returning to `(R, I)` is the shape of problem that
  `FormalSchemes.TargetBasicRefinement` solves for §10.13 — a basic-open refinement of the target
  cover, several modules of work. Nothing below should be read as having done it.
* **A composition law.** `IsSeparatedHom g → IsSeparatedHom h → IsSeparatedHom (g ≫ h)` is not
  proved and is not immediate: the target cover for `g ≫ h` has to be refined against both, and the
  per-chart clause would then need separatedness of a morphism between two open subschemes over a
  common affine, which the affine-base predicate does not state.
* **A value at a genuinely non-affine target.** The cheapest candidate is the identity on
  `ThreeChartCover.coverSubscheme`, and it runs into `FormalScheme.restrictOpenMap_id`'s documented
  heartbeat wall — the one place in this file's neighbourhood where that cost is real. Every value
  in `FormalSchemes.GeneralSeparatedHomValues` is conservativity applied at an affine target and
  then transported, which is what makes the predicate non-vacuous but says nothing that the
  base-affine notion could not already say.
* **Any relation to `BothChartedFibreDatumXY.IsSeparated`** beyond the one that
  `FormalScheme.IsSeparatedOverSpf` already carries. Nothing here is deprecated and no existing
  consumer moves.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
-/

noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry FormalSpectrum

universe u

namespace AlgebraicGeometry.FormalScheme

variable {X X' Y Y' : FormalScheme.{u}}

/-- **A morphism of formal schemes is separated** (EGA I §10.15) when the target has an open cover
on each piece of which the restricted morphism is separated over an affine formal scheme.

Concretely: opens `V j` of `Y` covering `Y`, and for each of them an adic ring `(R, I)` with `I`
finitely generated, an identification `e` of the open formal subscheme `Y|_{V j}` with `Spf I`, and
the statement that `X|_{g⁻¹ V j}` is separated over `Spf I` along `restrictOpenMap ≫ e.hom`.

This is the general-target form of `FormalScheme.IsSeparatedOverSpf`, which is this predicate with
`Y` forced to be `Spf I` and the cover forced to be `{⊤}`; that reduction is
`FormalScheme.isSeparatedHom_of_isSeparatedOverSpf`. The module docstring records why the
generalisation costs no new fibre product, and why the reason differs from the one
`FormalScheme.IsTopFiniteTypeHom` relies on. -/
def IsSeparatedHom (hX : X.LocallyFG) (hY : Y.LocallyFG) (g : X ⟶ Y) : Prop :=
  ∃ (J : Type u) (V : J → Opens Y), (⋃ j, ((V j : Set Y))) = Set.univ ∧
    ∀ j : J, ∃ (R : Type u) (_ : CommRing R) (_ : TopologicalSpace R) (I : Ideal R)
      (_ : IsAdicRing I) (hI : I.FG)
      (e : (Y.restrictOpen hY (V j)).toLocallyRingedSpace ≅ locallyRingedSpaceObj I),
      IsSeparatedOverSpf hI (X.restrictOpen hX ((Opens.map g.toLRSHom.base).obj (V j)))
        (X.restrictOpenMap hX Y hY g.toLRSHom (V j) ≫ e.hom)

/-! ### The reduction from the base-affine notion -/

section BaseAffine

variable {R : Type u} [CommRing R] [TopologicalSpace R] {I : Ideal R} [IsAdicRing I]

/-- **The base-affine notion implies the general one**: a formal scheme separated over `Spf R` in
the sense of `FormalScheme.IsSeparatedOverSpf` has separated structural morphism.

The cover is the one-element cover at `V = ⊤`, the affine identification is
`LocallyRingedSpace.restrictTopIso` — which is `FormalScheme.restrictOpenι` at `⊤` on the nose — and
the source comparison is `restrictOpenCongr ≪≫ restrictOpenTopIso`, whose forward leg is the
inclusion by `FormalScheme.restrictOpenCongrTop_hom`. That comparison is *named* rather than left to
unification on purpose: `FormalSchemes.OpenFormalSubscheme`'s functor-law note records that asking
`isDefEq` to identify `X.restrictOpen hX ((Opens.map _).obj V)` with `X.restrictOpen hX V` is what
exhausts the heartbeat budget in `FormalScheme.restrictOpenMap_id`.

This is the easy half of conservativity; the converse is not proved — see the module docstring. -/
theorem isSeparatedHom_of_isSeparatedOverSpf (hI : I.FG) (hX : X.LocallyFG)
    (g : X ⟶ FormalScheme.Spf I) (h : IsSeparatedOverSpf hI X g.toLRSHom) :
    IsSeparatedHom hX (locallyFG_Spf hI) g := by
  refine ⟨PUnit.{u + 1}, fun _ => ⊤, by simp [Set.iUnion_const], fun _ => ?_⟩
  have hUtop : (Opens.map g.toLRSHom.base).obj (⊤ : Opens (FormalScheme.Spf I)) = ⊤ :=
    Opens.map_top _
  refine ⟨R, inferInstance, inferInstance, I, inferInstance, hI,
    (FormalScheme.Spf I).toLocallyRingedSpace.restrictTopIso, ?_⟩
  set iso : X.restrictOpen hX ((Opens.map g.toLRSHom.base).obj ⊤) ≅ X :=
    X.restrictOpenCongr hX hUtop ≪≫ X.restrictOpenTopIso hX with hiso
  have hhom : iso.hom.toLRSHom = X.restrictOpenι hX ((Opens.map g.toLRSHom.base).obj ⊤) := by
    rw [hiso, X.restrictOpenCongrTop_hom hX hUtop]
    rfl
  refine isSeparatedOverSpf_of_iso hI
    { hom := iso.inv.toLRSHom, inv := iso.hom.toLRSHom
      hom_inv_id := congrArg Hom.toLRSHom iso.inv_hom_id
      inv_hom_id := congrArg Hom.toLRSHom iso.hom_inv_id } ?_ h
  change iso.inv.toLRSHom ≫ (X.restrictOpenMap hX (FormalScheme.Spf I) (locallyFG_Spf hI)
    g.toLRSHom ⊤ ≫ (FormalScheme.Spf I).restrictOpenι (locallyFG_Spf hI) ⊤) = g.toLRSHom
  rw [X.restrictOpenMap_comp_ι hX (FormalScheme.Spf I) (locallyFG_Spf hI) g.toLRSHom ⊤,
    ← Category.assoc, ← hhom]
  have hid : iso.inv.toLRSHom ≫ iso.hom.toLRSHom = 𝟙 X.toLocallyRingedSpace :=
    congrArg Hom.toLRSHom iso.inv_hom_id
  rw [hid, Category.id_comp]

end BaseAffine

/-! ### Isomorphism invariance

Both directions go through `FormalScheme.restrictOpenIso`: an isomorphism of the source carries the
inclusion of `g⁻¹V` to an open immersion of range `g'⁻¹V`, an isomorphism of the target carries the
inclusion of `V` to one of range `e.inv⁻¹V`, and in each case the comparison it produces is
recognised as the right one by `FormalScheme.restrictOpenMap_uniq`, which says the square over the
target determines the induced morphism. No germ-level or chart-level argument appears in either
proof. -/

private theorem base_hom_inv_id (e : X' ≅ X) (x : X) :
    e.hom.toLRSHom.base (e.inv.toLRSHom.base x) = x := by
  change (e.inv ≫ e.hom).toLRSHom.base x = x
  rw [e.inv_hom_id]
  rfl

private theorem base_inv_hom_id (e : X' ≅ X) (x : X') :
    e.inv.toLRSHom.base (e.hom.toLRSHom.base x) = x := by
  change (e.hom ≫ e.inv).toLRSHom.base x = x
  rw [e.hom_inv_id]
  rfl

/-- **Invariance under an isomorphism of the source.** The cover of the target, the base rings and
the affine identifications are all unchanged; only the source open subscheme moves, along the
comparison `FormalScheme.restrictOpenIso` built from `restrictOpenι ≫ e.inv`, whose range is the new
preimage because the isomorphism's two legs are inverse on points.

The general-target analogue of `FormalScheme.isSeparatedOverSpf_of_iso`, and the exact mirror of
`FormalScheme.IsTopFiniteTypeHom.of_iso`. -/
theorem IsSeparatedHom.of_iso (hX : X.LocallyFG) (hY : Y.LocallyFG) (hX' : X'.LocallyFG)
    {g : X ⟶ Y} (h : IsSeparatedHom hX hY g) (e : X' ≅ X) :
    IsSeparatedHom hX' hY (e.hom ≫ g) := by
  obtain ⟨J, V, hcov, hsep⟩ := h
  refine ⟨J, V, hcov, fun j => ?_⟩
  obtain ⟨R, _, _, I, _, hI, ee, hj⟩ := hsep j
  refine ⟨R, inferInstance, inferInstance, I, inferInstance, hI, ee, ?_⟩
  have hrange : Set.range (X.restrictOpenι hX ((Opens.map g.toLRSHom.base).obj (V j))
      ≫ e.inv.toLRSHom).base
      = (((Opens.map (e.hom ≫ g).toLRSHom.base).obj (V j) : Opens X') : Set X') := by
    have hcomp : ⇑(X.restrictOpenι hX ((Opens.map g.toLRSHom.base).obj (V j))
        ≫ e.inv.toLRSHom).base
        = ⇑e.inv.toLRSHom.base ∘ ⇑(X.restrictOpenι hX
          ((Opens.map g.toLRSHom.base).obj (V j))).base := rfl
    rw [hcomp, Set.range_comp, range_restrictOpenι_base, Opens.map_coe,
      Set.image_eq_preimage_of_inverse (base_hom_inv_id e) (base_inv_hom_id e)]
    rfl
  set φ := X'.restrictOpenIso hX' ((Opens.map (e.hom ≫ g).toLRSHom.base).obj (V j))
    (X.restrictOpenι hX ((Opens.map g.toLRSHom.base).obj (V j)) ≫ e.inv.toLRSHom) hrange with hφ
  have hmap : φ.hom ≫ X'.restrictOpenMap hX' Y hY (e.hom ≫ g).toLRSHom (V j)
      = X.restrictOpenMap hX Y hY g.toLRSHom (V j) := by
    refine X.restrictOpenMap_uniq hX Y hY g.toLRSHom (V j) _ ?_
    rw [Category.assoc, restrictOpenMap_comp_ι, ← Category.assoc, hφ,
      restrictOpenIso_hom_comp, Category.assoc]
    congr 1
    change e.inv.toLRSHom ≫ e.hom.toLRSHom ≫ g.toLRSHom = g.toLRSHom
    rw [← Category.assoc]
    have hid : e.inv.toLRSHom ≫ e.hom.toLRSHom = 𝟙 X.toLocallyRingedSpace :=
      congrArg Hom.toLRSHom e.inv_hom_id
    rw [hid, Category.id_comp]
  exact isSeparatedOverSpf_of_iso hI φ (by rw [← Category.assoc, hmap]) hj

/-- **Invariance under an isomorphism of the target.** This is the half the base-affine predicate
cannot state, since its target is `Spf R` and not a variable.

The cover is transported along the isomorphism's inverse, the affine identification of each
transported piece is the old one precomposed with `FormalScheme.restrictOpenIso` at `restrictOpenι ≫
e.hom`, and the source open subscheme does not move at all — the two preimages are *equal*, because
`e.hom ≫ e.inv` is the identity, so the source comparison is `FormalScheme.restrictOpenCongr`. -/
theorem IsSeparatedHom.comp_iso (hX : X.LocallyFG) (hY : Y.LocallyFG) (hY' : Y'.LocallyFG)
    {g : X ⟶ Y} (h : IsSeparatedHom hX hY g) (e : Y ≅ Y') :
    IsSeparatedHom hX hY' (g ≫ e.hom) := by
  obtain ⟨J, V, hcov, hsep⟩ := h
  refine ⟨J, fun j => (Opens.map e.inv.toLRSHom.base).obj (V j), ?_, fun j => ?_⟩
  · have hpre : (⋃ j, (((Opens.map e.inv.toLRSHom.base).obj (V j) : Opens Y') : Set Y'))
        = ⇑e.inv.toLRSHom.base ⁻¹' (⋃ j, ((V j : Set Y))) := by
      rw [Set.preimage_iUnion]
      rfl
    rw [hpre, hcov, Set.preimage_univ]
  · obtain ⟨R, _, _, I, _, hI, ee, hj⟩ := hsep j
    have hrange : Set.range (Y.restrictOpenι hY (V j) ≫ e.hom.toLRSHom).base
        = (((Opens.map e.inv.toLRSHom.base).obj (V j) : Opens Y') : Set Y') := by
      have hcomp : ⇑(Y.restrictOpenι hY (V j) ≫ e.hom.toLRSHom).base
          = ⇑e.hom.toLRSHom.base ∘ ⇑(Y.restrictOpenι hY (V j)).base := rfl
      rw [hcomp, Set.range_comp, range_restrictOpenι_base,
        Set.image_eq_preimage_of_inverse (base_inv_hom_id e) (base_hom_inv_id e)]
      rfl
    set ψ := Y'.restrictOpenIso hY' ((Opens.map e.inv.toLRSHom.base).obj (V j))
      (Y.restrictOpenι hY (V j) ≫ e.hom.toLRSHom) hrange with hψ
    refine ⟨R, inferInstance, inferInstance, I, inferInstance, hI, ψ.symm ≪≫ ee, ?_⟩
    have hU : (Opens.map (g ≫ e.hom).toLRSHom.base).obj
        ((Opens.map e.inv.toLRSHom.base).obj (V j)) = (Opens.map g.toLRSHom.base).obj (V j) := by
      ext x
      change e.inv.toLRSHom.base (e.hom.toLRSHom.base (g.toLRSHom.base x)) ∈ V j
        ↔ g.toLRSHom.base x ∈ V j
      rw [base_inv_hom_id e]
    set χ : X.restrictOpen hX ((Opens.map g.toLRSHom.base).obj (V j))
        ≅ X.restrictOpen hX ((Opens.map (g ≫ e.hom).toLRSHom.base).obj
          ((Opens.map e.inv.toLRSHom.base).obj (V j))) := X.restrictOpenCongr hX hU.symm
    have hχcomp : χ.hom.toLRSHom ≫ X.restrictOpenι hX
          ((Opens.map (g ≫ e.hom).toLRSHom.base).obj ((Opens.map e.inv.toLRSHom.base).obj (V j)))
        = X.restrictOpenι hX ((Opens.map g.toLRSHom.base).obj (V j)) :=
      congrArg Hom.toLRSHom (X.restrictOpenCongr_hom_comp hX hU.symm)
    have hehom : e.hom.toLRSHom ≫ e.inv.toLRSHom = 𝟙 Y.toLocallyRingedSpace :=
      congrArg Hom.toLRSHom e.hom_inv_id
    have hψinv : ψ.inv ≫ Y.restrictOpenι hY (V j)
        = Y'.restrictOpenι hY' ((Opens.map e.inv.toLRSHom.base).obj (V j)) ≫ e.inv.toLRSHom := by
      rw [← Y'.restrictOpenIso_inv_comp hY' ((Opens.map e.inv.toLRSHom.base).obj (V j))
        (Y.restrictOpenι hY (V j) ≫ e.hom.toLRSHom) hrange, ← hψ, Category.assoc,
        Category.assoc, hehom, Category.comp_id]
    have hge : (g ≫ e.hom).toLRSHom ≫ e.inv.toLRSHom = g.toLRSHom := by
      change g.toLRSHom ≫ e.hom.toLRSHom ≫ e.inv.toLRSHom = g.toLRSHom
      rw [hehom, Category.comp_id]
    have hmap : (χ.hom.toLRSHom ≫ X.restrictOpenMap hX Y' hY' (g ≫ e.hom).toLRSHom
          ((Opens.map e.inv.toLRSHom.base).obj (V j))) ≫ ψ.inv
        = X.restrictOpenMap hX Y hY g.toLRSHom (V j) := by
      refine X.restrictOpenMap_uniq hX Y hY g.toLRSHom (V j) _ ?_
      simp only [Category.assoc]
      rw [hψinv, restrictOpenMap_comp_ι_assoc, hge, ← Category.assoc, hχcomp]
    refine isSeparatedOverSpf_of_iso hI
      { hom := χ.hom.toLRSHom, inv := χ.inv.toLRSHom
        hom_inv_id := congrArg Hom.toLRSHom χ.hom_inv_id
        inv_hom_id := congrArg Hom.toLRSHom χ.inv_hom_id } ?_ hj
    simp only [Iso.trans_hom, Iso.symm_hom, ← Category.assoc]
    rw [hmap]

end AlgebraicGeometry.FormalScheme

end
