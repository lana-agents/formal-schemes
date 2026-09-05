import FormalSchemes.AdicSectionsChart
import FormalSchemes.OpenFormalSubscheme

set_option linter.style.header false

/-!
# Adicity over `ψ` on an open formal subscheme is a condition on charts of the ambient

`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG` (`FormalSchemes.AdicSectionsChart`) is a
condition on the charts of its own source. When that source is an **open** of something else —
`AlgebraicGeometry.FormalScheme.restrictOpen` (`FormalSchemes.OpenFormalSubscheme`) — a chart of it
is not an object the ambient's own results are about, and neither is the ring homomorphism `ψ`,
which lands in the global sections of the restriction rather than in the sections of the ambient
over the open. Both gaps are bookkeeping, and this file closes them.

## What the condition becomes

The homomorphisms `ψ` that arise this way all factor as
`AlgebraicGeometry.FormalScheme.restrictOpenTopSectionsHom` after a homomorphism
`φ : R →+* Γ (X, U)`, and for those
`AlgebraicGeometry.FormalScheme.adicSectionsLocallyFG_restrictOpen_iff` says

```
AdicSectionsLocallyFG I ((restrictOpenTopSectionsHom X hX U).comp φ) ↔
  ∀ y ∈ U, ∃ (d : AffineChart X y) (hd : Set.range d.map.base ⊆ U),
    d.I.FG ∧ I ≤ d.I.comap ((d.opensSectionsHom U hd).comp φ)
```

— a condition on charts of `X` that happen to sit inside `U`, with no restriction, no `⊤` and no
lifting in it. **It is an equivalence, not an implication.** That matters for a caller that expects
the answer to be *no*: a chart family of `X` inside `U` for which the bound provably fails refutes
the predicate at the restriction, which a one-way criterion would not give.

## The two halves of the dictionary

`AlgebraicGeometry.FormalScheme.AffineChart.ofRestrictOpen` lifts a chart of `X` whose range is
inside `U` to a chart of `X.restrictOpen hX U` — this is
`AlgebraicGeometry.FormalScheme.exists_lifted_affineChart`
(`FormalSchemes.OpenImmersionSourceFormalScheme`) in the bundled
`AlgebraicGeometry.FormalScheme.AffineChart` spelling, with the factorisation
`AlgebraicGeometry.FormalScheme.AffineChart.map_ofRestrictOpen_comp` recorded rather than discarded;
`AlgebraicGeometry.FormalScheme.AffineChart.toAmbient` pushes a chart of the restriction forward,
and `AlgebraicGeometry.FormalScheme.AffineChart.range_toAmbient` says the result lands in `U`. The
two are inverse *for the purpose of the bound* — not literally, because the lift is
`CategoryTheory.IsOpenImmersion.lift`, defined through a pullback — and that is all the equivalence
needs.

## The one piece of algebra

Everything about `ψ` runs through
`AlgebraicGeometry.LocallyRingedSpace.sectionsMapOfRangeSubset`: the section map of a morphism `f`
over an open `U` containing its range, landing in the *global* sections of the source because
`AlgebraicGeometry.opens_map_obj_eq_top_of_range_subset` says the preimage of `U` is everything.
`AlgebraicGeometry.LocallyRingedSpace.sectionsMapOfRangeSubset_comp` is its functoriality, and it is
the only computation here: with `f` the inclusion of the open subscheme and `g` a chart of the
restriction, it turns the chart-restriction of `ψ` into the section map of the *composite* chart,
which is a chart of `X`.

Its proof is `CategoryTheory.NatTrans.naturality` of `f.c` at an `CategoryTheory.eqToHom` between
two spellings of the same open, isolated as
`AlgebraicGeometry.LocallyRingedSpace.c_app_comp_map_eqToHom` so that the `subst` that discharges it
happens once.

## Main definitions and results

* `AlgebraicGeometry.opens_map_obj_eq_top_of_range_subset`: a morphism whose range lies in `U` has
  `U` for its preimage everything.
* `AlgebraicGeometry.LocallyRingedSpace.c_app_comp_map_eqToHom`,
  `AlgebraicGeometry.LocallyRingedSpace.sectionsMapOfRangeSubset`,
  `AlgebraicGeometry.LocallyRingedSpace.sectionsMapOfRangeSubset_comp`,
  `AlgebraicGeometry.LocallyRingedSpace.sectionsMapOfRangeSubset_comp_opens` and
  `AlgebraicGeometry.LocallyRingedSpace.sectionsMapOfRangeSubset_congr`: the section map over `U`
  and its functoriality, in the two forms a composite can take.
* `AlgebraicGeometry.FormalScheme.AffineChart.opensSectionsHom`: the chart-restriction of a
  homomorphism into `Γ (X, U)`, the analogue of
  `AlgebraicGeometry.FormalScheme.AffineChart.sectionsHom` one open down.
* `AlgebraicGeometry.FormalScheme.restrictOpenTopSectionsHom`: sections over `U` as global sections
  of `X.restrictOpen hX U`.
* `AlgebraicGeometry.FormalScheme.AffineChart.ofRestrictOpen` /
  `AlgebraicGeometry.FormalScheme.AffineChart.map_ofRestrictOpen_comp` and
  `AlgebraicGeometry.FormalScheme.AffineChart.toAmbient` /
  `AlgebraicGeometry.FormalScheme.AffineChart.range_toAmbient`: the charts, both ways.
* `AlgebraicGeometry.FormalScheme.AffineChart.sectionsHom_ofRestrictOpen` and
  `AlgebraicGeometry.FormalScheme.AffineChart.opensSectionsHom_toAmbient`: the bound is the same
  bound on either side.
* `AlgebraicGeometry.FormalScheme.adicSectionsLocallyFG_restrictOpen_iff`: **the criterion.**
* `AlgebraicGeometry.FormalScheme.AffineChart.opensSectionsHom_basicOpenRefine`,
  `AlgebraicGeometry.FormalScheme.AffineChart.le_comap_opensSectionsHom_basicOpenRefine` and
  `AlgebraicGeometry.FormalScheme.exists_affineChart_subset_opensSectionsHom`: the charts the
  criterion asks for are a neighbourhood basis, so a witness may be cut down into any patch.

## What is *not* proved here

**No witness of `AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG` is produced**, at any source,
and nothing here says the condition holds anywhere. This file changes where the condition is
*asked*: at charts of an ambient formal scheme rather than at charts of an open of it. A source for
which no chart of the ambient inside `U` carries the bound is not excluded by anything below — that
is exactly what the right-to-left direction of the criterion would refute, and it is not proved
either.

The criterion also says nothing about
`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.OverlapAdic`, whose charts live on the
overlaps of a cover and not on the source, and whose status
`FormalSchemes.AdicSectionsChart`'s module docstring records as open.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4 (10.4.6), §10.6.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry CategoryTheory.Limits
open FormalSpectrum

namespace AlgebraicGeometry

/-- **A morphism whose range is inside `U` has all of its source over `U`.** The preimage in the
statement is the one `CategoryTheory.NatTrans.app` of a morphism's comparison map is indexed by, so
this is what lets a section over `U` be restricted to a *global* section of the source. -/
theorem opens_map_obj_eq_top_of_range_subset {W Y : LocallyRingedSpace.{u}} (f : W ⟶ Y)
    (U : Opens Y) (h : Set.range f.base ⊆ (U : Set Y)) :
    (Opens.map f.base).obj U = ⊤ := by
  ext z
  simp only [Opens.map_coe, Set.mem_preimage, Opens.coe_top, Set.mem_univ, iff_true]
  exact h ⟨z, rfl⟩

namespace LocallyRingedSpace

set_option backward.isDefEq.respectTransparency false in
/-- **Naturality of a morphism's comparison map at an equality of opens.** Both `Opens` are the
same object up to the given equality, so `subst` reduces this to the identity square; it is
separated out because the `subst` cannot happen once the equality has been consumed by an
`CategoryTheory.eqToHom` inside a larger composite. -/
theorem c_app_comp_map_eqToHom {V W : LocallyRingedSpace.{u}} (g : V ⟶ W) {A B : Opens W}
    (hAB : A = B) :
    g.c.app (op A) ≫ V.presheaf.map
        (eqToHom (congrArg (Opens.map g.base).obj hAB).symm).op
      = W.presheaf.map (eqToHom hAB.symm).op ≫ g.c.app (op B) := by
  subst hAB
  simp only [eqToHom_refl, op_id, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-- **The section map of `f` over an open containing its range, read on global sections of the
source.** This is `f.c.app` at `U` followed by the transport along
`AlgebraicGeometry.opens_map_obj_eq_top_of_range_subset`; the transport is what makes the target
`Γ (W, ⊤)` rather than `Γ (W, f⁻¹ U)`, which is the side a chart-restriction of a homomorphism is
stated on. -/
def sectionsMapOfRangeSubset {W Y : LocallyRingedSpace.{u}} (f : W ⟶ Y) (U : Opens Y)
    (h : Set.range f.base ⊆ (U : Set Y)) :
    Y.presheaf.obj (op U) ⟶ W.presheaf.obj (op ⊤) :=
  f.c.app (op U) ≫ W.presheaf.map (eqToHom (opens_map_obj_eq_top_of_range_subset f U h).symm).op

set_option backward.isDefEq.respectTransparency false in
/-- **Functoriality.** Restricting a section over `U` to the source of `g ≫ f` is restricting it to
the source of `f` and then along `g`. This is the whole computational content of the file: with `f`
the inclusion of an open formal subscheme and `g` a chart of it, the left-hand side is a chart of
the *ambient* and the right-hand side is the chart-restriction of `ψ`. -/
theorem sectionsMapOfRangeSubset_comp {V W Y : LocallyRingedSpace.{u}} (g : V ⟶ W) (f : W ⟶ Y)
    (U : Opens Y) (hf : Set.range f.base ⊆ (U : Set Y))
    (hgf : Set.range (g ≫ f).base ⊆ (U : Set Y)) :
    sectionsMapOfRangeSubset (g ≫ f) U hgf =
      sectionsMapOfRangeSubset f U hf ≫ g.c.app (op ⊤) := by
  rw [sectionsMapOfRangeSubset, sectionsMapOfRangeSubset, LocallyRingedSpace.comp_c_app,
    Category.assoc, Category.assoc, ← c_app_comp_map_eqToHom g
      (opens_map_obj_eq_top_of_range_subset f U hf)]

set_option backward.isDefEq.respectTransparency false in
/-- **Functoriality when only the composite lands in `U`.** The variant above needs `f`'s own range
inside `U`; a chart of a glued object factors through a patch inclusion whose range is *not* inside
`U`, and this is the form that case takes: the intermediate ring is the sections of the patch over
the preimage of `U`, not its global sections.

Nothing below uses it. It is here because it is the hinge of any patch-by-patch check of
`AlgebraicGeometry.FormalScheme.adicSectionsLocallyFG_restrictOpen_iff` on a source presented by a
`AlgebraicGeometry.FormalScheme.GlueData`, and it is the same one-line naturality as the variant
above. -/
theorem sectionsMapOfRangeSubset_comp_opens {V W Y : LocallyRingedSpace.{u}} (g : V ⟶ W)
    (f : W ⟶ Y) (U : Opens Y)
    (hg : Set.range g.base ⊆ SetLike.coe ((Opens.map f.base).obj U))
    (hgf : Set.range (g ≫ f).base ⊆ (U : Set Y)) :
    sectionsMapOfRangeSubset (g ≫ f) U hgf =
      f.c.app (op U) ≫ sectionsMapOfRangeSubset g ((Opens.map f.base).obj U) hg := by
  rw [sectionsMapOfRangeSubset, sectionsMapOfRangeSubset, LocallyRingedSpace.comp_c_app,
    Category.assoc]

/-- **It depends on the morphism and not on the containment proof**, so an equality of morphisms
transports it. Needed because the containment is an argument, so a plain `rw` at the morphism does
not typecheck. -/
theorem sectionsMapOfRangeSubset_congr {W Y : LocallyRingedSpace.{u}} {f f' : W ⟶ Y}
    (hff : f = f') (U : Opens Y) (h : Set.range f.base ⊆ (U : Set Y))
    (h' : Set.range f'.base ⊆ (U : Set Y)) :
    sectionsMapOfRangeSubset f U h = sectionsMapOfRangeSubset f' U h' := by
  subst hff; rfl

end LocallyRingedSpace

namespace FormalScheme

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable {X : FormalScheme.{u}} {x : X}

/-- **The chart-restriction of a homomorphism into the sections over `U`**, at a chart whose range
is inside `U`. This is `AlgebraicGeometry.FormalScheme.AffineChart.sectionsHom` with `Γ (X, ⊤)`
replaced by `Γ (X, U)`; the two agree once the chart is read on the open formal subscheme
(`AlgebraicGeometry.FormalScheme.AffineChart.sectionsHom_ofRestrictOpen`). -/
def AffineChart.opensSectionsHom (c : AffineChart X x) (U : Opens X)
    (h : Set.range c.map.base ⊆ (U : Set X)) : X.presheaf.obj (op U) →+* c.R :=
  (globalSectionsEquiv c.I).toRingHom.comp
    (LocallyRingedSpace.sectionsMapOfRangeSubset c.map U h).hom

variable (X)

/-- The range of the inclusion of an open formal subscheme is contained in that open — it is equal
to it, by `AlgebraicGeometry.FormalScheme.range_restrictOpenι_base`; this is the containment form
every construction below asks for. -/
theorem range_restrictOpenι_subset (hX : X.LocallyFG) (U : Opens X) :
    Set.range (X.restrictOpenι hX U).base ⊆ (U : Set X) :=
  (range_restrictOpenι_base X hX U).le

/-- **Sections over `U` are global sections of the open formal subscheme `X|_U`.** Every `ψ` this
file is about is this homomorphism after one into `Γ (X, U)`. -/
def restrictOpenTopSectionsHom (hX : X.LocallyFG) (U : Opens X) :
    X.presheaf.obj (op U) →+* (X.restrictOpen hX U).presheaf.obj (op ⊤) :=
  (LocallyRingedSpace.sectionsMapOfRangeSubset (X.restrictOpenι hX U) U
    (range_restrictOpenι_subset X hX U)).hom

/-! ### Charts of an open formal subscheme, both ways -/

variable {X}

/-- **A chart of `X` sitting inside `U`, lifted to a chart of `X.restrictOpen hX U`.** This is
`AlgebraicGeometry.FormalScheme.exists_lifted_affineChart`
(`FormalSchemes.OpenImmersionSourceFormalScheme`) in the bundled
`AlgebraicGeometry.FormalScheme.AffineChart` spelling: same ring, same ideal of definition, and the
morphism replaced by its lift through the inclusion. The open-immersion field is supplied
explicitly — instance synthesis does not find it inside a structure literal, exactly as
`AlgebraicGeometry.FormalScheme.AffineChart.ofSpf` records. -/
def AffineChart.ofRestrictOpen (hX : X.LocallyFG) (U : Opens X)
    {x : X.restrictOpen hX U} (d : AffineChart X ((X.restrictOpenι hX U).base x))
    (hsub : Set.range d.map.base ⊆ (U : Set X)) : AffineChart (X.restrictOpen hX U) x :=
  have hr : Set.range d.map.base ⊆ Set.range (X.restrictOpenι hX U).base := by
    rw [range_restrictOpenι_base]; exact hsub
  have hoi : LocallyRingedSpace.IsOpenImmersion
      (LocallyRingedSpace.IsOpenImmersion.lift (X.restrictOpenι hX U) d.map hr) := by
    haveI := LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset
      (X.restrictOpenι hX U) d.map hr
    have hlift : LocallyRingedSpace.IsOpenImmersion.lift (X.restrictOpenι hX U) d.map hr
        = inv (pullback.snd (X.restrictOpenι hX U) d.map) ≫
          pullback.fst (X.restrictOpenι hX U) d.map := rfl
    rw [hlift]
    infer_instance
  { R := d.R, I := d.I,
    map := LocallyRingedSpace.IsOpenImmersion.lift (X.restrictOpenι hX U) d.map hr,
    mem := by
      rw [LocallyRingedSpace.IsOpenImmersion.lift_range]
      exact d.mem
    isOpenImmersion := hoi }

/-- **The lift factors the original chart through the inclusion.** This is the half of the
construction the bound travels along; without it the lifted chart would be a chart of the
restriction about which nothing is known. -/
theorem AffineChart.map_ofRestrictOpen_comp (hX : X.LocallyFG) (U : Opens X)
    {x : X.restrictOpen hX U} (d : AffineChart X ((X.restrictOpenι hX U).base x))
    (hsub : Set.range d.map.base ⊆ (U : Set X)) :
    (d.ofRestrictOpen hX U hsub).map ≫ X.restrictOpenι hX U = d.map :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _
    (by rw [range_restrictOpenι_base]; exact hsub)

/-- **A chart of `X.restrictOpen hX U`, pushed forward to a chart of `X`**: compose with the
inclusion. Unlike the lift this is a plain composite, which is why the bound is *literally* the
same on both sides (`AlgebraicGeometry.FormalScheme.AffineChart.opensSectionsHom_toAmbient`). -/
def AffineChart.toAmbient (hX : X.LocallyFG) (U : Opens X)
    {x : X.restrictOpen hX U} (c : AffineChart (X.restrictOpen hX U) x) :
    AffineChart X ((X.restrictOpenι hX U).base x) where
  R := c.R
  I := c.I
  map := c.map ≫ X.restrictOpenι hX U
  mem := by
    obtain ⟨w, hw⟩ := c.mem
    exact ⟨w, by simp only [LocallyRingedSpace.comp_base, TopCat.comp_app, hw]⟩

/-- **The pushed-forward chart lands inside `U`**, so it is admissible for the criterion below. -/
theorem AffineChart.range_toAmbient (hX : X.LocallyFG) (U : Opens X)
    {x : X.restrictOpen hX U} (c : AffineChart (X.restrictOpen hX U) x) :
    Set.range (c.toAmbient hX U).map.base ⊆ (U : Set X) := by
  intro z hz
  obtain ⟨w, rfl⟩ := hz
  rw [← range_restrictOpenι_base X hX U]
  exact ⟨c.map.base w, (TopCat.comp_app _ _ w).symm⟩

/-! ### The chart-restriction of a `ψ` that comes from sections over `U` -/

omit [TopologicalSpace R] in
/-- **The chart-restriction of `ψ` at a lifted chart is the `U`-restriction at the chart it was
lifted from.** `AlgebraicGeometry.LocallyRingedSpace.sectionsMapOfRangeSubset_comp` at the
inclusion and the lift, with
`AlgebraicGeometry.FormalScheme.AffineChart.map_ofRestrictOpen_comp` identifying the composite. -/
theorem AffineChart.sectionsHom_ofRestrictOpen (hX : X.LocallyFG) (U : Opens X)
    {x : X.restrictOpen hX U} (d : AffineChart X ((X.restrictOpenι hX U).base x))
    (hsub : Set.range d.map.base ⊆ (U : Set X)) (φ : R →+* X.presheaf.obj (op U)) :
    (d.ofRestrictOpen hX U hsub).sectionsHom ((restrictOpenTopSectionsHom X hX U).comp φ)
      = (d.opensSectionsHom U hsub).comp φ := by
  have key : LocallyRingedSpace.sectionsMapOfRangeSubset (X.restrictOpenι hX U) U
        (range_restrictOpenι_subset X hX U)
        ≫ (d.ofRestrictOpen hX U hsub).map.c.app (op ⊤)
      = LocallyRingedSpace.sectionsMapOfRangeSubset d.map U hsub := by
    rw [← LocallyRingedSpace.sectionsMapOfRangeSubset_comp]
    · exact LocallyRingedSpace.sectionsMapOfRangeSubset_congr
        (AffineChart.map_ofRestrictOpen_comp hX U d hsub) U _ _
    · rw [AffineChart.map_ofRestrictOpen_comp]
      exact hsub
  rw [AffineChart.sectionsHom, AffineChart.opensSectionsHom, restrictOpenTopSectionsHom,
    ← RingHom.comp_assoc, ← CommRingCat.hom_comp, key, RingHom.comp_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [TopologicalSpace R] in
/-- **And at a pushed-forward chart it is the chart-restriction of `ψ` itself.** Same lemma, with
the composite already on the nose. -/
theorem AffineChart.opensSectionsHom_toAmbient (hX : X.LocallyFG) (U : Opens X)
    {x : X.restrictOpen hX U} (c : AffineChart (X.restrictOpen hX U) x)
    (φ : R →+* X.presheaf.obj (op U)) :
    ((c.toAmbient hX U).opensSectionsHom U (c.range_toAmbient hX U)).comp φ
      = c.sectionsHom ((restrictOpenTopSectionsHom X hX U).comp φ) := by
  have key : LocallyRingedSpace.sectionsMapOfRangeSubset (c.toAmbient hX U).map U
        (c.range_toAmbient hX U)
      = LocallyRingedSpace.sectionsMapOfRangeSubset (X.restrictOpenι hX U) U
          (range_restrictOpenι_subset X hX U) ≫ c.map.c.app (op ⊤) :=
    LocallyRingedSpace.sectionsMapOfRangeSubset_comp _ _ _ _ _
  rw [AffineChart.sectionsHom, AffineChart.opensSectionsHom, restrictOpenTopSectionsHom, key,
    CommRingCat.hom_comp, RingHom.comp_assoc]
  rfl

/-! ### The criterion -/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Adicity over `ψ` on an open formal subscheme is adicity over `φ` at charts of the ambient
inside the open.** Both directions are the two chart constructions above together with the fact
that the bound is the same bound on either side; nothing else enters.

The right-to-left direction is what a *positive* answer would be produced by: exhibit, at each
point of `U`, one finitely generated chart of `X` inside `U` carrying the bound. The left-to-right
direction is what a *negative* answer would be produced by: if no chart of `X` inside `U` carries
it, the predicate fails at the restriction. Neither is proved of any particular `X`, `U` or `φ`
here. -/
theorem adicSectionsLocallyFG_restrictOpen_iff (hX : X.LocallyFG) (U : Opens X)
    (φ : R →+* X.presheaf.obj (op U)) :
    AdicSectionsLocallyFG I ((restrictOpenTopSectionsHom X hX U).comp φ) ↔
      ∀ y ∈ (U : Set X), ∃ (d : AffineChart X y) (hd : Set.range d.map.base ⊆ (U : Set X)),
        d.I.FG ∧ I ≤ d.I.comap ((d.opensSectionsHom U hd).comp φ) := by
  constructor
  · intro h y hy
    rw [← range_restrictOpenι_base X hX U] at hy
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨c, hfg, hcont⟩ := h x
    refine ⟨c.toAmbient hX U, c.range_toAmbient hX U, hfg, ?_⟩
    rw [AffineChart.opensSectionsHom_toAmbient]
    exact hcont
  · intro h x
    have hy : (X.restrictOpenι hX U).base x ∈ (U : Set X) := by
      rw [← range_restrictOpenι_base X hX U]
      exact ⟨x, rfl⟩
    obtain ⟨d, hd, hfg, hcont⟩ := h _ hy
    refine ⟨d.ofRestrictOpen hX U hd, hfg, ?_⟩
    rw [AffineChart.sectionsHom_ofRestrictOpen]
    exact hcont

/-! ### The charts of the criterion are a neighbourhood basis -/

omit [TopologicalSpace R] [IsAdicRing I] in
set_option backward.isDefEq.respectTransparency false in
/-- **The `U`-restriction of `φ` along a basic-open refinement factors through the refinement.**
This is `AlgebraicGeometry.FormalScheme.AffineChart.sectionsHom_basicOpenRefine` one open down, and
it has the same subtlety: it is **not** `rfl`, because the two
`FormalSpectrum.globalSectionsEquiv` round-trips cancel only propositionally — here that
cancellation is `RingEquiv.symm_toRingHom_comp_toRingHom` rather than a `simp` step, and the `rfl`
at the end closes only the two spellings of the refinement's ideal of definition. -/
theorem AffineChart.opensSectionsHom_basicOpenRefine (c : AffineChart X x) (U : Opens X) (g : c.R)
    [IsAdicRing (awayCompletionIdeal c.I g)]
    [LocallyRingedSpace.IsOpenImmersion (basicOpenChart c.I g ≫ c.map)]
    (hmem : x ∈ Set.range (basicOpenChart c.I g ≫ c.map).base)
    (h : Set.range c.map.base ⊆ (U : Set X))
    (h' : Set.range (c.basicOpenRefine g hmem).map.base ⊆ (U : Set X)) :
    (c.basicOpenRefine g hmem).opensSectionsHom U h' =
      (globalSectionsMap c.I (awayCompletionIdeal c.I g) (basicOpenChart c.I g)).comp
        (c.opensSectionsHom U h) := by
  have key : LocallyRingedSpace.sectionsMapOfRangeSubset (c.basicOpenRefine g hmem).map U h'
      = LocallyRingedSpace.sectionsMapOfRangeSubset c.map U h
          ≫ (basicOpenChart c.I g).c.app (op ⊤) :=
    LocallyRingedSpace.sectionsMapOfRangeSubset_comp _ _ _ _ _
  rw [AffineChart.opensSectionsHom, key, CommRingCat.hom_comp, AffineChart.opensSectionsHom,
    globalSectionsMap, RingHom.comp_assoc, RingHom.comp_assoc,
    ← RingHom.comp_assoc (LocallyRingedSpace.sectionsMapOfRangeSubset c.map U h).hom
      (globalSectionsEquiv c.I).toRingHom (globalSectionsEquiv c.I).symm.toRingHom,
    RingEquiv.symm_toRingHom_comp_toRingHom, RingHom.id_comp]
  rfl

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The bound of the criterion travels to a refinement.** Immediate from the factorisation above
and `FormalSpectrum.basicOpenChart_le_comap_globalSectionsMap`, exactly as
`AlgebraicGeometry.FormalScheme.AffineChart.le_comap_sectionsHom_basicOpenRefine` is at `⊤`. -/
theorem AffineChart.le_comap_opensSectionsHom_basicOpenRefine (c : AffineChart X x) (U : Opens X)
    (g : c.R) [IsAdicRing (awayCompletionIdeal c.I g)]
    [LocallyRingedSpace.IsOpenImmersion (basicOpenChart c.I g ≫ c.map)]
    (hmem : x ∈ Set.range (basicOpenChart c.I g ≫ c.map).base)
    (h : Set.range c.map.base ⊆ (U : Set X))
    (h' : Set.range (c.basicOpenRefine g hmem).map.base ⊆ (U : Set X))
    (φ : R →+* X.presheaf.obj (op U))
    (hc : I ≤ c.I.comap ((c.opensSectionsHom U h).comp φ)) :
    I ≤ (c.basicOpenRefine g hmem).I.comap
      (((c.basicOpenRefine g hmem).opensSectionsHom U h').comp φ) := by
  rw [AffineChart.opensSectionsHom_basicOpenRefine c U g hmem h h']
  intro a ha
  simp only [Ideal.mem_comap, RingHom.comp_apply]
  exact basicOpenChart_le_comap_globalSectionsMap c.I g (hc ha)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The charts the criterion asks for are a neighbourhood basis**: a witness at a point can be
shrunk into any given open neighbourhood of it and keeps both the containment in `U` and the bound.

This is what makes the criterion checkable patch by patch on a source presented as a glued object:
a witness produced anywhere inside `U` may be cut down to sit inside one patch as well. It is the
`AlgebraicGeometry.FormalScheme.AffineChart.opensSectionsHom` analogue of
`AlgebraicGeometry.FormalScheme.exists_affineChart_subset_adicSections`, and it goes through the
same `AlgebraicGeometry.FormalScheme.exists_basicOpenRefine_subset`, applied to `W ∩ U`. -/
theorem exists_affineChart_subset_opensSectionsHom (U : Opens X)
    (φ : R →+* X.presheaf.obj (op U)) {y : X} (hy : y ∈ U)
    (hcrit : ∃ (d : AffineChart X y) (hd : Set.range d.map.base ⊆ (U : Set X)),
      d.I.FG ∧ I ≤ d.I.comap ((d.opensSectionsHom U hd).comp φ))
    (W : Set X) (hW : IsOpen W) (hyW : y ∈ W) :
    ∃ (d : AffineChart X y) (hd : Set.range d.map.base ⊆ (U : Set X)),
      d.I.FG ∧ Set.range d.map.base ⊆ W ∧
        I ≤ d.I.comap ((d.opensSectionsHom U hd).comp φ) := by
  obtain ⟨c, hcU, hfg, hb⟩ := hcrit
  obtain ⟨g, _, _, hmem, hsub⟩ :=
    exists_basicOpenRefine_subset c hfg (W ∩ (U : Set X)) (hW.inter U.isOpen) ⟨hyW, hy⟩
  refine ⟨c.basicOpenRefine g hmem, hsub.trans Set.inter_subset_right,
    awayCompletionIdeal_fg c.I g hfg, hsub.trans Set.inter_subset_left, ?_⟩
  exact c.le_comap_opensSectionsHom_basicOpenRefine I U g hmem hcU _ φ hb

end FormalScheme

end AlgebraicGeometry

end
