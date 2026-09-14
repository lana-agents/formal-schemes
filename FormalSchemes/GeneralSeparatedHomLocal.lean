import FormalSchemes.GeneralSeparatedHom
import FormalSchemes.NestedOpenFormalSubscheme

set_option linter.style.header false

/-!
# Separatedness of a morphism of formal schemes is local on the target, in one direction

`FormalScheme.IsSeparatedHom` (`FormalSchemes.GeneralSeparatedHom`) is defined by the existence of
**one** cover of the target with affine restrictions. A predicate of that shape says nothing about
any other cover until someone proves it does, and nothing on the tree related the predicate at two
different covers in either direction. This file supplies the gluing direction:

```
FormalScheme.isSeparatedHom_of_cover : (⋃ k, W k) = univ →
  (∀ k, IsSeparatedHom _ _ (X.restrictOpenSchemeMap hX Y hY g (W k))) → IsSeparatedHom hX hY g
```

The opens `W k` are **arbitrary** — not required to be affine, not required to come from any cover
the predicate itself produced. So separatedness of `g : X ⟶ Y` may be checked on any open cover of
`Y` whatever, by checking it for each restricted morphism `X|_{g⁻¹W k} ⟶ Y|_{W k}`.

## How the cover is assembled

Each hypothesis `h k` supplies a cover `V k j` of `Y|_{W k}` by opens with affine restriction. The
cover of `Y` produced here is the union over `k` of the images of those in `Y`, indexed by
`Σ k, J k` — `FormalScheme.openOfNested` (`FormalSchemes.NestedOpenFormalSubscheme`) is the image,
`FormalScheme.mem_openOfNested` is what makes it still a cover, and
`FormalScheme.openOfNested_le` is what makes each piece land inside its own `W k`, which is the
hypothesis the comparison needs.

The affine identification at `⟨k, j⟩` is the one `h k` supplies for `V k j`, composed with
`FormalScheme.restrictOpenNestedIso`; the source clause is transported along the *other* nesting
comparison by `FormalScheme.isSeparatedOverSpf_of_iso`, and the compatibility that makes those two
transports agree is `FormalScheme.restrictOpenMap_nested`. That per-chart step is
`FormalScheme.chart_clause_of_nested`, stated separately because it is the whole of the content
and none of the bookkeeping.

## What this settles, and what it does not

* It settles that `FormalScheme.IsSeparatedHom` is **local on the target in the gluing direction**.
  Before it, the predicate was tied to whichever cover its witness happened to name.
* It does **not** give the **refinement** direction — from a witness at one cover to a witness at a
  finer one. That is the half `FormalSchemes.GeneralSeparatedHom`'s not-proved list actually needs
  for a composition law, since refining the target cover against two morphisms is exactly what that
  list names as the obstruction. It would require `FormalScheme.IsSeparatedOverSpf` to restrict to
  an open subscheme over an open of the affine base, which is a statement about the
  presentation-level predicate `BothChartedFibreDatumXY.IsSeparated` and is nowhere on the tree.
  **Nothing here should be read as bringing the composition law close.**
* It does **not** touch conservativity's hard direction, which needs a basic-open refinement of the
  target cover and is recorded in the same list.
* `FormalScheme.isSeparatedHom_of_cover` has **zero** consumers on landing: a comment-stripped
  count over every file of this library finds the name once, in its own declaration below. Eight of
  the ten declarations of `FormalSchemes.NestedOpenFormalSubscheme` are consumed here, and here
  only; the remaining two, `FormalScheme.range_nestedι` and
  `FormalScheme.restrictOpenNestedIso_hom_comp`, are used inside that module and nowhere else.
  So this is a structural theorem about the predicate rather than an ingredient of a value, and
  it is worth having for the same reason `FormalScheme.IsSeparatedHom.of_iso` is: a predicate one
  cannot move between presentations is a definition that elaborates rather than a notion.

## Placement

`FormalSchemes.GeneralSeparatedHom` is where this belongs on subject matter, and that module has
reverse closure **5**, against `FormalSchemes.OpenFormalSubscheme`'s **75** one file down — so
the hub is cheap here in a way it is not there, and cost does not decide the placement. It is a
new module anyway, for a reason that is not cost: `FormalSchemes.GeneralSeparatedHom` does not
import `FormalSchemes.NestedOpenFormalSubscheme`, and putting this theorem into the hub would
push that import onto everything the hub reaches in order to serve a theorem with no consumer.

`FormalSchemes.GeneralSeparatedHomLocal` has reverse closure **0** and forward closure **182**,
against `FormalSchemes.GeneralSeparatedHom`'s forward closure of **180**. The difference is that
module itself together with `FormalSchemes.NestedOpenFormalSubscheme`, whose own forward closure
of **33** already lies inside it.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
-/

noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry FormalSpectrum

universe u

namespace AlgebraicGeometry.FormalScheme

variable {X Y : FormalScheme.{u}}

section

variable (hX : X.LocallyFG) (hY : Y.LocallyFG) (g : X ⟶ Y)
variable {R : Type u} [CommRing R] [TopologicalSpace R] {I : Ideal R} [IsAdicRing I]

/-- **The per-chart clause transports to the smaller open.** Given `W' ≤ W` and the clause of
`FormalScheme.IsSeparatedHom` for the nested open `V` of `Y|_W` cut out by `W'`, the clause holds
for `W'` itself, at the same ring.

The target identification is `FormalScheme.restrictOpenNestedIso` composed with the one in hand;
the source clause moves along the other nesting comparison by
`FormalScheme.isSeparatedOverSpf_of_iso`, the two being compatible by
`FormalScheme.restrictOpenMap_nested`. The final step is closed with
`simp only [Category.assoc, Iso.hom_inv_id_assoc]` and not with more `rw`: inside a long `rw`
chain `Category.assoc` fires on the wrong occurrence, after which `Iso.hom_inv_id_assoc` reports
*"Did not find an occurrence"* against a goal that visibly contains one. -/
theorem chart_clause_of_nested {W W' : Opens Y} (hW' : W' ≤ W)
    {V : Opens (Y.restrictOpen hY W)} (hV : Y.nestedOpen hY W W' = V) (hI : I.FG)
    (e : ((Y.restrictOpen hY W).restrictOpen (Y.restrictOpen_locallyFG hY W)
        V).toLocallyRingedSpace ≅ locallyRingedSpaceObj I)
    (hj : IsSeparatedOverSpf hI
      ((X.restrictOpen hX ((Opens.map g.toLRSHom.base).obj W)).restrictOpen
        (X.restrictOpen_locallyFG hX _)
        ((Opens.map (X.restrictOpenMap hX Y hY g.toLRSHom W).base).obj V))
      ((X.restrictOpen hX ((Opens.map g.toLRSHom.base).obj W)).restrictOpenMap
          (X.restrictOpen_locallyFG hX _) (Y.restrictOpen hY W) (Y.restrictOpen_locallyFG hY W)
          (X.restrictOpenMap hX Y hY g.toLRSHom W) V ≫ e.hom)) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : TopologicalSpace R') (I' : Ideal R')
      (_ : IsAdicRing I') (hI' : I'.FG)
      (e' : (Y.restrictOpen hY W').toLocallyRingedSpace ≅ locallyRingedSpaceObj I'),
      IsSeparatedOverSpf hI' (X.restrictOpen hX ((Opens.map g.toLRSHom.base).obj W'))
        (X.restrictOpenMap hX Y hY g.toLRSHom W' ≫ e'.hom) := by
  subst hV
  refine ⟨R, inferInstance, inferInstance, I, inferInstance, hI,
    (Y.restrictOpenNestedIso hY (Y.nestedOpen hY W W') rfl hW').symm ≪≫ e, ?_⟩
  refine isSeparatedOverSpf_of_iso hI (X.restrictOpenNestedIso hX
      ((Opens.map (X.restrictOpenMap hX Y hY g.toLRSHom W).base).obj (Y.nestedOpen hY W W'))
      (X.map_restrictOpenMap_nestedOpen hX Y hY g.toLRSHom W W').symm
      (fun _ hx => hW' hx)) ?_ hj
  rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, ← Category.assoc,
    ← X.restrictOpenMap_nested hX Y hY g.toLRSHom W W' hW']
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end

/-- **Separatedness of a morphism is local on the target, in the gluing direction.** If `Y` is
covered by *arbitrary* opens `W k` and every restricted morphism `X|_{g⁻¹W k} ⟶ Y|_{W k}` is
separated, then `g` is separated.

The cover `FormalScheme.IsSeparatedHom` asks for is assembled as the union over `k` of the images
in `Y` of each `W k`'s own affine cover, indexed by `Σ k, J k`; see the module docstring for the
three nesting facts that make each piece's clause go through, and for what this does not settle —
in particular it is **not** the refinement direction and does not bring the composition law
closer. -/
theorem isSeparatedHom_of_cover (hX : X.LocallyFG) (hY : Y.LocallyFG) (g : X ⟶ Y)
    {K : Type u} (W : K → Opens Y) (hcov : (⋃ k, (W k : Set Y)) = Set.univ)
    (h : ∀ k, IsSeparatedHom
      (X.restrictOpen_locallyFG hX ((Opens.map g.toLRSHom.base).obj (W k)))
      (Y.restrictOpen_locallyFG hY (W k))
      (X.restrictOpenSchemeMap hX Y hY g (W k))) :
    IsSeparatedHom hX hY g := by
  choose J V hVcov hsep using h
  refine ⟨Σ k, J k, fun p => Y.openOfNested hY (W p.1) (V p.1 p.2), ?_, ?_⟩
  · refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨_, ⟨k, rfl⟩, hy⟩ := Set.eq_univ_iff_forall.mp hcov y
    obtain ⟨_, ⟨j, rfl⟩, hyj⟩ :=
      Set.eq_univ_iff_forall.mp (hVcov k) (⟨y, hy⟩ : Y.restrictOpen hY (W k))
    exact Set.mem_iUnion.mpr ⟨⟨k, j⟩, Y.mem_openOfNested hY (W k) (V k j) ⟨y, hy⟩ hyj⟩
  · rintro ⟨k, j⟩
    obtain ⟨R, _, _, I, _, hI, e, hj⟩ := hsep k j
    rw [restrictOpenSchemeMap_toLRSHom] at hj
    exact chart_clause_of_nested hX hY g (Y.openOfNested_le hY (W k) (V k j))
      (Y.nestedOpen_openOfNested hY (W k) (V k j)) hI e hj

end AlgebraicGeometry.FormalScheme
