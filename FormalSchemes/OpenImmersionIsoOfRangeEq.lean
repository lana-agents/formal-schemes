import FormalSchemes.CoproductOpenImmersion

set_option linter.style.header false

/-!
# Two open immersions of locally ringed spaces with equal range are isomorphic

Mathlib has the "same range ⟹ canonically isomorphic" principle for open immersions of
`PresheafedSpace`s (`AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoOfRangeEq`) and of
`Scheme`s (`AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq`), but **not** for
`LocallyRingedSpace`s, which is the category formal schemes live in here. This file supplies it,
together with both factorisation laws.

The proof is the same three lines as its two Mathlib siblings, and rests entirely on the universal
property of open immersions of locally ringed spaces already in Mathlib
(`LocallyRingedSpace.IsOpenImmersion.lift`, `lift_fac`, `lift_uniq`): an open immersion is a
monomorphism, so the two lifts are mutually inverse as soon as each round trip commutes with the
structural map.

The file also records the underlying-space range of a coproduct descent map, since identifying a
coproduct of charts with a single chart is the typical way this lemma gets used here.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq`: two open immersions
  `f : X ⟶ Z`, `g : Y ⟶ Z` with `Set.range f.base = Set.range g.base` induce `X ≅ Y`.
* `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_hom_fac` and
  `isoOfRangeEq_inv_fac`: the isomorphism commutes with `f` and `g`.
* `AlgebraicGeometry.LocallyRingedSpace.range_coprodDesc_base`: the range of `coprod.desc f g` is
  the union of the ranges of `f` and `g`.
* `AlgebraicGeometry.LocallyRingedSpace.range_ofRestrict`: the range of `Y|_V ⟶ Y` is `V`.
* `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.opensRange` and `coe_opensRange`: the range
  of an open immersion, as an open of the target.
* `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoRestrictOfRangeEq`: an open immersion
  `j : X ⟶ Y` whose range is an open `U` identifies `Y|_U` with `X`, and
  `isoRestrictOpensRange` is the case `U = opensRange j`.

## Implementation notes

`isoRestrictOfRangeEq` is the single proof of "an open immersion is the restriction to its range",
and the two forms this library asks for are one line each off it:
`AlgebraicGeometry.FormalScheme.restrictOpenIso` (`FormalSchemes.OpenFormalSubscheme`), which takes
the open and a range proof, and `isoRestrictOpensRange`, which takes neither. Two constructions in
the same direction already exist and neither serves, which is why this one is here:

* Mathlib's `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoRestrict`, in this very
  namespace, is `X ≅ Y.restrict H.base_open` — the restriction along the *map*, whose carrier is
  `X`. Every cover hypothesis in the `SpfHom*` cluster and the `local_affine` field of
  `AlgebraicGeometry.FormalScheme` instead ask for the restriction along an `Opens`, whose carrier
  is `↥(Set.range j.base)`, so Mathlib's iso has the wrong type there, not merely the wrong
  direction.
* `AlgebraicGeometry.FormalScheme.restrictOpenIso` is the same term, but stated for
  `X : FormalScheme` with `hX : X.LocallyFG`, hypotheses its proof never uses. It is now a
  `.symm` of `isoRestrictOfRangeEq` rather than a second call of `isoOfRangeEq` (issue 1479).

The names follow Mathlib's at the `Scheme` level — `AlgebraicGeometry.Scheme.Hom.opensRange`
(`Mathlib/AlgebraicGeometry/OpenImmersion.lean`) is the identical construction one level up, and
`isoRestrict…` echoes the `LocallyRingedSpace`-level `isoRestrict` above. Mathlib also ships
`Scheme.Hom.isoOpensRange_hom_ι` and `isoOpensRange_inv_comp`; the analogues are not here because
no call site on this tree needs them — the two triangles that *are* needed,
`FormalScheme.restrictOpenIso_hom_comp` and `_inv_comp`, are stated where `restrictOpenIso` is and
are `isoOfRangeEq_hom_fac`/`_inv_fac` directly.

`range_coprodDesc_base` is the single home of this general locally-ringed-space fact. It was for a
while duplicated as `AlgebraicGeometry.range_coprodDesc_base` in
`FormalSchemes.TateSelfProductBothOverlap`, in the middle of the Tate self-product tower; that copy
has been deleted (issue 617) and its call sites re-pointed here. Keep the statement in this file:
it imports only `FormalSchemes.CoproductOpenImmersion`, so anything in the library may cite it,
whereas the Tate self-product tower drags in the whole completed-tensor interchange chain.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X Y Z : LocallyRingedSpace.{u}}

/-- **The restriction of a locally ringed space to an open has that open as its range.** A
restatement of `Opens.set_range_inclusion'` in the spelling the `IsOpenImmersion.lift` hypotheses
take.

It lives in `AlgebraicGeometry.LocallyRingedSpace` rather than in `FormalSpectrum`: its statement
mentions no ring, no ideal and no spectrum. Issue 1479 moved it here from
`FormalSchemes.ThickeningChartRestrict`, whose import closure of 25 modules put it out of reach of
`isoRestrictOfRangeEq` below; that file still holds the four `range_ofRestrict_comp_*` lemmas
about compatible families, which are not general. -/
theorem range_ofRestrict (Y : LocallyRingedSpace.{u}) (V : Opens Y.toTopCat) :
    Set.range (Y.ofRestrict V.isOpenEmbedding).base = (V : Set Y.toTopCat) :=
  Opens.set_range_inclusion' V

/-- **The underlying-space range of a coproduct descent map is the union of the ranges.** For
`f : X ⟶ Z` and `g : Y ⟶ Z`, the base map of `coprod.desc f g : X ⨿ Y ⟶ Z` has range
`Set.range f.base ∪ Set.range g.base`: the two coproduct inclusions cover `X ⨿ Y`
(`coprod_base_mem_range`) and `coprod.desc f g` restricts along them to `f` and `g`
(`IsOpenImmersion.coprodDesc_base_comp_inl`/`_inr`). No open-immersion hypothesis is needed. -/
theorem range_coprodDesc_base (f : X ⟶ Z) (g : Y ⟶ Z) :
    Set.range (coprod.desc f g).base = Set.range f.base ∪ Set.range g.base := by
  have key_inl : ∀ a, (coprod.desc f g).base ((coprod.inl : X ⟶ X ⨿ Y).base a) = f.base a :=
    fun a => congrArg (fun m => m a) (IsOpenImmersion.coprodDesc_base_comp_inl f g)
  have key_inr : ∀ b, (coprod.desc f g).base ((coprod.inr : Y ⟶ X ⨿ Y).base b) = g.base b :=
    fun b => congrArg (fun m => m b) (IsOpenImmersion.coprodDesc_base_comp_inr f g)
  apply Set.Subset.antisymm
  · rintro _ ⟨w, rfl⟩
    rcases coprod_base_mem_range w with ⟨a, ha⟩ | ⟨b, hb⟩
    · exact Or.inl ⟨a, by rw [← ha, key_inl]⟩
    · exact Or.inr ⟨b, by rw [← hb, key_inr]⟩
  · rintro _ (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · exact ⟨(coprod.inl : X ⟶ X ⨿ Y).base a, key_inl a⟩
    · exact ⟨(coprod.inr : Y ⟶ X ⨿ Y).base b, key_inr b⟩

namespace IsOpenImmersion

variable (f : X ⟶ Z) (g : Y ⟶ Z)
variable [LocallyRingedSpace.IsOpenImmersion f] [LocallyRingedSpace.IsOpenImmersion g]

/-- **Two open immersions of locally ringed spaces with equal range are isomorphic.** The
locally-ringed-space analogue of `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoOfRangeEq`
and of `AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq`: an open subspace of `Z` is determined by
its underlying set, so two open immersions onto the same subset differ by a unique isomorphism of
their sources.

Both directions are the universal-property lift `LocallyRingedSpace.IsOpenImmersion.lift`, and the
two round trips are identities because an open immersion is a monomorphism. -/
def isoOfRangeEq (e : Set.range f.base = Set.range g.base) : X ≅ Y where
  hom := lift g f (le_of_eq e)
  inv := lift f g (le_of_eq e.symm)
  hom_inv_id := by rw [← cancel_mono f]; simp
  inv_hom_id := by rw [← cancel_mono g]; simp

@[reassoc (attr := simp)]
theorem isoOfRangeEq_hom_fac (e : Set.range f.base = Set.range g.base) :
    (isoOfRangeEq f g e).hom ≫ g = f :=
  lift_fac _ _ (le_of_eq e)

@[reassoc (attr := simp)]
theorem isoOfRangeEq_inv_fac (e : Set.range f.base = Set.range g.base) :
    (isoOfRangeEq f g e).inv ≫ f = g :=
  lift_fac _ _ (le_of_eq e.symm)

section OpensRange

variable (j : X ⟶ Y) [H : LocallyRingedSpace.IsOpenImmersion j]

/-- **The range of an open immersion, as an open of the target.** The openness is
`Topology.IsOpenEmbedding.isOpen_range` of `PresheafedSpace.IsOpenImmersion.base_open`.

Named after `AlgebraicGeometry.Scheme.Hom.opensRange`, which is this construction for schemes. -/
def opensRange : Opens Y.toTopCat :=
  ⟨Set.range j.base, H.base_open.isOpen_range⟩

@[simp]
theorem coe_opensRange : (opensRange j : Set Y.toTopCat) = Set.range j.base := rfl

omit H in
/-- **An open immersion with range `U` and the inclusion of `U` have the same range**, in the
spelling `isoOfRangeEq`'s hypothesis takes. Named rather than written out because the three
declarations below all need it and `isoOfRangeEq`'s range argument cannot be synthesised from
their goals. -/
theorem range_ofRestrict_eq_range (U : Opens Y.toTopCat)
    (hj : Set.range j.base = (U : Set Y.toTopCat)) :
    Set.range (Y.ofRestrict U.isOpenEmbedding).base = Set.range j.base :=
  (LocallyRingedSpace.range_ofRestrict Y U).trans hj.symm

/-- **An open immersion whose range is `U` identifies `Y|_U` with its source.** Both `X` and
`Y|_U` are open immersions into `Y` with the same range, so this is `isoOfRangeEq`, whose range
hypothesis is `AlgebraicGeometry.LocallyRingedSpace.range_ofRestrict`.

Every cover-shaped hypothesis on this tree asks for an isomorphism in this direction —
`Y.restrict (U i).isOpenEmbedding ≅ X i`, as in `FormalSpectrum.isThickeningColimitTarget_of_cover`
and in the `local_affine` field of `AlgebraicGeometry.FormalScheme` — while every supply of charts
(`AlgebraicGeometry.FormalScheme.LocallyFG`,
`AlgebraicGeometry.LocallyRingedSpace.HasAffineChartAt`) produces an open immersion instead. This
is the one line between them; see the implementation notes for why neither Mathlib's
`isoRestrict` nor `AlgebraicGeometry.FormalScheme.restrictOpenIso` is that line. -/
def isoRestrictOfRangeEq (U : Opens Y.toTopCat) (hj : Set.range j.base = (U : Set Y.toTopCat)) :
    Y.restrict U.isOpenEmbedding ≅ X :=
  isoOfRangeEq (Y.ofRestrict U.isOpenEmbedding) j (range_ofRestrict_eq_range j U hj)

@[reassoc (attr := simp)]
theorem isoRestrictOfRangeEq_hom_fac (U : Opens Y.toTopCat)
    (hj : Set.range j.base = (U : Set Y.toTopCat)) :
    (isoRestrictOfRangeEq j U hj).hom ≫ j = Y.ofRestrict U.isOpenEmbedding :=
  isoOfRangeEq_hom_fac _ j (range_ofRestrict_eq_range j U hj)

@[reassoc (attr := simp)]
theorem isoRestrictOfRangeEq_inv_fac (U : Opens Y.toTopCat)
    (hj : Set.range j.base = (U : Set Y.toTopCat)) :
    (isoRestrictOfRangeEq j U hj).inv ≫ Y.ofRestrict U.isOpenEmbedding = j :=
  isoOfRangeEq_inv_fac _ j (range_ofRestrict_eq_range j U hj)

/-- **The case `U = opensRange j`**, where the range hypothesis is `rfl`. This is the form the
chart data of `FormalSchemes.SpfHomFormalScheme` and the locality proof of
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.formalScheme` take. -/
def isoRestrictOpensRange : Y.restrict (opensRange j).isOpenEmbedding ≅ X :=
  isoRestrictOfRangeEq j (opensRange j) rfl

end OpensRange

end IsOpenImmersion

end AlgebraicGeometry.LocallyRingedSpace
