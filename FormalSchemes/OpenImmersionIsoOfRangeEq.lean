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

## Implementation notes

`range_coprodDesc_base` duplicates `AlgebraicGeometry.range_coprodDesc_base` in
`FormalSchemes.TateSelfProductBothOverlap`, which states the same general locally-ringed-space
fact in the middle of the Tate self-product tower. The copy here is deliberate: this file is meant
to be importable by anything, whereas that one drags in the whole completed-tensor interchange
tower. **The one in `TateSelfProductBothOverlap` is the duplicate to delete** once that file can
be edited again (it is inside `FormalSchemes.TateSelfProductDSigmaInv`'s import closure, which
currently cannot be rebuilt); it is on issue 617's consolidation list.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X Y Z : LocallyRingedSpace.{u}}

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

end IsOpenImmersion

end AlgebraicGeometry.LocallyRingedSpace
