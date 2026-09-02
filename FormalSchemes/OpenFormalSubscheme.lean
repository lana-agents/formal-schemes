import FormalSchemes.OpenImmersionIsoOfRangeEq
import FormalSchemes.OpenImmersionSourceFormalScheme

set_option linter.style.header false

/-!
# The open formal subscheme cut out by an open subset

`FormalSchemes.OpenImmersionSourceFormalScheme` (issue 447) shows that the *source* of an open
immersion into a `LocallyFG` formal scheme is a formal scheme. This file records the consequence
the tree has been missing: the open subset itself, as an object.

For `X : FormalScheme` with `X.LocallyFG` and `U : Opens X`, the locally ringed space
`X.restrict U.isOpenEmbedding` is the source of the canonical open immersion `X.ofRestrict`, so it
is a formal scheme — `X.restrictOpen hX U` — and the inclusion `X.restrictOpen hX U ⟶ X` is an open
immersion with range exactly `U`. Nothing here is deep; the point is that the object did not exist,
and without it every statement about an open piece of a formal scheme had to name a presentation of
that piece instead.

## The comparison, which is what consumers actually want

A construction alone is not usable. What a caller has is some formal scheme `Y` and an open
immersion `j : Y ⟶ X` whose range is `U` — for instance a glued cover mapping into its ambient
affine — and what it wants is `Y ≅ X.restrictOpen hX U` *over* `X`. That is `restrictOpenIso`,
built from `LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq`, together with the triangle
`restrictOpenIso_hom_comp` identifying it with `j`. The triangle is the load-bearing half: it is
what lets a property of `Y` stated relative to a structural morphism through `X` transport to
`X.restrictOpen hX U` with the *same* morphism, rather than to an isomorphic copy with an opaque
one.

`restrictOpenSchemeIso` is the same isomorphism in `FormalScheme`, lifted along the fully faithful
forgetful functor.

## Functoriality

`restrictOpenMap` is the morphism `X|_{f⁻¹V} ⟶ Y|_V` induced by `f : X ⟶ Y`, together with the
square over `Y` that characterises it. Its base map is `Set.restrictPreimage` and its stalk maps
are those of `f` up to isomorphism, which is what makes it usable as the *restriction of `f` over
a chart* in a target-local argument: both halves of a condition like
`FormalScheme.IsClosedImmersion` can be read off from `f` itself.

## The `LocallyFG` hypothesis is not cosmetic

`ofOpenImmersion` needs it: `IsAdicRing I` does not force `I` to be finitely generated, and the
affine charts of a general formal scheme need not shrink (`FormalSchemes.LocallyFG`). So
`restrictOpen` carries `hX : X.LocallyFG` as an argument. It is a `Prop`, so the resulting object
does not depend on which proof is supplied, and `restrictOpen_locallyFG` says the hypothesis
propagates — an open piece of a `LocallyFG` formal scheme is again `LocallyFG`, so the construction
iterates.

## Main definitions and results

* `AlgebraicGeometry.FormalScheme.restrictOpen`: the open formal subscheme cut out by `U`.
* `AlgebraicGeometry.FormalScheme.restrictOpenι` / `restrictOpenHom`: the inclusion, as a morphism
  of locally ringed spaces and as a morphism of formal schemes.
* `AlgebraicGeometry.FormalScheme.range_restrictOpenι_base`: its range is `U`.
* `AlgebraicGeometry.FormalScheme.restrictOpenIso`, `restrictOpenIso_hom_comp`,
  `restrictOpenSchemeIso`: the comparison with any open immersion of range `U`, and the triangle
  over `X`.
* `AlgebraicGeometry.FormalScheme.restrictOpenTopIso` and `restrictOpenTopIso_hom`: the open
  subscheme cut out by `⊤` is `X`, and the comparison **is** the inclusion — so
  `restrictOpenHom hX ⊤` is an isomorphism (`isIso_restrictOpenHom_top`).
* `AlgebraicGeometry.FormalScheme.restrictOpenCongr` and `restrictOpenCongrTop_hom`: transport
  along an equality of opens, and its packaged composite with the `⊤` case.
* `AlgebraicGeometry.FormalScheme.restrictOpenMap` / `restrictOpenSchemeMap`: **functoriality** —
  the morphism `X|_{f⁻¹V} ⟶ Y|_V` induced by `f : X ⟶ Y`, with the square `restrictOpenMap_comp_ι`
  that characterises it (`restrictOpenMap_uniq`) and the functor laws `restrictOpenMap_id` /
  `restrictOpenMap_comp`.
* `AlgebraicGeometry.FormalScheme.restrictOpenMap_base`: its base map is `Set.restrictPreimage`,
  which is the form every target-local argument in the tree is phrased in.
* `AlgebraicGeometry.FormalScheme.stalkMap_restrictOpenMap` and
  `surjective_stalkMap_restrictOpenMap_iff`: its stalk maps are those of `f` up to isomorphism, so
  surjectivity of stalk maps is unaffected by restricting to an open — in both directions.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4, §10.15.
-/

noncomputable section

open CategoryTheory TopologicalSpace Topology

universe u

namespace AlgebraicGeometry.FormalScheme

variable (X : FormalScheme.{u}) (hX : X.LocallyFG) (U : Opens X)

/-- **The open formal subscheme of `X` cut out by `U`.** Its underlying locally ringed space is
`X.restrict U.isOpenEmbedding`, definitionally; it is a formal scheme because it is the source of
the open immersion `X.ofRestrict U.isOpenEmbedding`. -/
def restrictOpen : FormalScheme.{u} :=
  ofOpenImmersion (X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding) hX

@[simp]
theorem restrictOpen_toLocallyRingedSpace :
    (X.restrictOpen hX U).toLocallyRingedSpace
      = X.toLocallyRingedSpace.restrict U.isOpenEmbedding :=
  rfl

/-- **An open piece of a `LocallyFG` formal scheme is `LocallyFG`**, so the construction iterates
and its output feeds `exists_affineChart_subset` again. -/
theorem restrictOpen_locallyFG : (X.restrictOpen hX U).LocallyFG :=
  ofOpenImmersion_locallyFG _ hX

/-- **The inclusion of the open formal subscheme**, as a morphism of locally ringed spaces. -/
def restrictOpenι : (X.restrictOpen hX U).toLocallyRingedSpace ⟶ X.toLocallyRingedSpace :=
  X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding

instance isOpenImmersion_restrictOpenι :
    LocallyRingedSpace.IsOpenImmersion (X.restrictOpenι hX U) :=
  inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
    (X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding))

/-- **The base map of the inclusion is the inclusion of the open subspace.** The underlying space
of `X.restrictOpen hX U` is `U` itself, definitionally, so this is `rfl` after `TopCat.hom_ext`.
It is what turns any topological question about `restrictOpen` into one about `U` as a subtype. -/
theorem restrictOpenι_base : (X.restrictOpenι hX U).base = U.inclusion' :=
  TopCat.hom_ext_iff.mpr rfl

/-- **The range of the inclusion is `U`.** The base map is the inclusion of the open subspace, so
this is `Opens.set_range_inclusion'` after the two spellings are identified. -/
@[simp]
theorem range_restrictOpenι_base :
    Set.range (X.restrictOpenι hX U).base = (U : Set X) := by
  rw [restrictOpenι_base]
  exact Opens.set_range_inclusion' U

/-- **The inclusion, in the category of formal schemes.** -/
def restrictOpenHom : X.restrictOpen hX U ⟶ X :=
  Hom.mk (X.restrictOpenι hX U)

@[simp]
theorem restrictOpenHom_toLRSHom :
    (X.restrictOpenHom hX U).toLRSHom = X.restrictOpenι hX U :=
  rfl

/-! ### Comparison with an arbitrary open immersion of range `U` -/

variable {W : LocallyRingedSpace.{u}}

/-- **Any open immersion into `X` with range `U` identifies its source with `X.restrictOpen hX U`.**
Two open immersions of locally ringed spaces with the same range have isomorphic sources
(`LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq`), and the inclusion has range `U`. -/
def restrictOpenIso (j : W ⟶ X.toLocallyRingedSpace) [LocallyRingedSpace.IsOpenImmersion j]
    (hj : Set.range j.base = (U : Set X)) :
    W ≅ (X.restrictOpen hX U).toLocallyRingedSpace :=
  LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq j (X.restrictOpenι hX U)
    (by rw [hj, range_restrictOpenι_base])

/-- **The comparison is an isomorphism over `X`.** This is the half that makes `restrictOpenIso`
usable: a property of `W` stated relative to a morphism factoring through `j` transports to
`X.restrictOpen hX U` relative to the *same* morphism factored through the inclusion. -/
@[reassoc (attr := simp)]
theorem restrictOpenIso_hom_comp (j : W ⟶ X.toLocallyRingedSpace)
    [LocallyRingedSpace.IsOpenImmersion j] (hj : Set.range j.base = (U : Set X)) :
    (X.restrictOpenIso hX U j hj).hom ≫ X.restrictOpenι hX U = j :=
  LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- **The comparison is an isomorphism over `X`, other direction.** -/
@[reassoc (attr := simp)]
theorem restrictOpenIso_inv_comp (j : W ⟶ X.toLocallyRingedSpace)
    [LocallyRingedSpace.IsOpenImmersion j] (hj : Set.range j.base = (U : Set X)) :
    (X.restrictOpenIso hX U j hj).inv ≫ j = X.restrictOpenι hX U :=
  LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

/-- **The comparison in `FormalScheme`**: `restrictOpenIso` lifted along the fully faithful
forgetful functor, for a source that is already known to be a formal scheme. -/
def restrictOpenSchemeIso (Y : FormalScheme.{u})
    (j : Y.toLocallyRingedSpace ⟶ X.toLocallyRingedSpace)
    [LocallyRingedSpace.IsOpenImmersion j] (hj : Set.range j.base = (U : Set X)) :
    Y ≅ X.restrictOpen hX U :=
  -- The `show` pins `restrictOpenIso`'s implicit source: `preimageIso`'s expected type leaves it a
  -- metavariable, and the open-immersion instance for `j` is then not found.
  (Functor.FullyFaithful.ofFullyFaithful forgetToLocallyRingedSpace).preimageIso
    (show Y.toLocallyRingedSpace ≅ (X.restrictOpen hX U).toLocallyRingedSpace from
      X.restrictOpenIso hX U j hj)

section

variable (Y : FormalScheme.{u}) (j : Y.toLocallyRingedSpace ⟶ X.toLocallyRingedSpace)
variable [LocallyRingedSpace.IsOpenImmersion j] (hj : Set.range j.base = (U : Set X))

@[simp]
theorem restrictOpenSchemeIso_hom_toLRSHom :
    (X.restrictOpenSchemeIso hX U Y j hj).hom.toLRSHom = (X.restrictOpenIso hX U j hj).hom :=
  (Functor.FullyFaithful.ofFullyFaithful forgetToLocallyRingedSpace).map_preimage _

@[simp]
theorem restrictOpenSchemeIso_inv_toLRSHom :
    (X.restrictOpenSchemeIso hX U Y j hj).inv.toLRSHom = (X.restrictOpenIso hX U j hj).inv :=
  (Functor.FullyFaithful.ofFullyFaithful forgetToLocallyRingedSpace).map_preimage _

/-- **The `FormalScheme`-level triangle over `X`**: the comparison composed with the inclusion is
the given open immersion. -/
@[reassoc (attr := simp)]
theorem restrictOpenSchemeIso_hom_comp :
    (X.restrictOpenSchemeIso hX U Y j hj).hom ≫ X.restrictOpenHom hX U = Hom.mk j :=
  forgetToLocallyRingedSpace.map_injective (by
    change (X.restrictOpenSchemeIso hX U Y j hj).hom.toLRSHom ≫
      (X.restrictOpenHom hX U).toLRSHom = j
    rw [restrictOpenSchemeIso_hom_toLRSHom, restrictOpenHom_toLRSHom, restrictOpenIso_hom_comp])

/-- **The `FormalScheme`-level triangle over `X`, other direction**: this is the form the transports
consume, since a property of `Y` is moved to `X.restrictOpen hX U` along the *inverse*. -/
@[reassoc (attr := simp)]
theorem restrictOpenSchemeIso_inv_comp :
    (X.restrictOpenSchemeIso hX U Y j hj).inv ≫ Hom.mk j = X.restrictOpenHom hX U :=
  forgetToLocallyRingedSpace.map_injective (by
    change (X.restrictOpenSchemeIso hX U Y j hj).inv.toLRSHom ≫ j = X.restrictOpenι hX U
    rw [restrictOpenSchemeIso_inv_toLRSHom, restrictOpenIso_inv_comp])

end

/-! ### The degenerate open: `U = ⊤`

`restrictOpen` at `U = ⊤` is `X` again. Mathlib supplies the underlying isomorphism as
`LocallyRingedSpace.restrictTopIso`, which this tree already uses at `FormalSchemes.FormalScheme`
to exhibit `Spf I` as a formal scheme; what is added here is its lift to `FormalScheme` and — the
half that makes it usable — the identification of that lift with the inclusion itself.

That identification is stronger than a bare isomorphism and is what the consumers want: it says
`restrictOpenHom hX ⊤` **is** an isomorphism, so a statement proved about `X.restrictOpen hX ⊤`
relative to the inclusion transports to `X` relative to the identity, with no opaque comparison
morphism left in the way. It holds because `LocallyRingedSpace.restrictTopIso` is *defined* with
`hom := X.ofRestrict _`, which is `restrictOpenι` on the nose. -/

/-- **The open formal subscheme cut out by `⊤` is `X` itself.** `LocallyRingedSpace.restrictTopIso`
lifted along the fully faithful forgetful functor; the `show` pins the source, whose spelling
`restrictOpen_toLocallyRingedSpace` makes `rfl`-equal to Mathlib's. -/
def restrictOpenTopIso : X.restrictOpen hX ⊤ ≅ X :=
  (Functor.FullyFaithful.ofFullyFaithful forgetToLocallyRingedSpace).preimageIso
    (show (X.restrictOpen hX ⊤).toLocallyRingedSpace ≅ X.toLocallyRingedSpace from
      X.toLocallyRingedSpace.restrictTopIso)

/-- **The comparison at `⊤` is the inclusion.** This is the load-bearing half: without it the
isomorphism says nothing about what it does over `X`. Mathlib's `restrictTopIso` has
`hom := ofRestrict _` definitionally, so this is `map_preimage` and nothing else. -/
@[simp]
theorem restrictOpenTopIso_hom : (X.restrictOpenTopIso hX).hom = X.restrictOpenHom hX ⊤ :=
  forgetToLocallyRingedSpace.map_injective
    ((Functor.FullyFaithful.ofFullyFaithful forgetToLocallyRingedSpace).map_preimage _)

/-- **The inclusion of `⊤` is an isomorphism**, which is the form instance search wants. -/
instance isIso_restrictOpenHom_top : IsIso (X.restrictOpenHom hX ⊤) :=
  X.restrictOpenTopIso_hom hX ▸ (X.restrictOpenTopIso hX).isIso_hom

/-! ### Transport along an equality of opens

`restrictOpen` takes the open as an argument, so an equality of opens gives an equality of objects
and `eqToIso` suffices. It is recorded here with its triangle because the pair
`restrictOpenCongr … ≪≫ restrictOpenTopIso` is what a consumer holding a *covering* hypothesis
`U = ⊤` in some other spelling actually needs, and assembling it at each call site costs a `subst`
in a context where `restrictOpen`'s argument is buried. -/

/-- **Equal opens cut out equal open formal subschemes.** -/
def restrictOpenCongr {U U' : Opens X} (h : U = U') :
    X.restrictOpen hX U ≅ X.restrictOpen hX U' :=
  eqToIso (congrArg _ h)

/-- The transport commutes with the two inclusions. -/
@[reassoc (attr := simp)]
theorem restrictOpenCongr_hom_comp {U U' : Opens X} (h : U = U') :
    (X.restrictOpenCongr hX h).hom ≫ X.restrictOpenHom hX U' = X.restrictOpenHom hX U := by
  subst h
  simp [restrictOpenCongr]

/-- **An open equal to `⊤` cuts out `X`, and the resulting comparison is the inclusion.** This is
the packaged form: a consumer with `hU : U = ⊤` gets `X.restrictOpen hX U ≅ X` together with the
statement that it is `restrictOpenHom hX U`, which is what transports a property stated over the
inclusion. -/
theorem restrictOpenCongrTop_hom {U : Opens X} (h : U = ⊤) :
    (X.restrictOpenCongr hX h ≪≫ X.restrictOpenTopIso hX).hom = X.restrictOpenHom hX U := by
  rw [Iso.trans_hom, restrictOpenTopIso_hom, restrictOpenCongr_hom_comp]

/-! ### Functoriality: the induced morphism on open subschemes

Given `f : X ⟶ Y` and `V : Opens Y`, the inclusion of `f⁻¹V` composed with `f` lands inside `V`,
so the universal property of the open immersion `restrictOpenι hY V` lifts it to a morphism

```
X.restrictOpen hX (f⁻¹V) ⟶ Y.restrictOpen hY V
```

between the open subschemes. That is `restrictOpenMap`, and — as everywhere on this chain — the
statement that makes it usable is not its existence but the **commuting square**
`restrictOpenMap_comp_ι`, which says what it does over `Y`. `restrictOpenMap_uniq` says the square
determines it, which is how a hand-built map is recognised as this one.

The preimage is written `(Opens.map f.base).obj V` throughout, with no abbreviation: a `def`
wrapping it would not unfold at `instances` transparency and would put a wall between the two
spellings of the same open, which is the failure mode this file's `restrictOpenCongrTop_hom` exists
to work around.

`restrictOpenMap_base` is the topological payoff: the base map **is** `Set.restrictPreimage`, since
the underlying space of `restrictOpen` is the open subset itself. Every target-local argument in
the tree is phrased through `Set.restrictPreimage`, so this is the bridge to them.
-/

section Map

variable (Y : FormalScheme.{u}) (hY : Y.LocallyFG)
variable (f : X.toLocallyRingedSpace ⟶ Y.toLocallyRingedSpace) (V : Opens Y)

/-- **The inclusion of `f⁻¹V`, followed by `f`, lands in `V`.** This is the hypothesis of
`LocallyRingedSpace.IsOpenImmersion.lift`; both ranges are pinned by `range_restrictOpenι_base`,
after which it is `Set.image_preimage_subset`. -/
theorem range_restrictOpenι_comp_le :
    Set.range (X.restrictOpenι hX ((Opens.map f.base).obj V) ≫ f).base
      ⊆ Set.range (Y.restrictOpenι hY V).base := by
  rw [range_restrictOpenι_base]
  have h : ⇑(X.restrictOpenι hX ((Opens.map f.base).obj V) ≫ f).base
      = ⇑f.base ∘ ⇑(X.restrictOpenι hX ((Opens.map f.base).obj V)).base := rfl
  rw [h, Set.range_comp, range_restrictOpenι_base, Opens.map_coe]
  exact Set.image_preimage_subset _ _

/-- **The morphism induced by `f` on open subschemes**, `X|_{f⁻¹V} ⟶ Y|_V`. It is the lift of
`restrictOpenι ≫ f` through the open immersion `restrictOpenι hY V`, which applies exactly because
the composite lands in `V`. -/
def restrictOpenMap :
    (X.restrictOpen hX ((Opens.map f.base).obj V)).toLocallyRingedSpace ⟶
      (Y.restrictOpen hY V).toLocallyRingedSpace :=
  LocallyRingedSpace.IsOpenImmersion.lift (Y.restrictOpenι hY V)
    (X.restrictOpenι hX ((Opens.map f.base).obj V) ≫ f)
    (X.range_restrictOpenι_comp_le hX Y hY f V)

/-- **The square over `Y`**, which is the load-bearing half: the induced morphism followed by the
inclusion of `V` is the inclusion of `f⁻¹V` followed by `f`. -/
@[reassoc (attr := simp)]
theorem restrictOpenMap_comp_ι :
    X.restrictOpenMap hX Y hY f V ≫ Y.restrictOpenι hY V
      = X.restrictOpenι hX ((Opens.map f.base).obj V) ≫ f :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _

/-- **The square determines the morphism.** This is what lets a consumer recognise a map it built
by hand as `restrictOpenMap`, and it is the engine of the functor laws below. -/
theorem restrictOpenMap_uniq
    (l : (X.restrictOpen hX ((Opens.map f.base).obj V)).toLocallyRingedSpace ⟶
      (Y.restrictOpen hY V).toLocallyRingedSpace)
    (hl : l ≫ Y.restrictOpenι hY V = X.restrictOpenι hX ((Opens.map f.base).obj V) ≫ f) :
    l = X.restrictOpenMap hX Y hY f V :=
  LocallyRingedSpace.IsOpenImmersion.lift_uniq _ _ _ l hl

/-- **The square, read at a point of the base.** -/
theorem base_restrictOpenMap_comp_ι
    (x : (X.restrictOpen hX ((Opens.map f.base).obj V)).toLocallyRingedSpace) :
    (Y.restrictOpenι hY V).base ((X.restrictOpenMap hX Y hY f V).base x)
      = f.base ((X.restrictOpenι hX ((Opens.map f.base).obj V)).base x) := by
  have h := congrArg (fun m : (X.restrictOpen hX ((Opens.map f.base).obj V)).toLocallyRingedSpace ⟶
    Y.toLocallyRingedSpace => ⇑m.base) (X.restrictOpenMap_comp_ι hX Y hY f V)
  simpa only [LocallyRingedSpace.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp,
    Function.comp_apply] using congrFun h x

/-- **The base map is `Set.restrictPreimage`.** The underlying space of `X.restrictOpen hX U` is
`U` as a subtype and the inclusion's base map is `U.inclusion'` (`restrictOpenι_base`), so the
square says precisely that the base map of `restrictOpenMap` sends `x ∈ f⁻¹V` to `f x ∈ V`.

This is the bridge to every target-local argument already in the tree: `ClosedImmersion` and the
`GeneralSeparated*` layer phrase their per-chart hypotheses through `Set.restrictPreimage` applied
to a `.base`, and this says the induced morphism's base map *is* that. -/
theorem restrictOpenMap_base :
    ⇑(X.restrictOpenMap hX Y hY f V).base = Set.restrictPreimage (V : Set Y) ⇑f.base := by
  funext x
  refine Subtype.val_injective ?_
  have h := X.base_restrictOpenMap_comp_ι hX Y hY f V x
  rwa [restrictOpenι_base, restrictOpenι_base] at h

/-- **The range of the induced morphism**, in the form `LocallyRingedSpace.IsOpenImmersion.lift`
supplies it. -/
theorem range_restrictOpenMap_base :
    Set.range (X.restrictOpenMap hX Y hY f V).base
      = (Y.restrictOpenι hY V).base ⁻¹'
        Set.range (X.restrictOpenι hX ((Opens.map f.base).obj V) ≫ f).base :=
  LocallyRingedSpace.IsOpenImmersion.lift_range _ _ _

/-! #### The stalk maps

The stalk maps of `restrictOpenMap` are those of `f`, up to isomorphism. No germ-level argument is
needed for this, which the issue that asked for it expected to be the expensive step: both
inclusions are open immersions, so *their* stalk maps are isomorphisms
(`LocallyRingedSpace.IsOpenImmersion.stalk_iso`), and applying `stalkMap_comp` to both sides of
the square leaves the identification with two isomorphisms on the outside.

The one wrinkle is that the square is an equality of *morphisms*, so `stalkMap_congr_hom` inserts a
`stalkSpecializes` between the two spellings of the image point. That is an isomorphism too, by
`TopCat.Presheaf.stalkCongr` at the `Inseparable` coming from `base_restrictOpenMap_comp_ι` — so it
does not obstruct anything, it just has to be named. -/

/-- **The stalk map of the induced morphism, in terms of `f`.** The two inclusions are open
immersions, so their stalk maps are isomorphisms and this exhibits
`(restrictOpenMap f V).stalkMap x` as `f.stalkMap` conjugated by them. -/
theorem stalkMap_restrictOpenMap
    (x : (X.restrictOpen hX ((Opens.map f.base).obj V)).toLocallyRingedSpace) :
    (X.restrictOpenMap hX Y hY f V).stalkMap x
      = inv ((Y.restrictOpenι hY V).stalkMap ((X.restrictOpenMap hX Y hY f V).base x))
        ≫ Y.presheaf.stalkSpecializes
            (specializes_of_eq (X.base_restrictOpenMap_comp_ι hX Y hY f V x).symm)
        ≫ f.stalkMap ((X.restrictOpenι hX ((Opens.map f.base).obj V)).base x)
        ≫ (X.restrictOpenι hX ((Opens.map f.base).obj V)).stalkMap x := by
  rw [IsIso.eq_inv_comp]
  have h := LocallyRingedSpace.stalkMap_congr_hom _ _ (X.restrictOpenMap_comp_ι hX Y hY f V) x
  rw [LocallyRingedSpace.stalkMap_comp, LocallyRingedSpace.stalkMap_comp] at h
  exact h

/-- **Surjectivity of stalk maps is unaffected by restricting to an open.** This is the corollary
that matters: surjective stalk maps is exactly what `FormalScheme.IsClosedImmersion` asks for, and
because the comparison of `stalkMap_restrictOpenMap` is by isomorphisms on both sides it transports
in *both* directions. -/
theorem surjective_stalkMap_restrictOpenMap_iff
    (x : (X.restrictOpen hX ((Opens.map f.base).obj V)).toLocallyRingedSpace) :
    Function.Surjective ⇑((X.restrictOpenMap hX Y hY f V).stalkMap x).hom ↔
      Function.Surjective
        ⇑(f.stalkMap ((X.restrictOpenι hX ((Opens.map f.base).obj V)).base x)).hom := by
  haveI : IsIso (Y.presheaf.stalkSpecializes
      (specializes_of_eq (X.base_restrictOpenMap_comp_ι hX Y hY f V x).symm)) :=
    (TopCat.Presheaf.stalkCongr Y.presheaf
      (Inseparable.of_eq (X.base_restrictOpenMap_comp_ι hX Y hY f V x))).isIso_hom
  rw [stalkMap_restrictOpenMap]
  have hi := ConcreteCategory.bijective_of_isIso
    ((X.restrictOpenι hX ((Opens.map f.base).obj V)).stalkMap x)
  have hs := ConcreteCategory.bijective_of_isIso (Y.presheaf.stalkSpecializes
    (specializes_of_eq (X.base_restrictOpenMap_comp_ι hX Y hY f V x).symm))
  have hv := ConcreteCategory.bijective_of_isIso
    (inv ((Y.restrictOpenι hY V).stalkMap ((X.restrictOpenMap hX Y hY f V).base x)))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_assoc]
  rw [Function.Surjective.of_comp_iff' hi, Function.Surjective.of_comp_iff _
    (hs.surjective.comp hv.surjective)]

/-- **The morphism induced on open subschemes, in `FormalScheme`.** `FormalScheme` is a full
subcategory of locally ringed spaces, so this is `FormalScheme.Hom.mk`; it exists because
`FormalScheme.IsClosedImmersion` and the rest of the target-local vocabulary are stated for
`FormalScheme.Hom`, not for the underlying morphism. -/
def restrictOpenSchemeMap (g : X ⟶ Y) (V : Opens Y) :
    X.restrictOpen hX ((Opens.map g.toLRSHom.base).obj V) ⟶ Y.restrictOpen hY V :=
  Hom.mk (X.restrictOpenMap hX Y hY g.toLRSHom V)

@[simp]
theorem restrictOpenSchemeMap_toLRSHom (g : X ⟶ Y) (V : Opens Y) :
    (X.restrictOpenSchemeMap hX Y hY g V).toLRSHom = X.restrictOpenMap hX Y hY g.toLRSHom V :=
  rfl

/-- **The square over `Y`, in `FormalScheme`.** -/
@[reassoc (attr := simp)]
theorem restrictOpenSchemeMap_comp_hom (g : X ⟶ Y) (V : Opens Y) :
    X.restrictOpenSchemeMap hX Y hY g V ≫ Y.restrictOpenHom hY V
      = X.restrictOpenHom hX ((Opens.map g.toLRSHom.base).obj V) ≫ g :=
  forgetToLocallyRingedSpace.map_injective (X.restrictOpenMap_comp_ι hX Y hY g.toLRSHom V)

end Map

/-! ### The functor laws

Both are `restrictOpenMap_uniq`. The only friction is that `(Opens.map (𝟙 _)).obj V` and
`(Opens.map (f ≫ g)).obj W` are *definitionally* but not syntactically the opens one wants, so
the source objects of the two sides are spelled differently. For the composition law the two
spellings unify cheaply and the statement can be written directly; for the identity law they do
not — asking `isDefEq` to compare `X.restrictOpen hX ((Opens.map (𝟙 _)).obj V)` with
`X.restrictOpen hX V` while also inserting an identity morphism exhausts the heartbeat budget.
So the identity law is stated through `restrictOpenCongr`, which names the transport instead of
leaving it to unification, and then everything is fast. -/

/-- `(Opens.map (𝟙 X).base).obj V = V`, at the spelling `restrictOpenMap` produces it.

Mathlib's `Opens.map_id_obj` is the same fact, but stated at `𝟙 (X : TopCat)`. Using *that* one
here makes the identity law below **time out**: the unifier has to identify
`(𝟙 X.toLocallyRingedSpace).base` with `𝟙 ?T` and solve for `?T` through the
`LocallyRingedSpace → SheafedSpace → PresheafedSpace → TopCat` tower. Stated at the spelling in
hand it is `rfl` and costs nothing. -/
theorem opensMap_id_base_obj (V : Opens X) :
    (Opens.map (𝟙 X.toLocallyRingedSpace : X.toLocallyRingedSpace ⟶ _).base).obj V = V :=
  rfl

/-- The identity morphism of a formal scheme induces the transport along `opensMap_id_base_obj`,
which is the identity up to that renaming of the open. Stated through `restrictOpenCongr`
deliberately: see the note above. -/
theorem restrictOpenMap_id (V : Opens X) :
    X.restrictOpenMap hX X hX (𝟙 X.toLocallyRingedSpace : X.toLocallyRingedSpace ⟶ _) V
      = (X.restrictOpenCongr hX (X.opensMap_id_base_obj V)).hom.toLRSHom :=
  (X.restrictOpenMap_uniq hX X hX _ V _
    (show (X.restrictOpenCongr hX (X.opensMap_id_base_obj V)).hom.toLRSHom ≫ X.restrictOpenι hX V
        = X.restrictOpenι hX ((Opens.map
            (𝟙 X.toLocallyRingedSpace : X.toLocallyRingedSpace ⟶ _).base).obj V)
          ≫ 𝟙 X.toLocallyRingedSpace from by
      rw [Category.comp_id]
      exact congrArg Hom.toLRSHom
        (X.restrictOpenCongr_hom_comp hX (X.opensMap_id_base_obj V)))).symm

/-- **Composition.** Taking the open subscheme over `W` and then over `g⁻¹W` is the same as taking
it over `(f ≫ g)⁻¹W` in one step. -/
theorem restrictOpenMap_comp {Y Z : FormalScheme.{u}} (hY : Y.LocallyFG) (hZ : Z.LocallyFG)
    (f : X.toLocallyRingedSpace ⟶ Y.toLocallyRingedSpace)
    (g : Y.toLocallyRingedSpace ⟶ Z.toLocallyRingedSpace) (W : Opens Z) :
    X.restrictOpenMap hX Z hZ (f ≫ g) W
      = X.restrictOpenMap hX Y hY f ((Opens.map g.base).obj W)
        ≫ Y.restrictOpenMap hY Z hZ g W :=
  (X.restrictOpenMap_uniq hX Z hZ (f ≫ g) W _
    (show (X.restrictOpenMap hX Y hY f ((Opens.map g.base).obj W)
            ≫ Y.restrictOpenMap hY Z hZ g W) ≫ Z.restrictOpenι hZ W
        = X.restrictOpenι hX ((Opens.map f.base).obj ((Opens.map g.base).obj W)) ≫ f ≫ g from by
      rw [Category.assoc, restrictOpenMap_comp_ι, ← Category.assoc, restrictOpenMap_comp_ι,
        Category.assoc])).symm

end AlgebraicGeometry.FormalScheme

end
