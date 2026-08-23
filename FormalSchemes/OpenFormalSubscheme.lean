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

/-- **The range of the inclusion is `U`.** The base map is the inclusion of the open subspace, so
this is `Opens.set_range_inclusion'` after the two spellings are identified. -/
@[simp]
theorem range_restrictOpenι_base :
    Set.range (X.restrictOpenι hX U).base = (U : Set X) := by
  have hbase : (X.restrictOpenι hX U).base = U.inclusion' := TopCat.hom_ext_iff.mpr rfl
  rw [restrictOpenι, show (X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding).base
    = U.inclusion' from hbase]
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

end AlgebraicGeometry.FormalScheme

end
