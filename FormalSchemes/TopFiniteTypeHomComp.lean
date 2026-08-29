import FormalSchemes.RelativeTopFiniteTypeTrans
import FormalSchemes.TopFiniteTypeHom

set_option linter.style.header false

/-!
# Composition of finite-type morphisms at a non-affine target, over a shared chart

`AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom` (`FormalSchemes.TopFiniteTypeHom`) is EGA I,
10.13's finite-type condition for a morphism `f : X ⟶ Y` of formal schemes at an arbitrary target.
Its composition law — that `f ≫ g` is again topologically of finite type — is the half of the
category-theoretic sanity check that file left open. This file proves the composition law **for a
tower whose middle charts are shared**, and records precisely what separates that from the
unconditional statement.

## What is proved

`AlgebraicGeometry.FormalScheme.IsTfTypeTower` packages the data a composite needs: for each chart
of `𝒰` a chart of `𝒱` and a chart of `𝒲`, two tf-type algebras `A` over `(B, M)` and `B` over
`(S, K)`, and **one** identification `𝒱.obj i ≅ Spf M` of the middle chart, used by the
factorisation of `f` and by that of `g` alike.
`AlgebraicGeometry.FormalScheme.IsTfTypeTower.isTopFiniteTypeHomOn` composes it, and the proof is
the tower identity `AlgebraicGeometry.IsTopologicallyFiniteType.structHom_trans`
(`FormalSchemes.RelativeTopFiniteTypeTrans`) together with one `CategoryTheory.Iso.inv_hom_id`:
the middle identification cancels against itself, which is exactly what a shared chart buys.

`AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHomOn.chartMap_comp` is the first consumer: **the
restriction of a topologically finite-type morphism to a chart of its witnessing source cover is
again topologically of finite type**. There the shared middle chart is available for free — `g`'s
own identification of that chart is used on both sides, and the `f`-side algebra is
`AlgebraicGeometry.IsTopologicallyFiniteType.self`.

## What is *not* proved, and why it is not a bookkeeping gap

The unconditional law — `IsTopFiniteTypeHom f → IsTopFiniteTypeHom g → IsTopFiniteTypeHom (f ≫ g)`
— does **not** follow from this file by refining covers, and the obstruction is no longer the
geometric one that `FormalSchemes.TopFiniteTypeHom`'s module docstring recorded when it landed.
Both geometric ingredients now exist:

* `FormalSpectrum.exists_basicOpenChart_inter_iso` (`FormalSchemes.TwoChartBasicOpen`) refines two
  affine charts of `Y` to a common basic open and returns an **isomorphism of the two refined
  charts commuting with their inclusions into `Y`**;
* `AlgebraicGeometry.IsTopologicallyFiniteType.awayCompletion_baseChange`
  (`FormalSchemes.AwayBaseChangeTopFiniteType`) re-reads an `X`-chart tf-type over `(R, I)` as
  tf-type over the shrunk base `(R{1/c}^, I{1/c}^)`.

What they hand back is an isomorphism of *formal schemes* `Spf (I{1/c}^) ≅ Spf (M{1/d}^)`. What
`IsTopFiniteTypeHomOn` consumes is a tower of *algebras*: its factorisation is through
`AlgebraicGeometry.IsTopologicallyFiniteType.structHom`, which is `Spf` applied to an `algebraMap`.
Turning the first into the second needs the isomorphism to be `Spf` of a ring isomorphism carrying
one ideal of definition **onto** the other, and that is a genuine mathematical statement, not a
transport:

* `Spf` is full only onto the *continuous* morphisms (`AdicRingCat.spfHomEquiv`,
  `FormalSchemes.SpfFullyFaithful`), and the containment it demands is the strict
  `R.ideal ≤ S.ideal.comap _`;
* that containment is **not** an isomorphism invariant. Two ideals of definition that induce the
  same topology on a ring — `L` and `L ^ 2`, say — present the same formal spectrum, so an
  isomorphism `Spf J₁ ≅ Spf J₂` determines `J₁` and `J₂` only up to equivalence of the topologies
  they define, never on the nose;
* and two affine charts of one formal scheme, arriving as they do from two independent witnesses,
  are related on their overlap by exactly that much and no more.

So the remaining ingredient is the invariance of `IsTopologicallyFiniteType` under replacing the
base ideal by an equivalent one, plus the recovery of a ring isomorphism from an isomorphism of
formal spectra up to that equivalence. Neither is on this tree. Until they are, the composition law
is available in the shared-chart form below, and `IsTfTypeTower` is the interface a future
unconditional proof should produce.

The other blocker recorded in `FormalSchemes.TopFiniteTypeHom` — **conservativity**, that at
`Y = Spf I` the general notion implies the base-affine one — is untouched here.

## Main definitions and results

* `AlgebraicGeometry.FormalScheme.IsTfTypeTower`: the shared-chart tower datum for `f`, `g` and
  three covers.
* `AlgebraicGeometry.FormalScheme.IsTfTypeTower.isTopFiniteTypeHomOn` and
  `AlgebraicGeometry.FormalScheme.IsTfTypeTower.isTopFiniteTypeHom`: **the composition law** it
  supports.
* `AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHomOn.chartMap_comp`: restriction of a finite-type
  morphism to a chart of its witnessing source cover.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
-/

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FormalScheme

variable {X Y Z : FormalScheme.{u}}

/-! ### The shared-chart tower -/

/-- The data a composite `X ⟶ Y ⟶ Z` needs in order to be read chart by chart: for every chart of
`𝒰` a chart `i` of `𝒱` and a chart `k` of `𝒲`, a tower of tf-type algebras `A` over `(B, M)` over
`(S, K)`, and identifications of the three charts with `Spf L`, `Spf M`, `Spf K` making both
`f` and `g` structural.

The point of the definition is the quantifier placement: the middle identification
`eY : 𝒱.obj i ≅ Spf M` is bound **once** and used in both equations. `IsTopFiniteTypeHomOn f 𝒱 𝒰`
and `IsTopFiniteTypeHomOn g 𝒲 𝒱` each bind their own identification of a chart of `𝒱`
existentially, and nothing identifies the two; supplying them as one datum is precisely the
hypothesis this file's composition law adds, and the module docstring says why it cannot be
manufactured. -/
def IsTfTypeTower (f : X ⟶ Y) (g : Y ⟶ Z) (𝒲 : OpenCover Z) (𝒱 : OpenCover Y)
    (𝒰 : OpenCover X) : Prop :=
  ∀ j : 𝒰.J, ∃ (i : 𝒱.J) (k : 𝒲.J)
    (S : Type u) (_ : CommRing S) (_ : TopologicalSpace S) (K : Ideal S) (_ : IsAdicRing K)
    (_ : K.FG)
    (B : Type u) (_ : CommRing B) (_ : TopologicalSpace B) (_ : Algebra S B)
    (M : Ideal B) (_ : IsAdicRing M)
    (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : Algebra B A)
    (L : Ideal A) (_ : IsAdicRing L)
    (hg : IsTopologicallyFiniteType S K B M) (hf : IsTopologicallyFiniteType B M A L)
    (eX : 𝒰.obj j ≅ FormalScheme.Spf L) (eY : 𝒱.obj i ≅ FormalScheme.Spf M)
    (eZ : 𝒲.obj k ≅ FormalScheme.Spf K),
    𝒰.map j ≫ f = eX.hom ≫ IsTopologicallyFiniteType.structHom hf ≫ eY.inv ≫ 𝒱.map i ∧
      𝒱.map i ≫ g = eY.hom ≫ IsTopologicallyFiniteType.structHom hg ≫ eZ.inv ≫ 𝒲.map k

/-- **EGA I 10.13's composition law over a shared middle chart.** A tower whose middle
identification is shared between the two factorisations composes: the cover of `X` witnessing `f`
witnesses `f ≫ g` against the cover of `Z` witnessing `g`, with the same identification of each
chart of `X` and the same chart of `Z`.

**The cover of `X` is not refined**, which is what makes the proof bookkeeping. Two steps do the
work: `CategoryTheory.Iso.inv_hom_id` cancels the shared middle identification `eY` — this is the
step that fails when `f` and `g` identify the middle chart with two different affines — and
`AlgebraicGeometry.IsTopologicallyFiniteType.structHom_trans`
(`FormalSchemes.RelativeTopFiniteTypeTrans`) replaces the composite of the two structural
morphisms by the structural morphism of `IsTopologicallyFiniteType.trans`.

The `Algebra S A` and `IsScalarTower S B A` that `IsTopologicallyFiniteType.trans` needs are
*constructed* from the composite ring map rather than inferred, as in
`AlgebraicGeometry.FormalScheme.IsRelativelyTopFiniteType.comp_structHom`: the conclusion's own
existential is what they are supplied to, so there is no instance to find. -/
theorem IsTfTypeTower.isTopFiniteTypeHomOn {f : X ⟶ Y} {g : Y ⟶ Z}
    {𝒲 : OpenCover Z} {𝒱 : OpenCover Y} {𝒰 : OpenCover X}
    (h : IsTfTypeTower f g 𝒲 𝒱 𝒰) : IsTopFiniteTypeHomOn (f ≫ g) 𝒲 𝒰 := by
  intro j
  obtain ⟨i, k, S, _, _, K, _, hK, B, _, _, _, M, _, A, _, _, _, L, _, hg, hf, eX, eY, eZ,
    hfc, hgc⟩ := h j
  letI : Algebra S A := ((algebraMap B A).comp (algebraMap S B)).toAlgebra
  haveI : IsScalarTower S B A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨k, S, inferInstance, inferInstance, K, inferInstance, hK, A, inferInstance,
    inferInstance, inferInstance, L, inferInstance, hg.trans hK hf, eX, eZ, ?_⟩
  rw [← Category.assoc, hfc, Category.assoc, Category.assoc, Category.assoc, hgc,
    ← Category.assoc eY.inv, eY.inv_hom_id, Category.id_comp,
    ← Category.assoc (IsTopologicallyFiniteType.structHom hf),
    IsTopologicallyFiniteType.structHom_trans hK hg hf]

/-- The predicate-level form of `AlgebraicGeometry.FormalScheme.IsTfTypeTower.isTopFiniteTypeHomOn`,
for a caller who wants only that the composite is topologically of finite type and not the covers
that witness it. -/
theorem IsTfTypeTower.isTopFiniteTypeHom {f : X ⟶ Y} {g : Y ⟶ Z}
    {𝒲 : OpenCover Z} {𝒱 : OpenCover Y} {𝒰 : OpenCover X}
    (h : IsTfTypeTower f g 𝒲 𝒱 𝒰) : IsTopFiniteTypeHom (f ≫ g) :=
  ⟨𝒲, 𝒰, h.isTopFiniteTypeHomOn⟩

/-! ### A first consumer: restriction to a chart of the source cover -/

/-- **The restriction of a finite-type morphism to a chart of its witnessing source cover is
again of finite type.** If `g : Y ⟶ Z` is topologically of finite type through covers `𝒲` of `Z`
and `𝒱` of `Y`, then for every `i` the composite `𝒱.obj i ⟶ Y ⟶ Z` is topologically of finite
type.

This is a genuine application of `AlgebraicGeometry.FormalScheme.IsTfTypeTower`, not a restatement
of it: the tower it builds has `𝒱.obj i` as its own source cover, `A := B` with the identity
finiteness datum `AlgebraicGeometry.IsTopologicallyFiniteType.self`, and — the point — takes for
its shared middle identification the very isomorphism `g`'s witness supplies, which is why no
identification of two affine charts is needed. The `f`-side equation collapses through
`AlgebraicGeometry.IsTopologicallyFiniteType.structHom_self`
(`FormalSchemes.TopFiniteTypeHom`), and the conclusion is a statement about a composite that the
affine-target theory cannot reach, since neither `Y` nor `Z` is assumed affine. -/
theorem IsTopFiniteTypeHomOn.chartMap_comp {g : Y ⟶ Z} {𝒲 : OpenCover Z} {𝒱 : OpenCover Y}
    (hg : IsTopFiniteTypeHomOn g 𝒲 𝒱) (i : 𝒱.J) : IsTopFiniteTypeHom (𝒱.map i ≫ g) := by
  refine IsTfTypeTower.isTopFiniteTypeHom (𝒲 := 𝒲) (𝒱 := 𝒱)
    (𝒰 := OpenCover.self (𝒱.obj i)) fun _ => ?_
  obtain ⟨k, S, _, _, K, _, hK, B, _, _, _, M, _, hB, eY, eZ, hgc⟩ := hg i
  refine ⟨i, k, S, inferInstance, inferInstance, K, inferInstance, hK, B, inferInstance,
    inferInstance, inferInstance, M, inferInstance, B, inferInstance, inferInstance,
    inferInstance, M, inferInstance, hB, IsTopologicallyFiniteType.self, eY, eY, eZ, ?_, hgc⟩
  · simp only [OpenCover.self, IsTopologicallyFiniteType.structHom_self, Category.id_comp,
      Iso.hom_inv_id_assoc]

/-- **An affine chart inclusion is topologically of finite type.** For a formal scheme covered by
affines with finitely generated ideals of definition, every chart `𝒰.obj i ⟶ X` of that cover is a
topologically finite-type morphism.

`AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHomOn.chartMap_comp` applied to
`AlgebraicGeometry.FormalScheme.isTopFiniteTypeHomOn_id` (`FormalSchemes.TopFiniteTypeHom`), whose
cover of the target is the given `𝒰` and is therefore
multi-chart as soon as `X` is not affine. This is an application of the composition law and not a
restatement of it: `X` is arbitrary, the conclusion mentions neither `𝟙 X` nor any tower, and it is
not closed by `rfl` — an open immersion is not the structural morphism of anything until a cover
and a tf-type witness are produced for it. -/
theorem isTopFiniteTypeHom_chartMap (𝒰 : OpenCover X)
    (h𝒰 : ∀ j, ∃ (R : Type u) (_ : CommRing R) (_ : TopologicalSpace R) (I : Ideal R)
      (_ : IsAdicRing I) (_ : I.FG), Nonempty (𝒰.obj j ≅ FormalScheme.Spf I))
    (i : 𝒰.J) : IsTopFiniteTypeHom (𝒰.map i) := by
  have h := IsTopFiniteTypeHomOn.chartMap_comp (isTopFiniteTypeHomOn_id 𝒰 h𝒰) i
  rwa [Category.comp_id] at h

end AlgebraicGeometry.FormalScheme
