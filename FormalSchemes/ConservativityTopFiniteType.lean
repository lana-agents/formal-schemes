import FormalSchemes.AdicCofinalOpenImmersion
import FormalSchemes.RelativeTopFiniteTypeTrans
import FormalSchemes.TopFiniteTypeHomTrans

set_option linter.style.header false

/-!
# Conservativity for topologically-finite-type morphisms

`AlgebraicGeometry.FormalScheme.IsRelativelyTopFiniteType R I f` is the base-affine notion and
`AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom f` the general-target one
(`FormalSchemes.RelativeTopFiniteType`, `FormalSchemes.TopFiniteTypeHom`). One direction is
`AlgebraicGeometry.FormalScheme.IsRelativelyTopFiniteType.isTopFiniteTypeHom`. **Conservativity**
is the converse at `Y = FormalScheme.Spf I`, and this file is its assembly: the passage from
"every chart of the target cover is adic up to cofinality" to "the two notions agree".

The algebra was already there —
`AlgebraicGeometry.IsTopologicallyFiniteType.of_openImmersion_of_isCofinal`
(`FormalSchemes.AffineOpenTopFiniteType`) makes the ring of a target chart tf-type over `(R, I)`,
`IsTopologicallyFiniteType.trans` (`FormalSchemes.TopFiniteTypeTrans`) stacks the chart algebra on
top of it, and `IsTopologicallyFiniteType.ofCofinal` (`FormalSchemes.CofinalTopFiniteType`) aligns
the two base ideals. What was missing is **geometric**, and is the first result below.

## The geometric step

A witness for `IsTopFiniteTypeHom f` hands one, per chart of `X`, a factorisation
`𝒰.map j ≫ f = e.hom ≫ structHom h ≫ e'.inv ≫ 𝒱.map i` in which the last two arrows are an
*abstract* open immersion `t : Spf K ⟶ Spf I` of the target chart. `IsRelativelyTopFiniteType`
asks instead for a *structural* morphism `Spf L' ⟶ Spf I`. So `t` itself has to be recognised as
one, and that is `FormalSpectrum.structMap_eq_generalCofinalSpfIso_comp`: **an arbitrary morphism
of formal spectra is the structural morphism of the ideal it extends**, up to
`FormalSpectrum.generalCofinalSpfIso`.

Its proof is the Spf–Γ round trip `FormalSpectrum.locallyRingedSpaceMap_globalSectionsMap`
(`FormalSchemes.SpfGammaRoundTrip`), and the reason it has to be stated at the *extended* ideal
`I · B` rather than at `J` is exactly the reason issue 460's on-the-nose adicity is false: the
round trip needs continuity, `I ≤ J.comap φ`, i.e. `I · B ≤ J`, and `FormalSchemes.AdicOnSections`
refutes that. At `I · B` the containment is `Ideal.map_le_iff_le_comap` and costs nothing. The
whole hypothesis of this file is spent on one other thing — that `I · B` is again an *ideal of
definition*, `IsAdicRing (I · B)`, which `IsAdicRing.of_isCofinal`
(`FormalSchemes.CofinalAdicRing`) extracts from the cofinality.

## The hypothesis, and what is *not* proved here

`AlgebraicGeometry.FormalScheme.IsAdicOpenImmersionProperty I` is issue 1218's goal 2 verbatim:
every affine open immersion into `Spf I` is adic up to cofinality. **This file does not settle
it**, and it does not weaken any of the four finite-type predicates in order to avoid it. After
`FormalSpectrum.isCofinal_map_of_le_radical` (`FormalSchemes.AdicCofinalOpenImmersion`) the
property is the single containment `J ≤ √(I · B)`, and
`FormalSpectrum.isCofinal_map_of_range_eq_basicOpenChart` discharges it when the open is basic —
which is what makes the unconditional cases below unconditional.

## Where the residue now sits — and why this file's hypothesis is redundant

`IsRelativelyTopFiniteType` asserts the *existence* of a cover, so a witness may be refined before
it is used, and `IsTopFiniteTypeHomOn.isRelativelyTopFiniteType` below needs the adicity hypothesis
only at the charts of the *target* cover `𝒱` — where
`IsTopFiniteTypeHomOn.isRelativelyTopFiniteType_of_basicOpen` makes it free as soon as their ranges
are basic. So conservativity does not need the property at an arbitrary affine open: it is enough
to refine a given witness `IsTopFiniteTypeHomOn f 𝒱 𝒰` to one whose target cover is by basic opens
of `Spf I`.

**That refinement is now on the tree**, as
`AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom.exists_basicTargetRefinement`
(`FormalSchemes.TargetBasicRefinement`), and with it
`AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom.isRelativelyTopFiniteType_of_fg` proves
conservativity with **no hypothesis beyond `I.FG`**. Every theorem below that carries
`IsAdicOpenImmersionProperty I` therefore has a redundant hypothesis, and a caller should use the
unconditional form. They are kept because they record where the hypothesis is spent — at the charts
of `𝒱`, and nowhere else — which is the observation the refinement was built on.

The refinement does not go through `AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom.exists_refinement`
(`FormalSchemes.TopFiniteTypeHom`), which refines the cover of `X` *keeping `𝒱` fixed*: it shrinks
each target chart against the identity of `Spf I` with
`FormalSpectrum.exists_basicOpenChart_le_affine_inter` (`FormalSchemes.TwoChartBasicOpen`) and
carries the source chart along by `FormalSpectrum.map_preimage_basicOpen` and
`AlgebraicGeometry.IsTopologicallyFiniteType.awayCompletion_baseChange`
(`FormalSchemes.AwayBaseChangeTopFiniteType`).

`IsAdicOpenImmersionProperty I` itself — issue 1218's goal 2, EGA I 10.12 — is **not** settled by
any of this and remains open.

## Main definitions

* `AlgebraicGeometry.FormalScheme.IsAdicAffineOpen`: the adicity hypothesis at one open subset of
  `Spf I`, stated for an arbitrary presentation of it — the form
  `FormalSpectrum.isCofinal_map_of_range_eq` says is the invariant one.
* `AlgebraicGeometry.FormalScheme.IsAdicOpenImmersionProperty`: the same at every affine open.

## Main results

* `FormalSpectrum.structMap_eq_generalCofinalSpfIso_comp`: **the geometric step**, above.
* `AlgebraicGeometry.FormalScheme.isAdicAffineOpen_range_basicOpenChart` and
  `AlgebraicGeometry.FormalScheme.IsAdicOpenImmersionProperty.isAdicAffineOpen`: the two ways the
  per-open hypothesis is supplied — free at a basic open, and by specialising the global one.
* `AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHomOn.isRelativelyTopFiniteType`:
  **conservativity at a fixed pair of covers**, with the hypothesis only at the charts of `𝒱`.
* `AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom.isRelativelyTopFiniteType` and
  `AlgebraicGeometry.FormalScheme.isRelativelyTopFiniteType_iff_isTopFiniteTypeHom`: EGA I 10.13's
  conservativity, and the resulting equivalence of the two notions, under the global hypothesis.
* `AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHomOn.isRelativelyTopFiniteType_of_basicOpen` and
  `AlgebraicGeometry.FormalScheme.isRelativelyTopFiniteType_of_isTopFiniteTypeHomOn_self`: **two
  unconditional cases** — a target cover whose charts have basic ranges, and the trivial target
  cover.
* `AlgebraicGeometry.FormalScheme.isRelativelyTopFiniteType_of_openImmersion_range_eq_basicOpen`
  and `AlgebraicGeometry.FormalScheme.isRelativelyTopFiniteType_basicOpenChart`: an open immersion
  of formal spectra with basic range is relatively tf-type **as the morphism it is**, not merely
  through its ring. This is the application of the geometric step.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.12, §10.13.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.3.
-/

noncomputable section

open CategoryTheory

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] {I : Ideal R} [IsAdicRing I]
variable {B : Type u} [CommRing B] [TopologicalSpace B] {J : Ideal B} [IsAdicRing J]
variable [Algebra R B]

/-- **An arbitrary morphism of formal spectra is a structural morphism.** For any
`m : Spf J ⟶ Spf I` with `algebraMap R B` the induced map on global sections, `m` agrees with the
structural morphism `Spf (I · B) ⟶ Spf I` of the extended ideal, after the comparison
`FormalSpectrum.generalCofinalSpfIso` has moved the source from `Spf (I · B)` to `Spf J`.

No open immersion, no finite generation of `J` beyond what the comparison needs, and no
completeness hypothesis on `B`: the only input is `IsAdicRing (I · B)`, which is an instance
argument here and which a caller obtains from `IsAdicRing.of_isCofinal`
(`FormalSchemes.CofinalAdicRing`) — that is the single place the adicity hypothesis of this file
is spent.

The proof is `FormalSpectrum.locallyRingedSpaceMap_globalSectionsMap`
(`FormalSchemes.SpfGammaRoundTrip`) applied to `generalCofinalSpfIso … ≫ m`, whose global-sections
map is `algebraMap R B` because the comparison is the identity there
(`FormalSpectrum.globalSectionsMap_generalCofinalSpfIso_hom`). The round trip's continuity
hypothesis `I ≤ (I · B).comap (algebraMap R B)` is `Ideal.map_le_iff_le_comap`; stating the same
identity at `J` instead would need `I · B ≤ J`, which `FormalSchemes.AdicOnSections` refutes. -/
theorem structMap_eq_generalCofinalSpfIso_comp (hI : I.FG) (hJ : J.FG)
    (m : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    (halg : algebraMap R B = globalSectionsMap I J m)
    [IsAdicRing (I.map (algebraMap R B))] (hK : (I.map (algebraMap R B)).FG) :
    IsTopologicallyFiniteType.structMap
        (rfl : I.map (algebraMap R B) = I.map (algebraMap R B)) =
      (generalCofinalSpfIso (I.map (algebraMap R B)) J hK hJ).hom ≫ m := by
  set K := I.map (algebraMap R B) with hKdef
  have hg : globalSectionsMap I K ((generalCofinalSpfIso K J hK hJ).hom ≫ m) =
      algebraMap R B := by
    rw [globalSectionsMap_comp, globalSectionsMap_generalCofinalSpfIso_hom, ← halg,
      RingHom.id_comp]
  have hcont : I ≤ K.comap (algebraMap R B) := Ideal.map_le_iff_le_comap.mp le_rfl
  have hround := locallyRingedSpaceMap_globalSectionsMap I K hI hK
    ((generalCofinalSpfIso K J hK hJ).hom ≫ m) (by rw [hg]; exact hcont)
  rw [← hround]
  exact locallyRingedSpaceMap_congr I K _ _ _ _ hg.symm

end FormalSpectrum

namespace AlgebraicGeometry.FormalScheme

variable {R : Type u} [CommRing R] [TopologicalSpace R] {I : Ideal R} [IsAdicRing I]

variable (I) in
/-- **The adicity hypothesis at one open subset `U` of `Spf I`**: every presentation of `U` by an
affine open immersion `m : Spf J ⟶ Spf I` with `J` finitely generated has `J` cofinal with the
extension of `I` along `m`'s global-sections map.

Quantifying over *all* presentations rather than fixing one is not a strengthening:
`FormalSpectrum.isCofinal_map_of_range_eq` (`FormalSchemes.AdicCofinalOpenImmersion`) says the
conclusion depends only on the open subset, so any one presentation gives all of them. It is
stated this way because a caller arrives with the presentation the witness happened to produce. -/
def IsAdicAffineOpen (U : Set (FormalSpectrum I)) : Prop :=
  ∀ (B : Type u) [CommRing B] [TopologicalSpace B] (J : Ideal B) [IsAdicRing J], J.FG →
    ∀ m : FormalSpectrum.locallyRingedSpaceObj J ⟶ FormalSpectrum.locallyRingedSpaceObj I,
      LocallyRingedSpace.IsOpenImmersion m → Set.range m.base = U →
      Ideal.IsCofinal J (I.map (FormalSpectrum.globalSectionsMap I J m))

/-- **A basic open satisfies the hypothesis, unconditionally.** This is
`FormalSpectrum.isCofinal_map_of_range_eq_basicOpenChart` (`FormalSchemes.AdicCofinalOpenImmersion`)
repackaged: the algebra structure on `B` that lemma takes as data is here the one induced by `m`,
so nothing is assumed about it. -/
theorem isAdicAffineOpen_range_basicOpenChart (hI : I.FG) (g : R) :
    IsAdicAffineOpen I (Set.range (FormalSpectrum.basicOpenChart I g).base) := by
  intro B _ _ J _ hJ m hm hrange
  letI : Algebra R B := (FormalSpectrum.globalSectionsMap I J m).toAlgebra
  have halg : algebraMap R B = FormalSpectrum.globalSectionsMap I J m :=
    RingHom.algebraMap_toAlgebra _
  rw [← halg]
  exact FormalSpectrum.isCofinal_map_of_range_eq_basicOpenChart I J hI hJ m halg g hrange

/-- **Conservativity, at a fixed pair of covers.** If `f : X ⟶ Spf R` is topologically of finite
type as witnessed by `𝒱` and `𝒰`, and every chart of the *target* cover `𝒱` satisfies the adicity
hypothesis, then `f` is topologically of finite type over `(R, I)` in the base-affine sense — with
the very cover `𝒰`, unrefined.

Per chart `j` of `𝒰` the witness supplies a base `(S, K)`, an algebra `A` tf-type over it, and a
factorisation through the target chart `t = e'.inv ≫ 𝒱.map i`. The proof runs four steps:

* `AlgebraicGeometry.IsTopologicallyFiniteType.of_openImmersion_of_isCofinal`
  (`FormalSchemes.AffineOpenTopFiniteType`) makes `S` tf-type over `(R, I)`, with ideal `I · S`;
* `IsTopologicallyFiniteType.ofCofinal` (`FormalSchemes.CofinalTopFiniteType`) moves `A` from the
  base ideal `K` to the cofinal `I · S`, replacing `L` by `(I · S) · A`;
* `IsTopologicallyFiniteType.trans` (`FormalSchemes.TopFiniteTypeTrans`) composes the two;
* the compatibility square is `IsTopologicallyFiniteType.structMap_comp`
  (`FormalSchemes.RelativeTopFiniteTypeTrans`) for the tower,
  `FormalSpectrum.structMap_eq_generalCofinalSpfIso_comp` to recognise `t` as a structural
  morphism, and `FormalSpectrum.structMap_comp_generalCofinalSpfIso_inv`
  (`FormalSchemes.CofinalStructMap`) to move the ideal comparison past the two structural
  morphisms. The identification of `𝒰.obj j` is the given one composed with that comparison. -/
theorem IsTopFiniteTypeHomOn.isRelativelyTopFiniteType {X : FormalScheme.{u}}
    {f : X ⟶ FormalScheme.Spf I} (hI : I.FG) {𝒱 : OpenCover (FormalScheme.Spf I)}
    {𝒰 : OpenCover X} (hOn : IsTopFiniteTypeHomOn f 𝒱 𝒰)
    (hadic : ∀ i : 𝒱.J, IsAdicAffineOpen I (Set.range (𝒱.map i).toLRSHom.base)) :
    IsRelativelyTopFiniteType R I f := by
  refine ⟨𝒰, fun j => ?_⟩
  obtain ⟨i, S, _, _, K, _, hKfg, A, _, _, _, L, _, hA, e, e', hcomp⟩ := hOn j
  -- The chart of the target, presented by `(S, K)`.
  set t : FormalScheme.Spf K ⟶ FormalScheme.Spf I := e'.inv ≫ 𝒱.map i with ht
  haveI : IsIso e'.inv.toLRSHom :=
    inferInstanceAs (IsIso (forgetToLocallyRingedSpace.map e'.inv))
  haveI hti : LocallyRingedSpace.IsOpenImmersion t.toLRSHom :=
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
      (e'.inv.toLRSHom ≫ (𝒱.map i).toLRSHom))
  haveI hti' : @LocallyRingedSpace.IsOpenImmersion (FormalSpectrum.locallyRingedSpaceObj K)
      (FormalSpectrum.locallyRingedSpaceObj I) t.toLRSHom := hti
  have hrange : Set.range t.toLRSHom.base = Set.range (𝒱.map i).toLRSHom.base := by
    refine Set.Subset.antisymm ?_ fun u hu => ?_
    · rintro u ⟨v, rfl⟩
      exact ⟨e'.inv.toLRSHom.base v, rfl⟩
    · exact mem_range_iso_comp e'.symm (𝒱.map i) hu
  have hcof : Ideal.IsCofinal K (I.map (FormalSpectrum.globalSectionsMap I K t.toLRSHom)) :=
    hadic i S K hKfg t.toLRSHom hti hrange
  -- The base ring of the chart becomes an `R`-algebra, tf-type over `(R, I)`.
  letI : Algebra R S := (FormalSpectrum.globalSectionsMap I K t.toLRSHom).toAlgebra
  have halg : algebraMap R S = FormalSpectrum.globalSectionsMap I K t.toLRSHom :=
    RingHom.algebraMap_toAlgebra _
  set K' : Ideal S := I.map (algebraMap R S) with hK'
  have hcof' : Ideal.IsCofinal K K' := by rw [hK', halg]; exact hcof
  haveI : IsAdicRing K' := IsAdicRing.of_isCofinal hcof'
  have hK'fg : K'.FG := hI.map _
  have hS : IsTopologicallyFiniteType R I S K' :=
    IsTopologicallyFiniteType.of_openImmersion_of_isCofinal hI hKfg t.toLRSHom halg hcof'
  -- The chart algebra, realigned to the base ideal `K'`.
  have hLfg : L.FG := by rw [← hA.map_eq]; exact hKfg.map _
  set L' : Ideal A := K'.map (algebraMap S A) with hL'
  have hA' : IsTopologicallyFiniteType S K' A L' := hA.ofCofinal hcof'
  haveI : IsAdicRing L' := IsAdicRing.of_isCofinal (hA.isCofinal_map hcof')
  have hL'fg : L'.FG := hK'fg.map _
  letI : Algebra R A := ((algebraMap S A).comp (algebraMap R S)).toAlgebra
  haveI : IsScalarTower R S A :=
    IsScalarTower.of_algebraMap_eq' (RingHom.algebraMap_toAlgebra _)
  have hAtot : IsTopologicallyFiniteType R I A L' := hS.trans hI hA'
  refine ⟨A, inferInstance, inferInstance, inferInstance, L', inferInstance, hAtot,
    e ≪≫ (spfIsoOfLRS (FormalSpectrum.generalCofinalSpfIso L' L hL'fg hLfg)).symm, ?_⟩
  rw [hcomp, Iso.trans_hom, Category.assoc]
  congr 1
  apply Hom.ext'
  rw [comp_toLRSHom, comp_toLRSHom]
  change IsTopologicallyFiniteType.structMap hA.map_eq ≫ t.toLRSHom =
    (FormalSpectrum.generalCofinalSpfIso L' L hL'fg hLfg).inv ≫
      IsTopologicallyFiniteType.structMap hAtot.map_eq
  have h₁ : Ideal.map (algebraMap R S) I = K' := rfl
  have h₂ : Ideal.map (algebraMap S A) K' = L' := rfl
  have hstep1 : IsTopologicallyFiniteType.structMap h₂ ≫ IsTopologicallyFiniteType.structMap h₁ =
      IsTopologicallyFiniteType.structMap hAtot.map_eq :=
    IsTopologicallyFiniteType.structMap_comp h₁ h₂ hAtot.map_eq
  have hstep2 : IsTopologicallyFiniteType.structMap h₁ =
      (FormalSpectrum.generalCofinalSpfIso K' K hK'fg hKfg).hom ≫ t.toLRSHom :=
    FormalSpectrum.structMap_eq_generalCofinalSpfIso_comp hI hKfg t.toLRSHom halg hK'fg
  have hstep3 := FormalSpectrum.structMap_comp_generalCofinalSpfIso_inv (I := K') (J := K)
    (L := L') (M := L) hK'fg hKfg h₂ hA.map_eq hL'fg hLfg
  calc IsTopologicallyFiniteType.structMap hA.map_eq ≫ t.toLRSHom
      = (IsTopologicallyFiniteType.structMap hA.map_eq ≫
          (FormalSpectrum.generalCofinalSpfIso K' K hK'fg hKfg).inv) ≫
          ((FormalSpectrum.generalCofinalSpfIso K' K hK'fg hKfg).hom ≫ t.toLRSHom) := by
        rw [Category.assoc, ← Category.assoc
          (FormalSpectrum.generalCofinalSpfIso K' K hK'fg hKfg).inv, Iso.inv_hom_id,
          Category.id_comp]
    _ = ((FormalSpectrum.generalCofinalSpfIso L' L hL'fg hLfg).inv ≫
          IsTopologicallyFiniteType.structMap h₂) ≫ IsTopologicallyFiniteType.structMap h₁ := by
        rw [hstep3, ← hstep2]
        rfl
    _ = (FormalSpectrum.generalCofinalSpfIso L' L hL'fg hLfg).inv ≫
          IsTopologicallyFiniteType.structMap hAtot.map_eq := by
        rw [Category.assoc, hstep1]

variable (I) in
/-- **The adicity hypothesis at every affine open of `Spf I`.** This is the statement that an
affine open immersion of formal spectra is adic up to cofinality — the residue that
`FormalSpectrum.isCofinal_map_of_le_radical` (`FormalSchemes.AdicCofinalOpenImmersion`) reduces to
the single containment `J ≤ √(I · B)`, and that
`FormalSpectrum.isCofinal_map_of_range_eq_basicOpenChart` settles when the open is basic.

It is a hypothesis, not a theorem: its on-the-nose form `I · B ≤ J` is **false**
(`FormalSchemes.AdicOnSections`), and the cofinality form is open on this tree for an arbitrary
affine open. -/
def IsAdicOpenImmersionProperty : Prop :=
  ∀ (B : Type u) [CommRing B] [TopologicalSpace B] (J : Ideal B) [IsAdicRing J], J.FG →
    ∀ m : FormalSpectrum.locallyRingedSpaceObj J ⟶ FormalSpectrum.locallyRingedSpaceObj I,
      LocallyRingedSpace.IsOpenImmersion m →
      Ideal.IsCofinal J (I.map (FormalSpectrum.globalSectionsMap I J m))

/-- The global hypothesis gives the hypothesis at every open, by forgetting the range condition. -/
theorem IsAdicOpenImmersionProperty.isAdicAffineOpen (h : IsAdicOpenImmersionProperty I)
    (U : Set (FormalSpectrum I)) : IsAdicAffineOpen I U :=
  fun B _ _ J _ hJ m hm _ => h B J hJ m hm

/-- **Conservativity** (EGA I, 10.13): at an affine target, a topologically-finite-type morphism is
topologically of finite type over the base, given `IsAdicOpenImmersionProperty I`.

The converse is `IsRelativelyTopFiniteType.isTopFiniteTypeHom` (`FormalSchemes.TopFiniteTypeHom`)
and needs no hypothesis.

**The hypothesis here is redundant.**
`AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom.isRelativelyTopFiniteType_of_fg`
(`FormalSchemes.TargetBasicRefinement`) has the same conclusion from `I.FG` alone; prefer it. -/
theorem IsTopFiniteTypeHom.isRelativelyTopFiniteType {X : FormalScheme.{u}}
    {f : X ⟶ FormalScheme.Spf I} (hI : I.FG) (hadic : IsAdicOpenImmersionProperty I)
    (h : IsTopFiniteTypeHom f) : IsRelativelyTopFiniteType R I f := by
  obtain ⟨𝒱, 𝒰, hOn⟩ := h
  exact hOn.isRelativelyTopFiniteType hI fun i => hadic.isAdicAffineOpen _

/-- **The two notions of topological finite type agree at an affine target**, given
`IsAdicOpenImmersionProperty I`. The forward direction is unconditional. -/
theorem isRelativelyTopFiniteType_iff_isTopFiniteTypeHom {X : FormalScheme.{u}}
    (hI : I.FG) (hadic : IsAdicOpenImmersionProperty I) (f : X ⟶ FormalScheme.Spf I) :
    IsRelativelyTopFiniteType R I f ↔ IsTopFiniteTypeHom f :=
  ⟨fun h => h.isTopFiniteTypeHom hI, fun h => h.isRelativelyTopFiniteType hI hadic⟩

/-- **An unconditional case: a target cover whose charts have basic ranges.** No hypothesis beyond
`I.FG`, because `isAdicAffineOpen_range_basicOpenChart` discharges the adicity at each chart.

The condition is on the *ranges* only, so the charts of `𝒱` need not be presented by
`FormalSpectrum.basicOpenChart`; any presentation of a basic open will do, which is what
`FormalSpectrum.isCofinal_map_of_range_eq` buys. -/
theorem IsTopFiniteTypeHomOn.isRelativelyTopFiniteType_of_basicOpen {X : FormalScheme.{u}}
    {f : X ⟶ FormalScheme.Spf I} (hI : I.FG) {𝒱 : OpenCover (FormalScheme.Spf I)}
    {𝒰 : OpenCover X} (hOn : IsTopFiniteTypeHomOn f 𝒱 𝒰)
    (hbasic : ∀ i : 𝒱.J, ∃ g : R, Set.range (𝒱.map i).toLRSHom.base =
      Set.range (FormalSpectrum.basicOpenChart I g).base) :
    IsRelativelyTopFiniteType R I f := by
  refine hOn.isRelativelyTopFiniteType hI fun i => ?_
  obtain ⟨g, hg⟩ := hbasic i
  intro B _ _ J _ hJ m hm hr
  exact isAdicAffineOpen_range_basicOpenChart hI g B J hJ m hm (hr.trans hg)

/-- **An unconditional case: the trivial target cover.** A witness against the one-object
self-cover of `Spf R` gives the base-affine notion outright, since the range of the identity is
the range of the chart at `1` (`FormalSpectrum.basicOpen_one`).

This is the exact converse of `IsRelativelyTopFiniteType.isTopFiniteTypeHom`
(`FormalSchemes.TopFiniteTypeHom`), which produces a witness against precisely this cover. So the
two notions agree on the nose whenever the general one is witnessed without subdividing the
target, and all of conservativity's difficulty is in the target cover. -/
theorem isRelativelyTopFiniteType_of_isTopFiniteTypeHomOn_self {X : FormalScheme.{u}}
    {f : X ⟶ FormalScheme.Spf I} (hI : I.FG) {𝒰 : OpenCover X}
    (hOn : IsTopFiniteTypeHomOn f (OpenCover.self (FormalScheme.Spf I)) 𝒰) :
    IsRelativelyTopFiniteType R I f := by
  refine hOn.isRelativelyTopFiniteType_of_basicOpen hI fun i => ⟨1, ?_⟩
  rw [FormalSpectrum.range_basicOpenChart_base I 1 hI, FormalSpectrum.basicOpen_one]
  exact Set.range_eq_univ.mpr fun x => ⟨x, rfl⟩

/-- **An open immersion of formal spectra with basic range is relatively tf-type, as the morphism
it is.** Not merely: its ring is tf-type over `(R, I)`, which is
`AlgebraicGeometry.IsTopologicallyFiniteType.of_openImmersion_range_eq_basicOpen`
(`FormalSchemes.AdicCofinalOpenImmersion`) and says nothing about `m`. The content added here is
that `m` *itself* factors as the comparison isomorphism followed by a structural morphism, which
is `FormalSpectrum.structMap_eq_generalCofinalSpfIso_comp`.

That factorisation is not definitional — `m` is an arbitrary morphism of locally ringed spaces and
the right-hand side is built from `algebraMap R B` — so this is an application of the geometric
step rather than a restatement of it. -/
theorem isRelativelyTopFiniteType_of_openImmersion_range_eq_basicOpen
    {B : Type u} [CommRing B] [TopologicalSpace B] {J : Ideal B} [IsAdicRing J]
    (hI : I.FG) (hJ : J.FG)
    (m : FormalSpectrum.locallyRingedSpaceObj J ⟶ FormalSpectrum.locallyRingedSpaceObj I)
    [LocallyRingedSpace.IsOpenImmersion m] (g : R)
    (hrange : Set.range m.base = Set.range (FormalSpectrum.basicOpenChart I g).base) :
    IsRelativelyTopFiniteType R I
      (Hom.mk m : FormalScheme.Spf J ⟶ FormalScheme.Spf I) := by
  letI : Algebra R B := (FormalSpectrum.globalSectionsMap I J m).toAlgebra
  have halg : algebraMap R B = FormalSpectrum.globalSectionsMap I J m :=
    RingHom.algebraMap_toAlgebra _
  have hcof : Ideal.IsCofinal J (I.map (algebraMap R B)) :=
    FormalSpectrum.isCofinal_map_of_range_eq_basicOpenChart I J hI hJ m halg g hrange
  haveI : IsAdicRing (I.map (algebraMap R B)) := IsAdicRing.of_isCofinal hcof
  have hKfg : (I.map (algebraMap R B)).FG := hI.map _
  have hB : IsTopologicallyFiniteType R I B (I.map (algebraMap R B)) :=
    IsTopologicallyFiniteType.of_openImmersion_of_isCofinal hI hJ m halg hcof
  have hkey := FormalSpectrum.structMap_eq_generalCofinalSpfIso_comp hI hJ m halg hKfg
  refine ⟨OpenCover.self (FormalScheme.Spf J), fun _ =>
    ⟨B, inferInstance, inferInstance, inferInstance, I.map (algebraMap R B), inferInstance, hB,
      (spfIsoOfLRS (FormalSpectrum.generalCofinalSpfIso
        (I.map (algebraMap R B)) J hKfg hJ)).symm, ?_⟩⟩
  change 𝟙 (FormalScheme.Spf J) ≫ (Hom.mk m : FormalScheme.Spf J ⟶ FormalScheme.Spf I) = _
  rw [Category.id_comp]
  apply Hom.ext'
  change m = (FormalSpectrum.generalCofinalSpfIso (I.map (algebraMap R B)) J hKfg hJ).inv ≫
    IsTopologicallyFiniteType.structMap hB.map_eq
  calc m = (FormalSpectrum.generalCofinalSpfIso (I.map (algebraMap R B)) J hKfg hJ).inv ≫
        ((FormalSpectrum.generalCofinalSpfIso (I.map (algebraMap R B)) J hKfg hJ).hom ≫ m) := by
        rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    _ = (FormalSpectrum.generalCofinalSpfIso (I.map (algebraMap R B)) J hKfg hJ).inv ≫
        IsTopologicallyFiniteType.structMap hB.map_eq := by rw [← hkey]

/-- **The basic-open chart of `Spf R` is relatively topologically of finite type**, with no
hypothesis beyond `I.FG`. The concrete instance of the previous theorem: `basicOpenChart I g` is
an open immersion (`FormalSpectrum.isOpenImmersion_basicOpenChart`) whose range is its own, so the
range hypothesis is `rfl` and the adicity is free. -/
theorem isRelativelyTopFiniteType_basicOpenChart (hI : I.FG) (g : R) :
    haveI := FormalSpectrum.isAdicRing_awayCompletionIdeal I g hI
    IsRelativelyTopFiniteType R I
      (Hom.mk (FormalSpectrum.basicOpenChart I g) :
        FormalScheme.Spf (FormalSpectrum.awayCompletionIdeal I g) ⟶ FormalScheme.Spf I) := by
  haveI := FormalSpectrum.isAdicRing_awayCompletionIdeal I g hI
  haveI : LocallyRingedSpace.IsOpenImmersion (FormalSpectrum.basicOpenChart I g) :=
    FormalSpectrum.isOpenImmersion_basicOpenChart I g hI
  have hJ : (FormalSpectrum.awayCompletionIdeal I g).FG := by
    rw [← FormalSpectrum.map_awayCompletionHom I g]
    exact hI.map _
  exact isRelativelyTopFiniteType_of_openImmersion_range_eq_basicOpen hI hJ _ g rfl

end AlgebraicGeometry.FormalScheme
