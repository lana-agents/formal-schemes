import FormalSchemes.TateOverlapDisjoint
import FormalSchemes.Gluing

set_option linter.style.header false

/-!
# The Tate chain: the ℤ-indexed glue datum of the formal annulus chain

Fix an adic base `R` with finitely generated ideal of definition `I` and a **topologically
nilpotent** Tate parameter `q ∈ I`, and let `A = R{x, y} / (x·y − q)` be the coordinate ring of the
formal Tate annulus with ideal of definition `I·A`. The flagship goal of issue 208 is to glue the
`ℤ`-indexed chain of consecutive translates of `Spf A` into a single (non-affine) formal scheme
`T` — the formal model of the Tate curve before quotienting by the `q^ℤ`-action.

This file assembles that datum. The two-patch prototype (`FormalSchemes.TateGlueTwoPatch`) glued two
copies of `Spf A` along `{x invertible} ≅ {y invertible}`; here we carry that construction to the
full index type `ℤ` (lifted to the ambient universe as `ULift.{u} ℤ`). Patch `U_n = Spf A` overlaps
**only its two immediate neighbours**:

* with `U_{n+1}` along `V(n, n+1) = Spf A{1/x}` (the `{x invertible}` locus `D(x)`), and
* with `U_{n-1}` along `V(n, n-1) = Spf A{1/y}` (the `{y invertible}` locus `D(y)`);

for `|m − n| ≥ 2` the overlap `V(n, m)` is the **initial** (empty) locally ringed space `∅`, since
non-adjacent patches do not meet.

The transition `t_{n,n+1} : V(n, n+1) ≅ V(n+1, n)` is the geometric chart transition
`annulusChartTransitionSpf : Spf A{1/x} ≅ Spf A{1/y}` (`FormalSchemes.TateChartTransition`).

## Why the cocycle is automatic

Unlike the two-patch slice — where the triple-overlap fields `t'`, `t_fac`, `cocycle` were vacuous
because no triple of `Bool`-indices is pairwise distinct — here genuine pairwise-distinct triples
`(i, j, k)` exist. The point (issue 208's crux, `FormalSchemes.TateOverlapDisjoint`) is that the
**triple overlap of any patch with two distinct others is empty**:

* if one of the two others is non-adjacent to `i`, the corresponding leg `f i · ` has empty source;
* if both are adjacent (necessarily one on each side, `{i-1, i+1}`), the two legs are the `x`- and
  `y`-charts, whose ranges `D(x)`, `D(y)` are **disjoint** because `x · y = q ∈ I` vanishes in
  `A ⧸ (I·A)`.

Either way `pullback (f i j) (f i k)` has empty carrier, hence is **initial**, so the maps `t'`,
`t_fac`, `cocycle` out of it are forced by `IsInitial.hom_ext`. This is the geometric reason the
Tate chain glues with no genuine cocycle obstruction.

## Main definitions

* `AlgebraicGeometry.tateChainGlueData'`: the `CategoryTheory.GlueData' LocallyRingedSpace` of the
  ℤ-indexed annulus chain.
* `AlgebraicGeometry.tateChainLRSGlueData`: the induced `LocallyRingedSpace.GlueData`.
* `AlgebraicGeometry.tateChainFormalGlueData`: the `FormalScheme.GlueData`, each patch `Spf A`.
* `AlgebraicGeometry.tateChain`: the glued (non-affine) formal scheme `T`, the formal Tate chain.

## Remaining work (issue 208)

The glued structural morphism `T ⟶ Spf R` (assembling the per-patch `annulusStructMap` into a
morphism over the base, exhibiting the chain as a formal scheme over `Spf R`) remains open: the
in-repo gluing framework (`FormalSchemes.Gluing`) does not yet provide a morphism-gluing combinator
(`GlueData.glueMorphisms` / `Multicoequalizer.desc`). Part 3 (issue 135, the `q^ℤ`-shift action on
`T` and its proper discontinuity) also follows.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- The annulus object `Spf A`, the patches of the chain. -/
private abbrev tcU : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (annulusIdealOfDefinition R I q)

/-- The `x`-overlap `Spf A{1/x}` (the forward-gluing intersection `D(x)`). -/
private abbrev tcVx : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))

/-- The `y`-overlap `Spf A{1/y}` (the backward-gluing intersection `D(y)`). -/
private abbrev tcVy : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))

/-- The overlap object `V(i, j)` of the Tate chain: the `x`-chart domain for a forward step
`j = i + 1`, the `y`-chart domain for a backward step `j = i - 1`, and the empty locally ringed
space otherwise (non-adjacent patches do not meet). -/
def tateV (i j : ULift.{u} ℤ) : LocallyRingedSpace.{u} :=
  if j.down - i.down = 1 then tcVx R I q
  else if j.down - i.down = -1 then tcVy R I q
  else ∅

@[simp] theorem tateV_forward {i j : ULift.{u} ℤ} (h : j.down - i.down = 1) :
    tateV R I q i j = tcVx R I q := by simp [tateV, h]

@[simp] theorem tateV_backward {i j : ULift.{u} ℤ} (h : j.down - i.down = -1) :
    tateV R I q i j = tcVy R I q := by
  simp [tateV, h]

theorem tateV_far {i j : ULift.{u} ℤ} (h1 : j.down - i.down ≠ 1) (h2 : j.down - i.down ≠ -1) :
    tateV R I q i j = ∅ := by simp [tateV, h1, h2]

/-- The inclusion `f i j : V(i, j) ⟶ U i` of the Tate chain: the `x`-chart `Spf A{1/x} ⟶ Spf A`
forward, the `y`-chart `Spf A{1/y} ⟶ Spf A` backward, and the (empty-source) initial map otherwise.
-/
def tateF (i j : ULift.{u} ℤ) : tateV R I q i j ⟶ tcU R I q :=
  if h1 : j.down - i.down = 1 then
    eqToHom (tateV_forward R I q h1) ≫ annulusOverlapChart R I q
  else if h2 : j.down - i.down = -1 then
    eqToHom (tateV_backward R I q h2) ≫ annulusOverlapChartY R I q
  else
    eqToHom (tateV_far R I q h1 h2) ≫ LocallyRingedSpace.emptyTo _

theorem tateF_forward {i j : ULift.{u} ℤ} (h : j.down - i.down = 1) :
    tateF R I q i j = eqToHom (tateV_forward R I q h) ≫ annulusOverlapChart R I q := by
  simp only [tateF, dif_pos h]

theorem tateF_backward {i j : ULift.{u} ℤ} (h : j.down - i.down = -1) :
    tateF R I q i j = eqToHom (tateV_backward R I q h) ≫ annulusOverlapChartY R I q := by
  have h1 : j.down - i.down ≠ 1 := by omega
  simp only [tateF, dif_neg h1, dif_pos h]

theorem tateF_far {i j : ULift.{u} ℤ} (h1 : j.down - i.down ≠ 1) (h2 : j.down - i.down ≠ -1) :
    tateF R I q i j = eqToHom (tateV_far R I q h1 h2) ≫ LocallyRingedSpace.emptyTo _ := by
  simp only [tateF, dif_neg h1, dif_neg h2]

/-- **Every inclusion `f i j` of the Tate chain is an open immersion**: the charts are open
immersions (`isOpenImmersion_annulusOverlapChart(Y)`), the far maps have empty source
(`LocallyRingedSpace.isOpenImmersion_of_isEmpty`), and pre-composing with the isomorphism `eqToHom`
preserves the property. -/
theorem tateF_isOpenImmersion (hI : I.FG) (i j : ULift.{u} ℤ) :
    LocallyRingedSpace.IsOpenImmersion (tateF R I q i j) := by
  by_cases h1 : j.down - i.down = 1
  · rw [tateF_forward R I q h1]
    haveI := isOpenImmersion_annulusOverlapChart R I q hI
    infer_instance
  · by_cases h2 : j.down - i.down = -1
    · rw [tateF_backward R I q h2]
      haveI := isOpenImmersion_annulusOverlapChartY R I q hI
      infer_instance
    · rw [tateF_far R I q h1 h2]
      haveI : IsEmpty (tateV R I q i j) := (tateV_far R I q h1 h2) ▸ inferInstance
      infer_instance

/-- The transition `t i j : V(i, j) ⟶ V(j, i)` of the Tate chain: the geometric chart transition
`Spf A{1/x} ≅ Spf A{1/y}` forward (`.hom`) and backward (`.inv`), the empty map otherwise. -/
def tateT (hI : I.FG) (i j : ULift.{u} ℤ) : tateV R I q i j ⟶ tateV R I q j i :=
  if h1 : j.down - i.down = 1 then
    eqToHom (tateV_forward R I q h1) ≫ (annulusChartTransitionSpf R I q hI).hom ≫
      eqToHom (tateV_backward R I q (show i.down - j.down = -1 by omega)).symm
  else if h2 : j.down - i.down = -1 then
    eqToHom (tateV_backward R I q h2) ≫ (annulusChartTransitionSpf R I q hI).inv ≫
      eqToHom (tateV_forward R I q (show i.down - j.down = 1 by omega)).symm
  else
    eqToHom (tateV_far R I q h1 h2) ≫
      LocallyRingedSpace.emptyTo _ ≫
      eqToHom (tateV_far R I q (show i.down - j.down ≠ 1 by omega)
        (show i.down - j.down ≠ -1 by omega)).symm

/-- The range of `f i j` on underlying spaces is unchanged by the `eqToHom` pre-composition:
pre-composing with an isomorphism does not change the range. -/
private theorem range_eqToHom_comp {X Y Z : LocallyRingedSpace.{u}} (e : X = Y) (g : Y ⟶ Z) :
    Set.range (eqToHom e ≫ g).base = Set.range g.base := by
  subst e; simp

/-- The empty-source initial map has empty range. -/
private theorem range_emptyTo_empty (X : LocallyRingedSpace.{u}) :
    Set.range (LocallyRingedSpace.emptyTo X).base = ∅ := by
  rw [Set.range_eq_empty_iff]
  exact inferInstanceAs (IsEmpty (∅ : LocallyRingedSpace.{u}))

/-- **The legs of any pairwise-distinct triple overlap have disjoint ranges.** This is the geometric
crux (`FormalSchemes.TateOverlapDisjoint`): for distinct `j ≠ k`, at least one of `f i j`, `f i k`
either has empty source (non-adjacent patch) or the two are the `x`- and `y`-charts with disjoint
loci `D(x)`, `D(y)`. -/
private theorem tateF_range_disjoint (hq : q ∈ I) (hI : I.FG) {i j k : ULift.{u} ℤ}
    (hjk : j ≠ k) :
    Disjoint (Set.range (tateF R I q i j).base) (Set.range (tateF R I q i k).base) := by
  -- If either leg is a "far" (empty-source) map, its range is empty.
  by_cases h1j : j.down - i.down = 1
  · by_cases h1k : k.down - i.down = 1
    · exact absurd (ULift.down_injective (show j.down = k.down by omega)) hjk
    · by_cases h2k : k.down - i.down = -1
      · -- (i,j) = x-chart, (i,k) = y-chart: disjoint D(x), D(y).
        rw [tateF_forward R I q h1j, tateF_backward R I q h2k,
          range_eqToHom_comp, range_eqToHom_comp]
        exact annulusOverlapChart_range_disjoint R I q hq hI
      · rw [tateF_far R I q h1k h2k, range_eqToHom_comp, range_emptyTo_empty]
        exact Set.disjoint_right.mpr fun a ha => ha.elim
  · by_cases h2j : j.down - i.down = -1
    · by_cases h1k : k.down - i.down = 1
      · -- (i,j) = y-chart, (i,k) = x-chart: disjoint D(y), D(x).
        rw [tateF_backward R I q h2j, tateF_forward R I q h1k,
          range_eqToHom_comp, range_eqToHom_comp]
        exact (annulusOverlapChart_range_disjoint R I q hq hI).symm
      · by_cases h2k : k.down - i.down = -1
        · exact absurd (ULift.down_injective (show j.down = k.down by omega)) hjk
        · rw [tateF_far R I q h1k h2k, range_eqToHom_comp, range_emptyTo_empty]
          exact Set.disjoint_right.mpr fun a ha => ha.elim
    · rw [tateF_far R I q h1j h2j, range_eqToHom_comp, range_emptyTo_empty]
      exact Set.disjoint_left.mpr fun a ha => ha.elim

/-- **The triple overlap of any pairwise-distinct triple is empty.** The tool that degenerates the
Tate-chain cocycle: `pullback (f i j) (f i k)` has empty carrier, hence is initial. -/
private theorem isEmpty_tatePullback (hq : q ∈ I) (hI : I.FG) (i : ULift.{u} ℤ) {j k : ULift.{u} ℤ}
    (hjk : j ≠ k) [HasPullback (tateF R I q i j) (tateF R I q i k)] :
    IsEmpty (pullback (tateF R I q i j) (tateF R I q i k) : LocallyRingedSpace.{u}) :=
  LocallyRingedSpace.isEmpty_pullback _ _ (tateF_range_disjoint R I q hq hI hjk)

/-- **The ℤ-indexed glue datum of the Tate annulus chain**, as a `CategoryTheory.GlueData'` on the
index type `ULift ℤ`. Consecutive patches `Spf A` are glued along `{x invertible} ≅ {y invertible}`;
non-consecutive overlaps are empty, so the triple-overlap fields `t'`, `t_fac`, `cocycle` are forced
by initiality. -/
def tateChainGlueData' (hq : q ∈ I) (hI : I.FG) :
    CategoryTheory.GlueData' LocallyRingedSpace.{u} where
  J := ULift.{u} ℤ
  U := fun _ => tcU R I q
  V := fun i j _ => tateV R I q i j
  f := fun i j _ => tateF R I q i j
  f_mono := fun i j _ => by haveI := tateF_isOpenImmersion R I q hI i j; infer_instance
  f_hasPullback := fun i j k _ _ =>
    haveI := tateF_isOpenImmersion R I q hI i j
    inferInstance
  t := fun i j _ => tateT R I q hI i j
  t' := fun i j k _ _ hjk => by
    haveI := tateF_isOpenImmersion R I q hI i j
    haveI := isEmpty_tatePullback R I q hq hI i hjk
    exact (LocallyRingedSpace.isInitialOfIsEmpty).to _
  t_fac := fun i j k _ _ hjk => by
    haveI := tateF_isOpenImmersion R I q hI i j
    haveI := isEmpty_tatePullback R I q hq hI i hjk
    exact (LocallyRingedSpace.isInitialOfIsEmpty).hom_ext _ _
  t_inv := fun i j hij => by
    by_cases h1 : j.down - i.down = 1
    · have h2j : i.down - j.down = -1 := by omega
      rw [tateT, dif_pos h1, tateT, dif_neg (show i.down - j.down ≠ 1 by omega), dif_pos h2j]
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp,
        Iso.hom_inv_id_assoc, eqToHom_trans_assoc]
    · by_cases h2 : j.down - i.down = -1
      · have h1j : i.down - j.down = 1 := by omega
        rw [tateT, dif_neg h1, dif_pos h2, tateT, dif_pos h1j]
        simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp,
          Iso.inv_hom_id_assoc, eqToHom_trans_assoc]
      · rw [tateT, dif_neg h1, dif_neg h2]
        haveI : IsEmpty (tateV R I q i j) := (tateV_far R I q h1 h2) ▸ inferInstance
        exact (LocallyRingedSpace.isInitialOfIsEmpty (X := tateV R I q i j)).hom_ext _ _
  cocycle := fun i j k _ _ hjk => by
    haveI := tateF_isOpenImmersion R I q hI i j
    haveI := isEmpty_tatePullback R I q hq hI i hjk
    exact (LocallyRingedSpace.isInitialOfIsEmpty).hom_ext _ _

/-- **The ℤ-indexed Tate chain glue datum as a `LocallyRingedSpace.GlueData`**, produced by
`GlueData.ofGlueData'` together with the open-immersion field `f_open`: off the diagonal each glue
map is `eqToHom ≫ (chart or empty map)`, an isomorphism composed with an open immersion; on the
diagonal it is `eqToHom`, an isomorphism. -/
def tateChainLRSGlueData (hq : q ∈ I) (hI : I.FG) : LocallyRingedSpace.GlueData.{u} :=
  { CategoryTheory.GlueData.ofGlueData' (tateChainGlueData' R I q hq hI) with
    f_open := by
      haveI hoi : ∀ a b : ULift.{u} ℤ, LocallyRingedSpace.IsOpenImmersion (tateF R I q a b) :=
        tateF_isOpenImmersion R I q hI
      rintro i j
      simp only [CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f']
      split_ifs with h
      · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (eqToHom _))
      · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (eqToHom _ ≫ tateF R I q i j)) }

/-- **The ℤ-indexed Tate chain glue datum as a `FormalScheme.GlueData`**: each patch is the affine
formal scheme `Spf A`, whose underlying locally ringed space is the object
`locallyRingedSpaceObj (I·A)` used as `U i`. -/
def tateChainFormalGlueData (hq : q ∈ I) (hI : I.FG) [IsNoetherianRing R] :
    FormalScheme.GlueData.{u} :=
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  { toLocallyRingedSpaceGlueData := tateChainLRSGlueData R I q hq hI
    isFormalScheme := fun _ =>
      ⟨FormalScheme.Spf (annulusIdealOfDefinition R I q), ⟨Iso.refl _⟩⟩ }

/-- **The formal Tate chain `T`**: the (non-affine) formal scheme obtained by gluing the ℤ-indexed
chain of formal Tate annuli `Spf A` along their consecutive overlaps `{x invertible} ≅
{y invertible}`. This is the flagship geometric object of issue 208 — the formal model of the Tate
curve before quotienting by the `q^ℤ`-action (issue 135). -/
def tateChain (hq : q ∈ I) (hI : I.FG) [IsNoetherianRing R] : FormalScheme.{u} :=
  (tateChainFormalGlueData R I q hq hI).gluedFormalScheme

end AlgebraicGeometry
