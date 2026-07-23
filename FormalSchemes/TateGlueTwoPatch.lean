import FormalSchemes.TateChartTransition
import FormalSchemes.Gluing

set_option linter.style.header false

/-!
# The two-patch (`J = Bool`) slice of the Tate chain

Fix an adic base `R` with finitely generated ideal of definition `I` and a Tate parameter
`q : R`, and let `A = R{x, y} / (x·y − q)` be the coordinate ring of the formal Tate annulus with
ideal of definition `I·A`. The flagship goal of issue 208 is the `ℤ`-indexed
`AlgebraicGeometry.FormalScheme.GlueData` of the annulus chain, gluing the consecutive translates
of `Spf A` along their overlaps. This file delivers the sanctioned **two-patch prototype**: the
honest first slice on the index type `Bool` (lifted to the ambient universe as `ULift.{u} Bool`,
since a glue-data index type must live in `Type u`).

Two copies `U₀ = U₁ = Spf A` of the annulus are glued along the overlap where the coordinate is
invertible: the `{x invertible}` locus of `U₀` is identified with the `{y invertible}` locus of
`U₁` via the geometric transition isomorphism `annulusChartTransitionSpf : Spf A{1/x} ≅ Spf A{1/y}`
(`FormalSchemes.TateChartTransition`). Concretely:

* `f` on the `false` side is the affine overlap chart `annulusOverlapChart : Spf A{1/x} ⟶ Spf A`
  and on the `true` side the `y`-analogue `annulusOverlapChartY : Spf A{1/y} ⟶ Spf A`;
* `t` on the `false, true` side is the transition `.hom` and on the `true, false` side its `.inv`.

Because the index type has only **two** elements, no triple `(i, j, k)` can be pairwise distinct, so
in a `CategoryTheory.GlueData'` the fields `t'`, `t_fac` and `cocycle` are all **vacuous**: their
hypotheses `i ≠ j ∧ i ≠ k ∧ j ≠ k` are unsatisfiable on `Bool`. This is what makes the two-patch
slice tractable ahead of the full chain, where the cocycle condition carries real content.

## Main definitions

* `AlgebraicGeometry.tateTwoPatchGlueData'`: the `CategoryTheory.GlueData' LocallyRingedSpace`
  value assembling the two annulus copies and their overlap datum.
* `AlgebraicGeometry.tateTwoPatchLRSGlueData`: the induced
  `AlgebraicGeometry.LocallyRingedSpace.GlueData`, via `CategoryTheory.GlueData.ofGlueData'`
  together with the open-immersion field `f_open`.
* `AlgebraicGeometry.tateTwoPatchFormalGlueData`: the `AlgebraicGeometry.FormalScheme.GlueData`,
  each piece being the affine formal scheme `Spf A`.
* `AlgebraicGeometry.tateTwoPatch`: the glued (non-affine) formal scheme obtained from the two
  patches.

## Remaining work (issue 208)

This is only the `J = Bool` slice. The full flagship deliverable — the `ℤ`-indexed
`FormalScheme.GlueData` of the annulus chain, whose `cocycle` is genuine on adjacent triples, and
the glued structural morphism `T ⟶ Spf R` exhibiting the chain as a formal scheme over the base —
remains open.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- The annulus object `Spf A`, the two patches to be glued. -/
private abbrev tpU : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (annulusIdealOfDefinition R I q)

/-- The `x`-overlap `Spf A{1/x}` (the `false`-side intersection). -/
private abbrev tpVx : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))

/-- The `y`-overlap `Spf A{1/y}` (the `true`-side intersection). -/
private abbrev tpVy : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapY R I q))

/-- On a two-element index type no triple is pairwise distinct: this discharges the vacuous
`t'`, `t_fac` and `cocycle` fields of the two-patch glue data. -/
private theorem tpBool_not_pairwise_distinct {i j k : ULift.{u} Bool}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : False := by
  obtain ⟨i⟩ := i
  obtain ⟨j⟩ := j
  obtain ⟨k⟩ := k
  cases i <;> cases j <;> cases k <;> simp_all

/-- **The two-patch glue datum** of the Tate annulus, as a `CategoryTheory.GlueData'` on the index
type `ULift Bool`: two copies of `Spf A` glued along the overlap `{x invertible} ≅ {y invertible}`
via the geometric transition isomorphism. The three fields `t'`, `t_fac`, `cocycle` are vacuous
because no triple of `Bool`-indices is pairwise distinct. -/
def tateTwoPatchGlueData' (hI : I.FG) : CategoryTheory.GlueData' LocallyRingedSpace.{u} where
  J := ULift.{u} Bool
  U := fun _ => tpU R I q
  V := fun i _ _ => cond i.down (tpVy R I q) (tpVx R I q)
  f := fun i j h => match i, j, h with
    | ⟨false⟩, ⟨true⟩, _ => annulusOverlapChart R I q
    | ⟨true⟩, ⟨false⟩, _ => annulusOverlapChartY R I q
    | ⟨false⟩, ⟨false⟩, h => (h rfl).elim
    | ⟨true⟩, ⟨true⟩, h => (h rfl).elim
  f_mono := by
    haveI := isOpenImmersion_annulusOverlapChart R I q hI
    haveI := isOpenImmersion_annulusOverlapChartY R I q hI
    rintro ⟨_ | _⟩ ⟨_ | _⟩ h
    · exact absurd rfl h
    · exact inferInstanceAs (Mono (annulusOverlapChart R I q))
    · exact inferInstanceAs (Mono (annulusOverlapChartY R I q))
    · exact absurd rfl h
  f_hasPullback := by
    haveI := isOpenImmersion_annulusOverlapChart R I q hI
    haveI := isOpenImmersion_annulusOverlapChartY R I q hI
    rintro ⟨_ | _⟩ ⟨_ | _⟩ ⟨_ | _⟩ hij hik
    · exact absurd rfl hij
    · exact absurd rfl hij
    · exact absurd rfl hik
    · exact inferInstanceAs
        (HasPullback (annulusOverlapChart R I q) (annulusOverlapChart R I q))
    · exact inferInstanceAs
        (HasPullback (annulusOverlapChartY R I q) (annulusOverlapChartY R I q))
    · exact absurd rfl hik
    · exact absurd rfl hij
    · exact absurd rfl hij
  t := fun i j h => match i, j, h with
    | ⟨false⟩, ⟨true⟩, _ => (annulusChartTransitionSpf R I q hI).hom
    | ⟨true⟩, ⟨false⟩, _ => (annulusChartTransitionSpf R I q hI).inv
    | ⟨false⟩, ⟨false⟩, h => (h rfl).elim
    | ⟨true⟩, ⟨true⟩, h => (h rfl).elim
  t' := fun _ _ _ hij hik hjk => (tpBool_not_pairwise_distinct hij hik hjk).elim
  t_fac := fun _ _ _ hij hik hjk => (tpBool_not_pairwise_distinct hij hik hjk).elim
  t_inv := by
    rintro ⟨_ | _⟩ ⟨_ | _⟩ h
    · exact absurd rfl h
    · exact (annulusChartTransitionSpf R I q hI).hom_inv_id
    · exact (annulusChartTransitionSpf R I q hI).inv_hom_id
    · exact absurd rfl h
  cocycle := fun _ _ _ hij hik hjk => (tpBool_not_pairwise_distinct hij hik hjk).elim

/-- **The two-patch glue datum as a `LocallyRingedSpace.GlueData`**: the full
`CategoryTheory.GlueData` produced by `GlueData.ofGlueData'`, together with the open-immersion
field `f_open`. Off the diagonal each glue map is `eqToHom ≫ (overlap chart)`, a composite of an
isomorphism with an open immersion; on the diagonal it is `eqToHom`, an isomorphism. -/
def tateTwoPatchLRSGlueData (hI : I.FG) : LocallyRingedSpace.GlueData.{u} :=
  { CategoryTheory.GlueData.ofGlueData' (tateTwoPatchGlueData' R I q hI) with
    f_open := by
      haveI := isOpenImmersion_annulusOverlapChart R I q hI
      haveI := isOpenImmersion_annulusOverlapChartY R I q hI
      rintro i j
      simp only [CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f']
      split_ifs with h
      · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (eqToHom _))
      · rcases i with ⟨_ | _⟩ <;> rcases j with ⟨_ | _⟩
        · exact absurd rfl h
        · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
            (eqToHom _ ≫ annulusOverlapChart R I q))
        · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
            (eqToHom _ ≫ annulusOverlapChartY R I q))
        · exact absurd rfl h }

/-- **The two-patch glue datum as a `FormalScheme.GlueData`**: each of the two pieces is the affine
formal scheme `Spf A`, whose underlying locally ringed space is definitionally the object
`locallyRingedSpaceObj (I·A)` used as a patch. -/
def tateTwoPatchFormalGlueData (hI : I.FG) [IsNoetherianRing R] :
    FormalScheme.GlueData.{u} :=
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  { toLocallyRingedSpaceGlueData := tateTwoPatchLRSGlueData R I q hI
    isFormalScheme := fun _ =>
      ⟨FormalScheme.Spf (annulusIdealOfDefinition R I q), ⟨Iso.refl _⟩⟩ }

/-- **The glued two-patch formal scheme**: the (non-affine) formal scheme obtained by gluing two
copies of the formal Tate annulus `Spf A` along the overlap `{x invertible} ≅ {y invertible}`. This
is the `J = Bool` slice of the Tate chain (issue 208). -/
def tateTwoPatch (hI : I.FG) [IsNoetherianRing R] : FormalScheme.{u} :=
  (tateTwoPatchFormalGlueData R I q hI).gluedFormalScheme

end AlgebraicGeometry
