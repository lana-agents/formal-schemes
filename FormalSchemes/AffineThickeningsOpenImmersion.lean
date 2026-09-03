import FormalSchemes.AdicOpennessHalf

set_option linter.style.header false

/-!
# The range of an affine open immersion of formal spectra has affine thickenings

`FormalSchemes.AffineThickenings` introduced `FormalSpectrum.HasAffineThickenings I U` and
`FormalSchemes.AdicOpennessHalf` proved the openness half of adicity,
`FormalSpectrum.le_radical_map_of_hasAffineThickenings`, from it. Both files record that whether
the hypothesis holds for the range of an arbitrary open immersion of formal spectra is the one
question left in EGA I 10.12's affine case. **This file answers it, unconditionally.**

## The route, and why it is not the one the predecessors ruled out

`FormalSchemes.AffineThickenings`'s module docstring says the elementary criterion
`AlgebraicGeometry.isAffineOpen_of_isAffineOpen_basicOpen` (Stacks 01QF) cannot be used, because
it needs `Ideal.span s = ⊤` in the sections ring and a cover of an open by its own basic opens does
not supply that off an affine scheme — `𝔸² ∖ {0}` is covered by two basic opens whose span is not
the unit ideal. That is right, and the conclusion drawn from it — *"recovering the span is exactly
the surjectivity of the reduction map, i.e. the statement one is trying to prove"* — is what this
file refutes. The span does not have to come from the level the criterion is applied at. It comes
from the **formal** sections ring, and it is pushed forward:

1. `Γ (range m, O_{Spf R})` is `B`, by `FormalSpectrum.rangeSectionsHom`, which is not merely
   surjective but bijective — `FormalSpectrum.bijective_rangeSectionsHom`, of
   `FormalSchemes.AdicOpennessHalf`, where the surjective half it generalises already lived.
2. The basic opens `D(f) ⊆ range m` cover `range m`, so their images cover `Spf J`; membership
   transports along `m` by `FormalSpectrum.base_toPrimeSpectrum_eq`. A cover of `Spf J` by basic
   opens is the ideal-theoretic statement `Ideal.span s ⊔ J = ⊤`
   (`FormalSpectrum.sup_eq_top_of_forall_exists_mem_basicOpen`, already on the tree).
3. `B` is `J`-adically complete, so `J` lies in its Jacobson radical
   (`IsAdicComplete.le_jacobson_bot`) and drops out of that sup
   (`Ideal.eq_top_of_sup_eq_top_of_isAdicComplete`): the family generates the **unit** ideal of
   `B`, not merely of `B ⧸ J`. This is `FormalSpectrum.span_globalSectionsMap_eq_top`.
4. A ring map carries `1 = ∑ cᵢ bᵢ` to `1 = ∑ φ cᵢ · φ bᵢ`. No surjectivity is needed to push a
   spanning family forward, and `FormalSpectrum.sectionsPi` is the push. So the span the criterion
   wants is available at **every** level of the tower at once.

The reason `𝔸² ∖ {0}` is not a counterexample to this argument is that it is not the range of an
open immersion **from a formal spectrum**: step 1 is where that hypothesis is spent, and it is the
only place other than the range being open.

## What this closes

* `FormalSpectrum.hasAffineThickenings_opensRange` — the hypothesis of every theorem in
  `FormalSchemes.AdicOpennessHalf`, discharged with **no** finiteness hypothesis on `I` or `J` and
  no condition on the range.
* `FormalSpectrum.le_radical_map_of_openImmersion` — the openness half `J ≤ √(I · B)`, for an
  arbitrary affine open immersion, needing only `I.FG`.
* `FormalSpectrum.isCofinal_map_of_openImmersion` — **an affine open immersion of formal spectra is
  adic up to cofinality**, `Ideal.IsCofinal J (I.map (algebraMap R B))`, needing `I.FG` and `J.FG`.
  This is EGA I 10.12's statement, and the on-the-nose form `I · B ≤ J` is false — see
  `FormalSchemes.AdicOnSections` for the counterexample `Spf (y ^ 2) ≅ Spf (y)`.
* `AlgebraicGeometry.IsTopologicallyFiniteType.of_openImmersion` — conservativity's affine step:
  an arbitrary affine open of `Spf I`, presented by any open immersion, is topologically of finite
  type over `(R, I)`. `FormalSchemes.AffineOpenTopFiniteType`'s
  `AlgebraicGeometry.IsTopologicallyFiniteType.of_openImmersion_of_isCofinal` is where the
  cofinality was consumed and this is its hypothesis discharged.

## Main results

* `FormalSpectrum.hasAffineThickenings_of_span_eq_top`: the criterion in reusable form — an open
  covered by basic opens whose structural sections span the unit ideal of `Γ (U, O_{Spf R})` has
  affine thickenings. This is the only place where
  `AlgebraicGeometry.isAffineOpen_of_isAffineOpen_basicOpen` is used, and it mentions no
  morphism.
* `Ideal.eq_top_of_sup_eq_top_of_isAdicComplete`: an ideal of definition of a complete ring is
  superfluous in a sup — the step that turns a cover of `Spf J`, which only ever sees `B ⧸ J`,
  into a spanning family of `B`.
* `FormalSpectrum.span_globalSectionsMap_eq_top`: the elements of `B` attached to the basic opens
  inside the range span the unit ideal.
* `FormalSpectrum.hasAffineThickenings_opensRange`, and the four consequences listed above.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.12, §10.13.
* [The Stacks Project, Tag 01QF](https://stacks.math.columbia.edu/tag/01QF).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- **The basic open of a restricted global section of an affine scheme.** For `a : A` and an open
`V ⊆ Spec A`, the basic open cut out by the restriction of `a` to `V` is `V ⊓ D(a)`.

This is `AlgebraicGeometry.Scheme.basicOpen_res` followed by
`AlgebraicGeometry.basicOpen_eq_of_affine`; it is stated separately because the rewrite has to
happen in the `Spec` spelling, and the tree's thickening sheaves present their sections in the
`AlgebraicGeometry.Spec.structureSheaf` one. -/
theorem basicOpen_res_ΓSpecIso_inv {A : CommRingCat.{u}} (a : A) (V : (Spec A).Opens) :
    (Spec A).basicOpen ((Spec A).presheaf.map (homOfLE (le_top (a := V))).op
        ((Scheme.ΓSpecIso A).inv a)) = V ⊓ PrimeSpectrum.basicOpen a := by
  rw [Scheme.basicOpen_res, basicOpen_eq_of_affine]

end AlgebraicGeometry

namespace Ideal

/-- **An ideal of definition of a complete ring is superfluous in a sup.** If `K ⊔ J = ⊤` and `B`
is `J`-adically complete then already `K = ⊤`.

`J` lies in the Jacobson radical of `B` (`IsAdicComplete.le_jacobson_bot`), so an element of `K`
congruent to `1` modulo `J` is a unit (`Ideal.isUnit_of_sub_one_mem_jacobson_bot`). This is the
step that turns a covering statement, which is only ever about `B ⧸ J`, into a spanning statement
in `B`. -/
theorem eq_top_of_sup_eq_top_of_isAdicComplete {B : Type u} [CommRing B] (J : Ideal B)
    [IsAdicComplete J B] {K : Ideal B} (h : K ⊔ J = ⊤) : K = ⊤ := by
  have h1 : (1 : B) ∈ K ⊔ J := by rw [h]; trivial
  obtain ⟨k, hk, j, hj, hkj⟩ := Submodule.mem_sup.mp h1
  refine Ideal.eq_top_of_isUnit_mem K hk (Ideal.isUnit_of_sub_one_mem_jacobson_bot k ?_)
  have hsub : k - 1 = -j := by rw [← hkj]; ring
  rw [hsub]
  exact neg_mem (IsAdicComplete.le_jacobson_bot J hj)

end Ideal

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

/-!
### The criterion

Everything in this section is about one open of `Spf R` and mentions no morphism.
-/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- `FormalSpectrum.thickeningOpen` is monotone: it is a preimage. -/
theorem thickeningOpen_mono (n : ℕ) {U V : Opens (FormalSpectrum I)} (h : U ≤ V) :
    thickeningOpen I n U ≤ thickeningOpen I n V :=
  fun _ hx => h hx

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The basic opens of `Spf R` are a neighbourhood basis**, in the form the criterion below
consumes: a point of an open lies in a `FormalSpectrum.basicOpen` inside it.

`FormalSpectrum.isBasis_basicOpen` (`FormalSchemes.SpfGammaRoundTrip`) is the tree's own
`TopologicalSpace.Opens.IsBasis` packaging of `FormalSpectrum.isTopologicalBasis_basicOpen`, and
`TopologicalSpace.Opens.isBasis_iff_nbhd` is that packaging's point of existing — so nothing here
goes back to `PrimeSpectrum.isBasis_basic_opens`. -/
theorem exists_basicOpen_le (U : Opens (FormalSpectrum I)) (x : FormalSpectrum I) (hx : x ∈ U) :
    ∃ f : R, x ∈ basicOpen I f ∧ basicOpen I f ≤ U := by
  obtain ⟨_, ⟨f, rfl⟩, hxV, hVU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (isBasis_basicOpen I) hx
  exact ⟨f, hxV, hVU⟩

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The basic open cut out at level `n` by the structural section attached to `f : R`.**
`FormalSpectrum.thickeningSectionsMk` is, definitionally, the restriction to
`FormalSpectrum.thickeningOpen` of the global section of `Spec (R ⧸ I ^ (n + 1))` attached to the
residue of `f`, so `AlgebraicGeometry.basicOpen_res_ΓSpecIso_inv` computes its basic open. -/
theorem basicOpen_thickeningSectionsMk (n : ℕ) (U : Opens (FormalSpectrum I)) (f : R) :
    (Spec (CommRingCat.of (R ⧸ I ^ (n + 1)))).basicOpen (thickeningSectionsMk I n U f) =
      thickeningOpen I n U ⊓ PrimeSpectrum.basicOpen (Ideal.Quotient.mk (I ^ (n + 1)) f) := by
  have h : thickeningSectionsMk I n U f =
      ((Spec (CommRingCat.of (R ⧸ I ^ (n + 1)))).presheaf.map
        (homOfLE (le_top (a := thickeningOpen I n U))).op).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I ^ (n + 1)))).inv.hom
          (Ideal.Quotient.mk (I ^ (n + 1)) f)) := rfl
  rw [h]
  exact basicOpen_res_ΓSpecIso_inv (A := CommRingCat.of (R ⧸ I ^ (n + 1)))
    (Ideal.Quotient.mk (I ^ (n + 1)) f) (thickeningOpen I n U)

variable {I}

/-- **The criterion.** An open `U ⊆ Spf R` has affine thickenings as soon as there is a family
`T ⊆ R` of elements whose basic opens lie inside `U` and whose structural sections span the unit
ideal of `Γ (U, O_{Spf R})`.

Both halves of `AlgebraicGeometry.isAffineOpen_of_isAffineOpen_basicOpen` are supplied at once and
at every level: the affineness of each piece because `D(f) ⊆ U` makes the basic open cut out at
level `n` equal to `D(f mod I ^ (n + 1))` (`FormalSpectrum.basicOpen_thickeningSectionsMk` and
`FormalSpectrum.thickeningOpen_basicOpen`), and the span because
`FormalSpectrum.sectionsPi` is a ring map and a ring map carries a spanning family to a spanning
family (`Ideal.map_span`, `Ideal.map_top`) — *no* surjectivity is involved.

`FormalSpectrum.sectionsPi_comp_sectionsOpenHom` is what identifies the level-`n` image of the
structural map with `FormalSpectrum.thickeningSectionsMk`. -/
theorem hasAffineThickenings_of_span_eq_top {U : Opens (FormalSpectrum I)} (T : Set R)
    (hT : ∀ f ∈ T, basicOpen I f ≤ U)
    (hspan : Ideal.span (sectionsOpenHom I U '' T) = ⊤) :
    HasAffineThickenings I U := by
  intro n
  refine isAffineOpen_of_isAffineOpen_basicOpen _
    ((sectionsPi I n U).hom '' (sectionsOpenHom I U '' T)) ?_ ?_
  · -- `rw` cannot act on the goal directly: its motive is not type-correct at `instances`
    -- transparency, the two presentations of the section ring being defeq but not syntactically
    -- equal. Restating and closing with `exact` is the tree's standing workaround.
    have hfin : Ideal.span ((sectionsPi I n U).hom '' (sectionsOpenHom I U '' T)) = ⊤ := by
      rw [← Ideal.map_span, hspan, Ideal.map_top]
    exact hfin
  · rintro _ ⟨t, ⟨f, hf, rfl⟩, rfl⟩
    have heq : (sectionsPi I n U).hom (sectionsOpenHom I U f) = thickeningSectionsMk I n U f :=
      DFunLike.congr_fun (sectionsPi_comp_sectionsOpenHom I n U) f
    have hle : PrimeSpectrum.basicOpen (Ideal.Quotient.mk (I ^ (n + 1)) f) ≤
        thickeningOpen I n U := by
      rw [← thickeningOpen_basicOpen I n f]
      exact thickeningOpen_mono I n (hT f hf)
    have hb : (Spec (CommRingCat.of (R ⧸ I ^ (n + 1)))).basicOpen
        ((sectionsPi I n U).hom (sectionsOpenHom I U f)) =
          PrimeSpectrum.basicOpen (Ideal.Quotient.mk (I ^ (n + 1)) f) := by
      have h1 : (Spec (CommRingCat.of (R ⧸ I ^ (n + 1)))).basicOpen
          ((sectionsPi I n U).hom (sectionsOpenHom I U f)) =
            (Spec (CommRingCat.of (R ⧸ I ^ (n + 1)))).basicOpen
              (thickeningSectionsMk I n U f) := congrArg _ heq
      rw [h1, basicOpen_thickeningSectionsMk I n U f, inf_eq_right.mpr hle]
    have hfin : IsAffineOpen (X := Spec (CommRingCat.of (R ⧸ I ^ (n + 1))))
        ((Spec (CommRingCat.of (R ⧸ I ^ (n + 1)))).basicOpen
          ((sectionsPi I n U).hom (sectionsOpenHom I U f))) := by
      rw [hb]
      exact IsAffineOpen.Spec_basicOpen _
    exact hfin

/-!
### The range of an open immersion
-/

section OpenImmersion

variable (I)
variable {B : Type u} [CommRing B] [TopologicalSpace B] (J : Ideal B) [IsAdicRing J]
variable (m : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
  [hm : LocallyRingedSpace.IsOpenImmersion m]

/-- The family of elements of `R` whose basic open lies inside the range of `m`. -/
def rangeBasicOpens : Set R :=
  {f : R | basicOpen I f ≤ LocallyRingedSpace.IsOpenImmersion.opensRange m}

omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace B] [IsAdicRing J] in
/-- Membership in `FormalSpectrum.rangeBasicOpens` unfolded. -/
theorem basicOpen_le_opensRange_of_mem {f : R} (hf : f ∈ rangeBasicOpens I J m) :
    basicOpen I f ≤ LocallyRingedSpace.IsOpenImmersion.opensRange m :=
  hf

/-- **The images in `B` of the elements of `FormalSpectrum.rangeBasicOpens` span the unit ideal.**

Two inputs. The basic opens inside the range cover `Spf J`, because membership transports along
`m` (`FormalSpectrum.base_toPrimeSpectrum_eq`), and a cover of `Spf J` by basic opens is
`Ideal.span s ⊔ J = ⊤` (`FormalSpectrum.sup_eq_top_of_forall_exists_mem_basicOpen`, which is
`FormalSchemes.AffineOpenTopFiniteType`'s and is reused rather than reproved). Then `J` drops out
of the sup, because `B` is `J`-adically complete
(`Ideal.eq_top_of_sup_eq_top_of_isAdicComplete`). That second step is the one that upgrades a span
in `B ⧸ J`, which is free, to a span in `B`, which is what the criterion consumes. -/
theorem span_globalSectionsMap_eq_top :
    Ideal.span (globalSectionsMap I J m '' rangeBasicOpens I J m) = ⊤ := by
  refine Ideal.eq_top_of_sup_eq_top_of_isAdicComplete J
    (sup_eq_top_of_forall_exists_mem_basicOpen J _ fun z => ?_)
  obtain ⟨f, hxf, hfU⟩ :=
    exists_basicOpen_le I (LocallyRingedSpace.IsOpenImmersion.opensRange m) (m.base z)
      (Set.mem_range_self z)
  refine ⟨globalSectionsMap I J m f, ⟨f, hfU, rfl⟩, ?_⟩
  -- `f` avoids the prime at `m z`, so its image avoids the prime at `z`
  have hnot : f ∉ (toPrimeSpectrum I (m.base z)).asIdeal := hxf
  rw [base_toPrimeSpectrum_eq I J m z] at hnot
  exact hnot

/-- **The range of an affine open immersion of formal spectra has affine thickenings.**

No hypothesis: not `I.FG`, not `J.FG`, and no condition on the range. This is the statement
`FormalSchemes.AffineThickenings` and `FormalSchemes.AdicOpennessHalf` both name as the one thing
left in EGA I 10.12's affine case.

`FormalSpectrum.span_globalSectionsMap_eq_top` gives the span in `B`, and
`FormalSpectrum.bijective_rangeSectionsHom` transports it back across
`FormalSpectrum.rangeSectionsHom` to `Γ (range m, O_{Spf R})`, where
`FormalSpectrum.hasAffineThickenings_of_span_eq_top` consumes it. -/
theorem hasAffineThickenings_opensRange :
    HasAffineThickenings I (LocallyRingedSpace.IsOpenImmersion.opensRange m) := by
  set U := LocallyRingedSpace.IsOpenImmersion.opensRange m with hU
  set e := rangeSectionsHom I J m with he
  have hbij := bijective_rangeSectionsHom I J m
  refine hasAffineThickenings_of_span_eq_top (rangeBasicOpens I J m)
    (fun f hf => basicOpen_le_opensRange_of_mem I J m hf) ?_
  -- the span in `B`, pulled back along the bijection `e`
  have himg : e '' (sectionsOpenHom I U '' rangeBasicOpens I J m) =
      globalSectionsMap I J m '' rangeBasicOpens I J m := by
    rw [← Set.image_comp]
    exact Set.image_congr fun f _ => rangeSectionsHom_sectionsOpenHom I J m f
  have hmapped : Ideal.map e (Ideal.span (sectionsOpenHom I U '' rangeBasicOpens I J m)) = ⊤ := by
    rw [Ideal.map_span, himg]
    exact span_globalSectionsMap_eq_top I J m
  have hker : Ideal.comap e (⊥ : Ideal B) = ⊥ := by
    rw [← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot e).mp hbij.1
  have hcomap := congrArg (Ideal.comap e) hmapped
  rwa [Ideal.comap_map_of_surjective e hbij.2, hker, sup_bot_eq, Ideal.comap_top] at hcomap

section Algebra

variable [Algebra R B]

/-- **The openness half of adicity, for an arbitrary affine open immersion.**
`FormalSpectrum.le_radical_map_of_hasAffineThickenings` with its hypothesis discharged by
`FormalSpectrum.hasAffineThickenings_opensRange`. -/
theorem le_radical_map_of_openImmersion (halg : algebraMap R B = globalSectionsMap I J m)
    (hI : I.FG) :
    J ≤ (I.map (algebraMap R B)).radical :=
  le_radical_map_of_hasAffineThickenings I J m halg hI (hasAffineThickenings_opensRange I J m)

/-- **An affine open immersion of formal spectra is adic, up to cofinality** — EGA I 10.12.

`Ideal.IsCofinal J (I.map (algebraMap R B))`: the extension of the ideal of definition of the
target is again an ideal of definition of the source. The on-the-nose containment `I · B ≤ J` is
**false**, and `FormalSchemes.AdicOnSections` records the counterexample
(`FormalSpectrum.cofinalSpfIso` presents `Spf (y ^ 2) ≅ Spf (y)` over a power series ring, an
isomorphism whose global-sections map carries `(y)` outside `(y ^ 2)`), so cofinality is the
sharpest true form. -/
theorem isCofinal_map_of_openImmersion (halg : algebraMap R B = globalSectionsMap I J m)
    (hI : I.FG) (hJ : J.FG) :
    Ideal.IsCofinal J (I.map (algebraMap R B)) :=
  isCofinal_map_of_hasAffineThickenings I J m hI hJ halg (hasAffineThickenings_opensRange I J m)

end Algebra

end OpenImmersion

end FormalSpectrum

namespace AlgebraicGeometry

open FormalSpectrum

variable {R : Type u} [CommRing R] {I : Ideal R} [TopologicalSpace R] [IsAdicRing I]
variable {B : Type u} [CommRing B] [TopologicalSpace B] {J : Ideal B} [IsAdicRing J]
variable [Algebra R B]

/-- **Conservativity's affine step, unconditionally.** An affine open of `Spf I`, presented by an
arbitrary open immersion of formal spectra, is topologically of finite type over `(R, I)`.

`FormalSchemes.AffineOpenTopFiniteType`'s
`AlgebraicGeometry.IsTopologicallyFiniteType.of_openImmersion_of_isCofinal` reduced this to a
cofinality, and `FormalSpectrum.isCofinal_map_of_openImmersion` supplies it. Compare
`AlgebraicGeometry.IsTopologicallyFiniteType.of_openImmersion_range_eq_basicOpen`, which is this
statement for an open immersion whose range is basic. -/
theorem IsTopologicallyFiniteType.of_openImmersion (hI : I.FG) (hJ : J.FG)
    (m : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    [LocallyRingedSpace.IsOpenImmersion m]
    (halg : algebraMap R B = globalSectionsMap I J m) :
    IsTopologicallyFiniteType R I B (I.map (algebraMap R B)) :=
  IsTopologicallyFiniteType.of_openImmersion_of_hasAffineThickenings hI hJ m halg
    (hasAffineThickenings_opensRange I J m)

end AlgebraicGeometry
