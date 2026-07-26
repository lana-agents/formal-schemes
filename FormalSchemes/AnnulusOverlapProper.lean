import FormalSchemes.AnnulusNontrivial
import FormalSchemes.TateOverlapImmersion

set_option linter.style.header false

/-!
# The Tate-annulus overlap `D(x)` is a *proper* open of the patch

Fix an adic base `(R, I)` and a Tate parameter `q ∈ I`, and let `A = R{x, y} / (x·y − q)` be the
Tate annulus. The overlap of two consecutive patches of the Tate chain is the basic open
`D(x) ⊆ Spf A` where the coordinate `x` is invertible (`FormalSchemes.TateOverlapImmersion`,
`annulusOverlapChart`). This file records that, when `I ≠ ⊤`, that overlap is a **proper** subset of
`Spf A`: it does not exhaust the patch.

The reason is that the annulus coordinate `x = overlapX` is a **non-unit** in the special fibre
`A ⧸ (I·A)`: the augmentation `A → R ⧸ I` of `FormalSchemes.AnnulusNontrivial` sends `x ↦ 0`, and
`0` is not a unit of the nontrivial ring `R ⧸ I`. Hence `x` lies in some maximal ideal of the
special fibre, giving a point of `Spf A` outside `D(x)`.

This is the last geometric input the Tate-chain **freeness** argument needs for the neighbouring
translate: if a patch coincided with its neighbour, the overlap inclusion `D(x) ↪ Spf A` would be
surjective, i.e. `D(x)` would be all of `Spf A` — contradicted here.

## Main results

* `overlapX_not_isUnit`: for `I ≠ ⊤`, the residue of `x` in `A ⧸ (I·A)` is not a unit.
* `range_annulusOverlapChart_ne_univ`: for `I ≠ ⊤`, the range of `annulusOverlapChart` (the open
  `D(x)`) is a proper subset of `Spf A`.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum TopologicalSpace

universe u

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- **The annulus coordinate `x` is a non-unit in the special fibre `A ⧸ (I·A)`.** The augmentation
`A → R ⧸ I` (`annulusAugAlg`) kills the ideal of definition `I·A`, so it descends to
`A ⧸ (I·A) → R ⧸ I`, under which the residue of `x` maps to `0` (`annulusAug_annulusX`). For `I ≠ ⊤`
the target `R ⧸ I` is nontrivial, in which `0` is not a unit, so the residue of `x` cannot be a unit
either. -/
theorem overlapX_not_isUnit (hq : q ∈ I) (hItop : I ≠ ⊤) :
    ¬ IsUnit (Ideal.Quotient.mk (annulusIdealOfDefinition R I q) (overlapX R I q)) := by
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
  -- The augmentation kills `I·A = I.map (algebraMap R A)`, so it descends to the special fibre.
  have hle : I.map (algebraMap R (annulusAlgebra R I q)) ≤
      RingHom.ker (annulusAugAlg R I q hq) := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    simp only [Ideal.mem_comap, RingHom.mem_ker, annulusAugAlg_algebraMap,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hr
  let ψ : (annulusAlgebra R I q ⧸ annulusIdealOfDefinition R I q) →+* R ⧸ I :=
    Ideal.Quotient.lift (annulusIdealOfDefinition R I q) (annulusAugAlg R I q hq) <| by
      rw [← annulus_map_eq]
      exact fun a ha => RingHom.mem_ker.mp (hle ha)
  intro hunit
  have hu : IsUnit (ψ (Ideal.Quotient.mk (annulusIdealOfDefinition R I q) (overlapX R I q))) :=
    hunit.map ψ
  rw [Ideal.Quotient.lift_mk] at hu
  have hzero : annulusAugAlg R I q hq (overlapX R I q) = 0 := by
    rw [overlapX, annulusAugAlg_mk, annulusAug_annulusX]
  rw [hzero] at hu
  exact not_isUnit_zero hu

/-- **The overlap `D(x)` is a proper open of the patch `Spf A`.** For `I ≠ ⊤` the range of the
overlap chart `annulusOverlapChart : Spf A{1/x} ⟶ Spf A` — the basic open `D(x)` — is not all of
`Spf A`, because the coordinate `x` is a non-unit in the special fibre, hence lies in some maximal
ideal, giving a point of `Spf A` outside `D(x)`. -/
theorem range_annulusOverlapChart_ne_univ (hq : q ∈ I) (hI : I.FG) (hItop : I ≠ ⊤) :
    Set.range (annulusOverlapChart R I q).base ≠ Set.univ := by
  -- A maximal ideal containing the non-unit residue of `x` gives a point outside `D(x)`.
  have hspan : Ideal.span {Ideal.Quotient.mk (annulusIdealOfDefinition R I q) (overlapX R I q)} ≠
      ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact overlapX_not_isUnit R I q hq hItop
  obtain ⟨m, hmax, hle⟩ := Ideal.exists_le_maximal _ hspan
  have hmem : Ideal.Quotient.mk (annulusIdealOfDefinition R I q) (overlapX R I q) ∈ m :=
    hle (Ideal.subset_span rfl)
  -- The prime point `⟨m⟩ ∈ Spf A` lies in `D(x)`'s complement, so `D(x)` is not the whole space.
  intro htop
  have hin : (⟨m, hmax.isPrime⟩ : FormalSpectrum (annulusIdealOfDefinition R I q)) ∈
      Set.range (annulusOverlapChart R I q).base := by rw [htop]; exact Set.mem_univ _
  -- Membership in `range = D(x)` reduces (definitionally) to `x ∉ m`, contradicting `hmem`.
  exact (Set.ext_iff.mp (range_annulusOverlapChart_base R I q hI) ⟨m, hmax.isPrime⟩).mp hin hmem

end
