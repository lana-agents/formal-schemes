import FormalSchemes.AdicOnOpenSections
import FormalSchemes.ThickeningTowerKernel

set_option linter.style.header false

/-!
# The limit step: the kernel of the reduction map on sections

`FormalSchemes.AdicCofinalOpenImmersion` reduces the adicity of an affine open immersion of formal
spectra to its **openness half** `J ≤ √(I · B)`, and records a sketch for it: write
`B = Γ (U, O_{Spf R})` as the inverse limit of `Bₙ = Γ (U, O_{Spec (R ⧸ I ^ (n + 1))})` and run
successive approximation against a finite generating set of `I`. `FormalSchemes.AffineThickenings`
supplies the first two inputs of that sketch from `FormalSpectrum.HasAffineThickenings`
(`Bₙ₊₁ ↠ Bₙ` and `B ↠ B₀`) and `FormalSchemes.ThickeningTowerKernel` the third
(`ker (Bₙ₊₁ → Bₙ) = I ^ (n + 1) · Bₙ₊₁`, hence `ker (Bₙ ↠ B₀) = I · Bₙ`). **This file runs the
approximation itself**: over an open with affine thickenings and for a finitely generated `I`,

`ker (Γ (U, O_{Spf R}) ↠ Γ (U, thickeningSheaf I 0)) = I · Γ (U, O_{Spf R})`.

Nothing here touches the openness half. The sketch's remaining step — that
`√(ker (B ↠ B₀)) = √J`, because both cut out the same subset — is a statement about the *two*
presentations of the open and is not attempted here; see "What this does not do" below. It is not
open either: `FormalSpectrum.le_radical_map_of_hasAffineThickenings`
(`FormalSchemes.AdicOpennessHalf`, the one module importing this one) runs it off the statement
below and settles `J ≤ √(I · B)` under the same `FormalSpectrum.HasAffineThickenings` hypothesis.

## The argument, and the one place it is delicate

Write `I = span s` for a finite `s`. An element `b` with `b₀ = 0` has, at each level `n`, a
representation `bₙ = ∑ x ∈ s, x · aₙ x` because `bₙ ∈ ker (Bₙ ↠ B₀) = I · Bₙ`. The obvious
induction — lift `aₙ` along `Bₙ₊₁ ↠ Bₙ` and correct — **does not produce a compatible family**,
and the reason is exact rather than technical. The correction `d = bₙ₊₁ − ∑ x · ãₙ x` lies in
`ker (Bₙ₊₁ → Bₙ) = I ^ (n + 1) · Bₙ₊₁`; splitting it as `∑ x · eₙ x` puts `eₙ x` in
`I ^ n · Bₙ₊₁`, which is *not* inside `ker (Bₙ₊₁ → Bₙ)`. So `aₙ₊₁ = ãₙ + eₙ` satisfies the
representation at level `n + 1` but only

`(Bₙ₊₁ → Bₙ) (aₙ₊₁ x) − aₙ x ∈ I ^ n · Bₙ`,

a Cauchy condition, not a compatibility. What repairs it is that the error is *already zero one
level down*: `I ^ n` dies in `Bₘ` for every `m < n` (`FormalSpectrum.map_thickeningSectionsMk_pow`),
so the family `m ↦ (Bₘ₊₁ → Bₘ) (aₘ₊₁ x)` **is** compatible on the nose, and it is that family, not
`m ↦ aₘ x`, that names the element of the limit. Only one-step transition maps appear anywhere in
the argument; no arbitrary-level form of the kernel is needed.

`Ideal.FG` enters exactly once, in the splitting of `d`
(`Ideal.exists_sum_of_mem_map_span_mul`), which is where the sketch says it should: nothing
earlier in the chain uses finite generation.

## What this does not do

* It says nothing about `J`. Relating `I · B` to the ideal of definition of a presentation of `U`
  is the whole of the openness half, and `FormalSchemes.AdicCofinalOpenImmersion`'s refutation of
  the on-the-nose containment `I · B ≤ J` is untouched, as is
  `FormalSchemes.AdicOnSections`'s record of it.
* `FormalSpectrum.HasAffineThickenings` remains a hypothesis. Whether it holds for an arbitrary
  affine open immersion of formal spectra is the question `FormalSchemes.AffineThickenings`
  isolates, and this file does not touch it either. The two unconditional cases are inherited:
  `⊤` and every basic open.

## Main definitions

* `FormalSpectrum.sectionsCone`, `FormalSpectrum.isLimitSectionsCone`: the tower of sections over
  `U`, presented as a limit cone whose point is `Γ (U, O_{Spf R})` itself rather than the
  categorical `limit`, so that the projections are literally `FormalSpectrum.sectionsPi`.
* `FormalSpectrum.sectionsMkCone`, `FormalSpectrum.sectionsMk`: the cone over the same tower with
  point `R`, and the canonical ring map `R →+* Γ (U, O_{Spf R})` it induces — the map along which
  `I · Γ (U, O_{Spf R})` is an extension. It is characterised by
  `FormalSpectrum.sectionsPi_comp_sectionsMk`, which pins it uniquely, and
  `FormalSpectrum.globalSectionsEquiv_sectionsMk_top` identifies it at `⊤` with the identity of
  `R` under `FormalSpectrum.globalSectionsEquiv`.

  **It is not a new map.** `FormalSpectrum.sectionsMk_eq_sectionsOpenHom` identifies it with
  `FormalSpectrum.sectionsOpenHom` (`FormalSchemes.AdicOnOpenSections`), which is the structural
  map this tree already fixes at an arbitrary open — and whose basic-open alias
  `FormalSpectrum.sectionsBasicOpenHom` is reconciled with it the same way, by
  `FormalSpectrum.sectionsOpenHom_basicOpen`. The limit presentation is what this file needs to
  *run the approximation*; the reconciliation is what lets the answer be stated in the ideal every
  consumer of `FormalSchemes.AdicOnOpenSections` already speaks,
  `FormalSpectrum.sectionsOpenIdeal`.
* `FormalSpectrum.sectionsQuotientEquiv`: the resulting `B ⧸ I · B ≃+* B₀`.

## Main results

* `CategoryTheory.Limits.exists_forall_π_app_eq_of_step`: a family of elements of a tower indexed
  by `ℕᵒᵖ` that is compatible with the **one-step** transition maps comes from the limit, in any
  concrete category whose forgetful functor preserves that limit. Its plumbing is
  `CategoryTheory.Limits.map_op_homOfLE_of_step`.
* `Ideal.exists_sum_of_mem_map_span_mul`: an element of `Ideal.map f (span s * K)` is
  `∑ x ∈ s, f x * e x` with every `e x` in `Ideal.map f K`.
* `CategoryTheory.Limits.ker_eq_map_of_isLimit`: **the successive approximation**, for an
  arbitrary tower in `CommRingCat` indexed by `ℕᵒᵖ` with surjective one-step transition maps whose
  kernels are the extensions of the powers of a finitely generated ideal.
* `FormalSpectrum.ker_sectionsPi_zero`: **the limit step**, `ker (B ↠ B₀) = I · B` over an open
  with affine thickenings. `FormalSpectrum.ker_sectionsPi_zero_top` and
  `FormalSpectrum.ker_sectionsPi_zero_basicOpen` are its two instances with no hypothesis on the
  open, and `FormalSpectrum.ker_sectionsPi_zero_eq_sectionsOpenIdeal` is the same statement in the
  spelling `FormalSchemes.AdicOnOpenSections` uses.
* `FormalSpectrum.sectionsMk_eq_sectionsOpenHom`: **the new map is the old one.** Both are pinned
  by `FormalSpectrum.sectionsPi`, so the limit's uniqueness identifies them; the ingredients are
  `FormalSpectrum.sectionsPi_naturality`, `FormalSpectrum.restrict_thickeningSectionsMk` and the
  `⊤` case `FormalSpectrum.sectionsMk_top_eq`, which is `globalSectionsEquiv_sectionsMk_top` read
  as an equation of maps.
* `FormalSpectrum.stepSheafHom_app_thickeningSectionsMk` and `FormalSpectrum.sectionsCone_π_app`:
  the plumbing that makes the two cones cones — the canonical maps `R →+* Bₙ` commute with the
  transition maps of the tower, and the legs of `FormalSpectrum.sectionsCone` are the projections
  `FormalSpectrum.sectionsPi`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.12.
* [The Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe w v u

namespace CategoryTheory.Limits

section NatTower

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type w}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} C FC]

/-- A family of elements of a tower indexed by `ℕᵒᵖ` that is compatible with the one-step
transition maps is compatible with every transition map. -/
theorem map_op_homOfLE_of_step {T : ℕᵒᵖ ⥤ C} {u : ∀ n : ℕ, ToType (T.obj ⟨n⟩)}
    (hu : ∀ n, (T.map (homOfLE (Nat.le_succ n)).op) (u (n + 1)) = u n) {m n : ℕ} (hmn : m ≤ n) :
    (T.map (homOfLE hmn).op) (u n) = u m := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    have hcomp : (homOfLE (hmn.trans (Nat.le_succ n))).op
        = (homOfLE (Nat.le_succ n)).op ≫ (homOfLE hmn).op := by
      rw [← op_comp]
      exact congrArg Quiver.Hom.op (Subsingleton.elim _ _)
    rw [hcomp, T.map_comp, ConcreteCategory.comp_apply, hu n, ih]

/-- **A step-compatible family of elements of a tower indexed by `ℕᵒᵖ` comes from the limit.**
The compatibility is only required for the one-step transition maps. -/
theorem exists_forall_π_app_eq_of_step {T : ℕᵒᵖ ⥤ C} {c : Cone T} (hc : IsLimit c)
    [PreservesLimit T (CategoryTheory.forget C)] (u : ∀ n : ℕ, ToType (T.obj ⟨n⟩))
    (hu : ∀ n, (T.map (homOfLE (Nat.le_succ n)).op) (u (n + 1)) = u n) :
    ∃ z : ToType c.pt, ∀ n : ℕ, c.π.app ⟨n⟩ z = u n := by
  have hT : IsLimit ((CategoryTheory.forget C).mapCone c) :=
    isLimitOfPreserves (CategoryTheory.forget C) hc
  refine ⟨(Types.isLimitEquivSections hT).symm ⟨fun j => u j.unop, ?_⟩, fun n => ?_⟩
  · rintro ⟨m⟩ ⟨n⟩ f
    have hnm : n ≤ m := leOfHom f.unop
    have hf : f = (homOfLE hnm).op := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    subst hf
    exact map_op_homOfLE_of_step hu hnm
  · exact Types.isLimitEquivSections_symm_apply hT _ ⟨n⟩

end NatTower

end CategoryTheory.Limits

namespace Ideal

/-- **Splitting an element of an extended product ideal along a finite generating set.**
If `d` lies in the extension along `f` of `span s * K`, then `d = ∑ x ∈ s, f x * e x` for
coefficients `e x` lying in the extension of `K`. -/
theorem exists_sum_of_mem_map_span_mul {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (s : Finset R) (K : Ideal R) {d : S}
    (hd : d ∈ Ideal.map f (Ideal.span (s : Set R) * K)) :
    ∃ e : R → S, (∀ x, e x ∈ Ideal.map f K) ∧ d = ∑ x ∈ s, f x * e x := by
  classical
  rw [Ideal.map_mul, Ideal.map_span] at hd
  refine Submodule.mul_induction_on hd ?_ ?_
  · intro m hm n hn
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨fun z => if z = y then n else 0, fun z => ?_, ?_⟩
      · by_cases hz : z = y <;> simp [hz, hn]
      · rw [Finset.sum_eq_single_of_mem y hy (fun z _ hzy => by simp [hzy])]
        simp
    | zero => exact ⟨fun _ => 0, fun _ => Submodule.zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨ex, hex, hxe⟩ := hx
      obtain ⟨ey, hey, hye⟩ := hy
      refine ⟨fun z => ex z + ey z, fun z => Submodule.add_mem _ (hex z) (hey z), ?_⟩
      rw [add_mul, hxe, hye, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun z _ => by ring
    | smul a x _ hx =>
      obtain ⟨ex, hex, hxe⟩ := hx
      refine ⟨fun z => a * ex z, fun z => Ideal.mul_mem_left _ _ (hex z), ?_⟩
      rw [smul_eq_mul, mul_assoc, hxe, Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by ring
  · intro x y hx hy
    obtain ⟨ex, hex, hxe⟩ := hx
    obtain ⟨ey, hey, hye⟩ := hy
    refine ⟨fun z => ex z + ey z, fun z => Submodule.add_mem _ (hex z) (hey z), ?_⟩
    rw [hxe, hye, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring

end Ideal

namespace CategoryTheory.Limits

section TowerKernel

variable {R : Type u} [CommRing R] (I : Ideal R) {T : ℕᵒᵖ ⥤ CommRingCat.{u}} {c : Cone T}

/-- **The successive approximation, for an abstract tower.**

Let `T` be a tower of commutative rings indexed by `ℕᵒᵖ` with a limit cone `c`, let `φ n` and `Φ`
be compatible structure maps from `R` to the levels and to the cone point, and suppose the
one-step transition maps are surjective with `ker (T n₊₁ → T n) = I ^ (n + 1) · T n₊₁`, while
`I ^ (n + 1)` already dies at level `n`. Then for a finitely generated `I` the kernel of the
bottom projection is the extension of `I`.

The family `p` and the hypothesis `hp` identify the projections: passing them rather than using
`c.π.app` directly lets a caller state the conclusion about its own maps, whose domain is the
cone point rather than the value of the constant functor at `⟨0⟩`.

Both inclusions are used below. The easy one needs only `hzero` at level `0`; the substance is
the other, and the shape of the induction is described in this module's docstring. -/
theorem ker_eq_map_of_isLimit (hc : IsLimit c)
    (φ : ∀ n : ℕ, R →+* (T.obj ⟨n⟩ : Type u))
    (p : ∀ n : ℕ, (c.pt : Type u) →+* (T.obj ⟨n⟩ : Type u))
    (Φ : R →+* (c.pt : Type u))
    (hp : ∀ (n : ℕ) (z : (c.pt : Type u)), p n z = (c.π.app ⟨n⟩).hom z)
    (hΦ : ∀ n, (p n).comp Φ = φ n)
    (hsurj : ∀ n, Function.Surjective (T.map (homOfLE (Nat.le_succ n)).op).hom)
    (hker : ∀ n, RingHom.ker (T.map (homOfLE (Nat.le_succ n)).op).hom
      = Ideal.map (φ (n + 1)) (I ^ (n + 1)))
    (hzero : ∀ n, Ideal.map (φ n) (I ^ (n + 1)) = ⊥)
    (hI : I.FG) :
    RingHom.ker (p 0) = Ideal.map Φ I := by
  classical
  obtain ⟨s, hs⟩ := hI
  have hπ : ∀ (n : ℕ) (z : (c.pt : Type u)),
      (T.map (homOfLE (Nat.le_succ n)).op).hom (p (n + 1) z) = p n z := by
    intro n z
    have h := congrArg CommRingCat.Hom.hom (c.w (homOfLE (Nat.le_succ n)).op)
    rw [CommRingCat.hom_comp] at h
    rw [hp, hp]
    exact DFunLike.congr_fun h z
  have hstep : ∀ (n : ℕ) (x : R),
      (T.map (homOfLE (Nat.le_succ n)).op).hom (φ (n + 1) x) = φ n x := by
    intro n x
    rw [← DFunLike.congr_fun (hΦ (n + 1)) x, ← DFunLike.congr_fun (hΦ n) x]
    exact hπ n (Φ x)
  have hcomp : ∀ n : ℕ,
      ((T.map (homOfLE (Nat.le_succ n)).op).hom).comp (φ (n + 1)) = φ n :=
    fun n => RingHom.ext (hstep n)
  refine le_antisymm ?_ ?_
  · intro b hb
    have hb0 : p 0 b = 0 := RingHom.mem_ker.mp hb
    have hstepex : ∀ (n : ℕ) (a : R → (T.obj ⟨n⟩ : Type u)),
        p n b = ∑ x ∈ s, φ n x * a x →
        ∃ a' : R → (T.obj ⟨n + 1⟩ : Type u),
          (p (n + 1) b = ∑ x ∈ s, φ (n + 1) x * a' x) ∧
            ∀ x, (T.map (homOfLE (Nat.le_succ n)).op).hom (a' x) - a x
              ∈ Ideal.map (φ n) (I ^ n) := by
      intro n a ha
      choose lift hlift using fun x => hsurj n (a x)
      have hd0 : (T.map (homOfLE (Nat.le_succ n)).op).hom
          (p (n + 1) b - ∑ x ∈ s, φ (n + 1) x * lift x) = 0 := by
        rw [map_sub, map_sum, hπ n b, ha]
        simp only [map_mul, hstep, hlift, sub_self]
      have hdmem : p (n + 1) b - ∑ x ∈ s, φ (n + 1) x * lift x
          ∈ Ideal.map (φ (n + 1)) (I ^ (n + 1)) := by
        rw [← hker n]
        exact RingHom.mem_ker.mpr hd0
      have hspan : I ^ (n + 1) = Ideal.span (s : Set R) * I ^ n := by
        rw [← hs, pow_succ']
      obtain ⟨e, he, hde⟩ := Ideal.exists_sum_of_mem_map_span_mul (φ (n + 1)) s (I ^ n)
        (by rwa [← hspan])
      refine ⟨fun x => lift x + e x, ?_, fun x => ?_⟩
      · have hsplit : ∑ x ∈ s, φ (n + 1) x * (lift x + e x)
            = ∑ x ∈ s, φ (n + 1) x * lift x + ∑ x ∈ s, φ (n + 1) x * e x := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun z _ => by ring
        rw [hsplit, ← hde]
        ring
      · have hqe : (T.map (homOfLE (Nat.le_succ n)).op).hom (e x)
            ∈ Ideal.map (φ n) (I ^ n) := by
          have hmm := Ideal.mem_map_of_mem (T.map (homOfLE (Nat.le_succ n)).op).hom (he x)
          rwa [Ideal.map_map, hcomp n] at hmm
        have hrw : (T.map (homOfLE (Nat.le_succ n)).op).hom (lift x + e x) - a x
            = (T.map (homOfLE (Nat.le_succ n)).op).hom (e x) := by
          rw [map_add, hlift]
          ring
        rw [hrw]
        exact hqe
    have hbase : p 0 b = ∑ x ∈ s, φ 0 x * (0 : (T.obj (⟨0⟩ : ℕᵒᵖ) : Type u)) := by
      simp [hb0]
    let A : ∀ n : ℕ, { a : R → (T.obj ⟨n⟩ : Type u) //
        p n b = ∑ x ∈ s, φ n x * a x } := fun n =>
      Nat.rec ⟨fun _ => 0, hbase⟩
        (fun n ih => ⟨(hstepex n ih.1 ih.2).choose, (hstepex n ih.1 ih.2).choose_spec.1⟩) n
    have hA2 : ∀ (n : ℕ) (x : R),
        (T.map (homOfLE (Nat.le_succ n)).op).hom ((A (n + 1)).1 x) - (A n).1 x
          ∈ Ideal.map (φ n) (I ^ n) :=
      fun n x => (hstepex n (A n).1 (A n).2).choose_spec.2 x
    have hstab : ∀ (m : ℕ) (x : R),
        (T.map (homOfLE (Nat.le_succ m)).op).hom
            ((T.map (homOfLE (Nat.le_succ (m + 1))).op).hom ((A (m + 2)).1 x))
          = (T.map (homOfLE (Nat.le_succ m)).op).hom ((A (m + 1)).1 x) := by
      intro m x
      have h2 := Ideal.mem_map_of_mem (T.map (homOfLE (Nat.le_succ m)).op).hom (hA2 (m + 1) x)
      rw [Ideal.map_map, hcomp m, hzero m] at h2
      have h3 := Ideal.mem_bot.mp h2
      rw [map_sub] at h3
      exact sub_eq_zero.mp h3
    have hex : ∀ x : R, ∃ z : (c.pt : Type u), ∀ m : ℕ,
        p m z = (T.map (homOfLE (Nat.le_succ m)).op).hom ((A (m + 1)).1 x) := by
      intro x
      obtain ⟨z, hz⟩ := exists_forall_π_app_eq_of_step hc
        (fun m => (T.map (homOfLE (Nat.le_succ m)).op).hom ((A (m + 1)).1 x))
        (fun m => hstab m x)
      exact ⟨z, fun m => by rw [hp]; exact hz m⟩
    choose z hz using hex
    have hbsum : b = ∑ x ∈ s, Φ x * z x := by
      refine Concrete.isLimit_ext T hc _ _ ?_
      rintro ⟨m⟩
      change (c.π.app ⟨m⟩).hom b = (c.π.app ⟨m⟩).hom _
      rw [← hp, ← hp, ← hπ m b, (A (m + 1)).2, map_sum, map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_mul, map_mul, hstep, hz x m]
      congr 1
      rw [← hΦ m, RingHom.comp_apply]
    rw [hbsum]
    refine Ideal.sum_mem _ fun x hx => ?_
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem Φ (hs ▸ Ideal.subset_span hx))
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    have hmem : φ 0 x ∈ Ideal.map (φ 0) (I ^ (0 + 1)) :=
      Ideal.mem_map_of_mem _ (by simpa using hx)
    rw [hzero 0] at hmem
    have hpx : p 0 (Φ x) = φ 0 x := by rw [← hΦ 0, RingHom.comp_apply]
    simp only [Ideal.mem_comap, RingHom.mem_ker, hpx]
    exact Ideal.mem_bot.mp hmem

end TowerKernel

end CategoryTheory.Limits

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable (U : Opens (FormalSpectrum I))

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The canonical map `R →+* Γ (U, thickeningSheaf I n)` is compatible with the transition
maps of the tower of sections. -/
theorem stepSheafHom_app_thickeningSectionsMk (n : ℕ) (x : R) :
    ((stepSheafHom I n).hom.app (op U)).hom (thickeningSectionsMk I (n + 1) U x)
      = thickeningSectionsMk I n U x := by
  rw [stepSheafHom_hom_app]
  exact (comap_step_algebraMap I n U (Ideal.Quotient.mk (I ^ (n + 1 + 1)) x)).trans
    (congrArg (algebraMap (R ⧸ I ^ (n + 1)) ((thickeningSheaf I n).presheaf.obj (op U)))
      (Ideal.Quotient.factor_mk (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) x))

/-- The cone over the tower of sections with point `Γ (U, O_{Spf R})`, obtained from the limit
cone through `FormalSpectrum.sectionsLimitIso`. Its legs are the projections
`FormalSpectrum.sectionsPi`. -/
def sectionsCone : Cone (sectionsTower I U) :=
  (limit.cone (sectionsTower I U)).extend (sectionsLimitIso I (op U)).hom

/-- `FormalSpectrum.sectionsCone` is a limit cone. -/
def isLimitSectionsCone : IsLimit (sectionsCone I U) :=
  IsLimit.extendIso _ (limit.isLimit _)

theorem sectionsCone_π_app (n : ℕ) : (sectionsCone I U).π.app ⟨n⟩ = sectionsPi I n U := by
  change (sectionsLimitIso I (op U)).hom ≫ limit.π (sectionsTower I U) ⟨n⟩ = sectionsPi I n U
  exact sectionsLimitIso_hom_π I (op U) n

/-- The cone over the tower of sections with point `R`, whose legs are the canonical maps
`FormalSpectrum.thickeningSectionsMk`. -/
def sectionsMkCone : Cone (sectionsTower I U) where
  pt := CommRingCat.of R
  π := NatTrans.ofOpSequence
    (fun n => CommRingCat.ofHom (thickeningSectionsMk I n U))
    (fun n => by
      apply CommRingCat.hom_ext
      refine RingHom.ext fun x => ?_
      simp only [Functor.const_obj_map, CommRingCat.hom_comp, RingHom.coe_comp,
        Function.comp_apply, sectionsTower_map_succ]
      exact (stepSheafHom_app_thickeningSectionsMk I U n x).symm)

/-- **The canonical map `R →+* Γ (U, O_{Spf R})`**, induced by the maps
`FormalSpectrum.thickeningSectionsMk` into the levels of the tower of sections. -/
def sectionsMk : R →+* ((structureSheaf I).presheaf.obj (op U) : Type u) :=
  ((isLimitSectionsCone I U).lift (sectionsMkCone I U)).hom

theorem sectionsPi_comp_sectionsMk (n : ℕ) :
    ((sectionsPi I n U).hom).comp (sectionsMk I U) = thickeningSectionsMk I n U := by
  have h := congrArg CommRingCat.Hom.hom
    ((isLimitSectionsCone I U).fac (sectionsMkCone I U) ⟨n⟩)
  rw [CommRingCat.hom_comp, sectionsCone_π_app] at h
  exact h

variable {I U}

/-- **The kernel of the reduction map on sections is the extension of the ideal of definition.**
Over an open with affine thickenings and for a finitely generated `I`,
`ker (Γ (U, O_{Spf R}) ↠ Γ (U, thickeningSheaf I 0)) = I · Γ (U, O_{Spf R})`. -/
theorem ker_sectionsPi_zero (hU : HasAffineThickenings I U) (hI : I.FG) :
    RingHom.ker (sectionsPi I 0 U).hom = Ideal.map (sectionsMk I U) I := by
  have hp : ∀ (n : ℕ) (z : ((sectionsCone I U).pt : Type u)),
      (sectionsPi I n U).hom z = ((sectionsCone I U).π.app ⟨n⟩).hom z := fun n z =>
    (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (sectionsCone_π_app I U n)) z).symm
  refine ker_eq_map_of_isLimit I (isLimitSectionsCone I U)
    (fun n => thickeningSectionsMk I n U) (fun n => (sectionsPi I n U).hom) (sectionsMk I U)
    hp (sectionsPi_comp_sectionsMk I U) ?_ ?_
    (fun n => map_thickeningSectionsMk_pow n U) hI
  · intro n
    rw [sectionsTower_map_succ]
    exact surjective_stepSheafHom_app hU n
  · intro n
    rw [sectionsTower_map_succ]
    exact ker_stepSheafHom_app hU n

/-- **The reduction of the sections ring is its quotient by the extended ideal of definition.** -/
def sectionsQuotientEquiv (hU : HasAffineThickenings I U) (hI : I.FG) :
    (((structureSheaf I).presheaf.obj (op U) : Type u) ⧸ Ideal.map (sectionsMk I U) I)
      ≃+* ((thickeningSheaf I 0).presheaf.obj (op U) : Type u) :=
  (Ideal.quotEquivOfEq (ker_sectionsPi_zero hU hI).symm).trans
    (RingHom.quotientKerEquivOfSurjective (surjective_sectionsPi_zero hU))

variable (I)

/-- **The canonical map is the expected one.** Under `FormalSpectrum.globalSectionsEquiv`, which
identifies the global sections of `O_{Spf R}` with `R`, the map `FormalSpectrum.sectionsMk` at the
top open is the identity of `R`. -/
theorem globalSectionsEquiv_sectionsMk_top (x : R) :
    globalSectionsEquiv I (sectionsMk I ⊤ x) = x := by
  have hhe : ∀ n : ℕ, (topLevelEquiv I n).toRingHom.comp
      ((sectionsTower I ⊤).map (homOfLE (Nat.le_add_right n 1)).op).hom =
        (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))).comp
          (topLevelEquiv I (n + 1)).toRingHom := fun n => by
    rw [sectionsTower_map_succ]
    exact topLevelEquiv_step I n
  have hcompl : globalSectionsEquivCompletion I (sectionsMk I ⊤ x) = AdicCompletion.of I R x := by
    refine AdicCompletion.ext_evalₐ fun n => ?_
    cases n with
    | zero =>
      have hsub : Subsingleton (R ⧸ I ^ 0) := by
        rw [pow_zero]
        exact Ideal.Quotient.subsingleton_iff.mpr Ideal.one_eq_top
      exact Subsingleton.elim _ _
    | succ n =>
      rw [AdicCompletion.evalₐ_of]
      change AdicCompletion.evalₐ I (n + 1) (AdicCompletion.towerLimitRingEquiv I
        (sectionsTower I ⊤) (topLevelEquiv I) hhe _) = _
      rw [AdicCompletion.evalₐ_towerLimitRingEquiv, AdicCompletion.towerProj_apply]
      have hval : (limit.π (sectionsTower I ⊤) ⟨n⟩).hom
          ((sectionsLimitIso I (op (⊤ : Opens (FormalSpectrum I)))).hom.hom
            (sectionsMk I ⊤ x)) = thickeningSectionsMk I n ⊤ x := by
        have h1 := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
          (sectionsLimitIso_hom_π I (op (⊤ : Opens (FormalSpectrum I))) n)) (sectionsMk I ⊤ x)
        rw [CommRingCat.hom_comp, RingHom.comp_apply] at h1
        have h2 : (limit.π (sectionsTower I ⊤) ⟨n⟩).hom
            ((sectionsLimitIso I (op (⊤ : Opens (FormalSpectrum I)))).hom.hom
              (sectionsMk I ⊤ x)) = (sectionsPi I n ⊤).hom (sectionsMk I ⊤ x) := h1
        rw [h2, ← sectionsPi_comp_sectionsMk I ⊤ n, RingHom.comp_apply]
      change topLevelEquiv I n ((limit.π (sectionsTower I ⊤) ⟨n⟩).hom
          ((sectionsLimitIso I (op (⊤ : Opens (FormalSpectrum I)))).hom.hom
            (sectionsMk I ⊤ x))) = Ideal.Quotient.mk (I ^ (n + 1)) x
      rw [hval]
      exact topLevelEquiv_algebraMap I n (Ideal.Quotient.mk (I ^ (n + 1)) x)
  change (AdicCompletion.ofAlgEquiv I).symm (globalSectionsEquivCompletion I (sectionsMk I ⊤ x)) = x
  rw [hcompl, AdicCompletion.ofAlgEquiv_symm_of]

/-- **Unconditional instance at the top open.** -/
theorem ker_sectionsPi_zero_top (hI : I.FG) :
    RingHom.ker (sectionsPi I 0 ⊤).hom = Ideal.map (sectionsMk I ⊤) I :=
  ker_sectionsPi_zero (hasAffineThickenings_top I) hI

/-- **Unconditional instance on a basic open.** -/
theorem ker_sectionsPi_zero_basicOpen (f : R) (hI : I.FG) :
    RingHom.ker (sectionsPi I 0 (basicOpen I f)).hom
      = Ideal.map (sectionsMk I (basicOpen I f)) I :=
  ker_sectionsPi_zero (hasAffineThickenings_basicOpen I f) hI

/-!
### `sectionsMk` is the structural map this tree already has

`FormalSpectrum.sectionsOpenHom` (`FormalSchemes.AdicOnOpenSections`) is the same map, presented
as a restriction from `⊤` rather than as a limit lift. Both are pinned by the projections
`FormalSpectrum.sectionsPi`, so the limit's uniqueness identifies them, and the identification is
what lets the limit step be stated in `FormalSpectrum.sectionsOpenIdeal` — the ideal of definition
of `Γ (U, O_{Spf R})` that the adicity results downstream are phrased in.
-/

/-- **`FormalSpectrum.sectionsPi` is natural in the open**, being a component of a limit
projection between two sheaves. -/
theorem sectionsPi_naturality (n : ℕ) {U V : Opens (FormalSpectrum I)} (h : U ≤ V) :
    (structureSheaf I).presheaf.map (homOfLE h).op ≫ sectionsPi I n U
      = sectionsPi I n V ≫ (thickeningSheaf I n).presheaf.map (homOfLE h).op :=
  (limit.π (structureSheafFunctor I) ⟨n⟩).hom.naturality (homOfLE h).op

omit [TopologicalSpace R] [IsAdicRing I] in
/-- Restriction carries the canonical map into a level to the canonical map into that level: both
are the `R ⧸ I ^ (n + 1)`-algebra map of a structure sheaf, and restriction is an algebra map. -/
theorem restrict_thickeningSectionsMk (n : ℕ) {U V : Opens (FormalSpectrum I)} (h : U ≤ V)
    (x : R) :
    ((thickeningSheaf I n).presheaf.map (homOfLE h).op).hom (thickeningSectionsMk I n V x)
      = thickeningSectionsMk I n U x :=
  rfl

/-- **The `⊤` case**: `FormalSpectrum.globalSectionsEquiv_sectionsMk_top` read as an equation of
maps rather than pointwise, the restriction along `⊤ ⊆ ⊤` being the identity. -/
theorem sectionsMk_top_eq : sectionsMk I ⊤ = sectionsOpenHom I ⊤ := by
  refine RingHom.ext fun x => ?_
  rw [sectionsOpenHom]
  have hid : (homOfLE (le_top (a := (⊤ : Opens (FormalSpectrum I))))).op = 𝟙 _ :=
    Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  simp only [hid, CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_apply,
    RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  exact (((globalSectionsEquiv I).symm_apply_eq).mpr
    (globalSectionsEquiv_sectionsMk_top I x).symm).symm

/-- **`FormalSpectrum.sectionsOpenHom` satisfies the characterisation that pins
`FormalSpectrum.sectionsMk`.** Naturality of `FormalSpectrum.sectionsPi` moves the question to
`⊤`, where it is `FormalSpectrum.sectionsMk_top_eq`. -/
theorem sectionsPi_comp_sectionsOpenHom (n : ℕ) (U : Opens (FormalSpectrum I)) :
    ((sectionsPi I n U).hom).comp (sectionsOpenHom I U) = thickeningSectionsMk I n U := by
  refine RingHom.ext fun x => ?_
  have hnat := congrArg CommRingCat.Hom.hom (sectionsPi_naturality I n (le_top (a := U)))
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp] at hnat
  have hgs : ((globalSectionsEquiv I).symm.toRingHom x) = sectionsMk I ⊤ x :=
    ((globalSectionsEquiv I).symm_apply_eq).mpr (globalSectionsEquiv_sectionsMk_top I x).symm
  have hx : sectionsOpenHom I U x
      = ((structureSheaf I).presheaf.map (homOfLE (le_top (a := U))).op).hom
          (sectionsMk I ⊤ x) := by
    rw [← hgs]; rfl
  have htop := DFunLike.congr_fun (sectionsPi_comp_sectionsMk I ⊤ n) x
  rw [RingHom.comp_apply] at htop
  rw [RingHom.comp_apply, hx, ← RingHom.comp_apply, hnat, RingHom.comp_apply, htop]
  exact restrict_thickeningSectionsMk I n (le_top (a := U)) x

/-- **The map this file builds is the one the tree already had.** A cone over the tower of
sections with point `R` has exactly one map to the limit, and
`FormalSpectrum.sectionsPi_comp_sectionsOpenHom` says `FormalSpectrum.sectionsOpenHom` is such a
map. This is the arbitrary-open twin of `FormalSpectrum.sectionsOpenHom_basicOpen`. -/
theorem sectionsMk_eq_sectionsOpenHom (U : Opens (FormalSpectrum I)) :
    sectionsMk I U = sectionsOpenHom I U := by
  have huniq := (isLimitSectionsCone I U).uniq (sectionsMkCone I U)
    (CommRingCat.ofHom (sectionsOpenHom I U)) ?_
  · exact congrArg CommRingCat.Hom.hom huniq.symm
  · rintro ⟨n⟩
    apply CommRingCat.hom_ext
    rw [CommRingCat.hom_comp, sectionsCone_π_app]
    exact sectionsPi_comp_sectionsOpenHom I n U

/-- **The limit step in the tree's own spelling.** `FormalSpectrum.sectionsOpenIdeal` is the ideal
of definition of `Γ (U, O_{Spf R})` that `FormalSchemes.AdicOnOpenSections` and its consumers use;
over an open with affine thickenings it is exactly the kernel of the reduction map. -/
theorem ker_sectionsPi_zero_eq_sectionsOpenIdeal {U : Opens (FormalSpectrum I)}
    (hU : HasAffineThickenings I U) (hI : I.FG) :
    RingHom.ker (sectionsPi I 0 U).hom = sectionsOpenIdeal I U := by
  rw [ker_sectionsPi_zero hU hI, sectionsMk_eq_sectionsOpenHom I U, sectionsOpenIdeal]

end FormalSpectrum
