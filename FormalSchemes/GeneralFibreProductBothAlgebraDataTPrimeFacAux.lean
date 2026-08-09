import FormalSchemes.GeneralFibreProductBothAlgebraDataTPrime

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.style.openClassical false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Away-completion compatibility lemmas for the mixed `bothAlgDataT'_fac` leaves

The twelve mixed-shape leaves of `bothAlgDataT'_fac` reduce, per tensor factor, to algebra
identities involving the self-multiply expand isomorphism
`FormalSpectrum.awayCompletionSelfMulEquiv`, the further-localization embeds `furtherLocFst`/
`furtherLocSnd`, the element-congruence `awayCongrElt*`, and the index transport `awayIdxTrans*`.

This file collects the genuinely new reusable algebra content those closers need: the
*self-multiply bridge* identifying `furtherLocFst I g g` (resp. `furtherLocSnd I g g`) with the
self-multiply isomorphism, and the index-transport compatibility of `awayIdxTrans*` with the
structure map `IsScalarTower.toAlgHom`.

All away-completion maps are `AdicCompletion.mapCompletion` of `Localization.Away` ring maps, so the
bridge is proved by identifying the underlying localization maps via
`IsLocalization.ringHom_ext (Submonoid.powers g)` and then lifting through the completion functor.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum CompletedTensorProduct
open CompletedTensorAwayInterchange

universe u

namespace AlgebraicGeometry

open scoped Classical

/-! ### The self-multiply bridge (single-ring statement) -/

section SelfMulBridge

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {A : Type u} [CommRing A] [Algebra R A]

/-- The localization map `awayToAwayRight g g : A_g → A_{g·g}` (invert `g` after `g`) is the
self-multiply localization identity `awaySelfMulLocEquiv g`. Both fix the image of `A`, so they
agree by the universal property of the localization `A_g`. -/
theorem awayToAwayRight_self_eq (g : A) :
    IsLocalization.Away.awayToAwayRight g g =
      (awaySelfMulLocEquiv g).toRingEquiv.toRingHom := by
  refine IsLocalization.ringHom_ext (Submonoid.powers g) ?_
  ext a
  rw [RingHom.comp_apply, RingHom.comp_apply, IsLocalization.Away.awayToAwayRight_eq]
  have h := RingHom.congr_fun (awaySelfMulLocEquiv_comp_algebraMap g) a
  rw [RingHom.comp_apply] at h
  rw [h]

/-- The localization map `awayToAwayLeft g g : A_g → A_{g·g}` (invert `g` after `g`) is the
self-multiply localization identity `awaySelfMulLocEquiv g`. -/
theorem awayToAwayLeft_self_eq (g : A) :
    IsLocalization.Away.awayToAwayLeft g g =
      (awaySelfMulLocEquiv g).toRingEquiv.toRingHom := by
  refine IsLocalization.ringHom_ext (Submonoid.powers g) ?_
  ext a
  rw [RingHom.comp_apply, RingHom.comp_apply, IsLocalization.Away.awayToAwayLeft_eq]
  have h := RingHom.congr_fun (awaySelfMulLocEquiv_comp_algebraMap g) a
  rw [RingHom.comp_apply] at h
  rw [h]

/-- The completed further-localization `A{1/g} →ₐ[R] A{1/g·g}` of any localization map equal to the
self-multiply localization identity is the self-multiply expand isomorphism (as an algebra map).
Both underlying ring maps are `AdicCompletion.mapCompletion` of the *same* localization map after
`subst`; the propositional witnesses are irrelevant. -/
theorem furtherLocAlgHom_self (g : A)
    (ρ : Localization.Away g →+* Localization.Away (g * g))
    (hρ : ρ.comp (algebraMap A (Localization.Away g)) = algebraMap A (Localization.Away (g * g)))
    (hI : I.FG)
    (hρeq : ρ = (awaySelfMulLocEquiv g).toRingEquiv.toRingHom) :
    furtherLocAlgHom I g (g * g) hI ρ hρ =
      (awayCompletionSelfMulEquiv (I.map (algebraMap R A)) g (hI.map _)).toAlgHom := by
  subst hρeq
  apply AlgHom.coe_ringHom_injective
  rfl

/-- **Self-multiply bridge (first embed).** `furtherLocFst I g g = awayCompletionSelfMulEquiv g`. -/
theorem furtherLocFst_self (g : A) (hI : I.FG) :
    furtherLocFst I g g hI =
      (awayCompletionSelfMulEquiv (I.map (algebraMap R A)) g (hI.map _)).toAlgHom :=
  furtherLocAlgHom_self g (IsLocalization.Away.awayToAwayRight g g) _ hI
    (awayToAwayRight_self_eq g)

/-- **Self-multiply bridge (second embed).** `furtherLocSnd I g g = awayCompletionSelfMulEquiv`. -/
theorem furtherLocSnd_self (g : A) (hI : I.FG) :
    furtherLocSnd I g g hI =
      (awayCompletionSelfMulEquiv (I.map (algebraMap R A)) g (hI.map _)).toAlgHom :=
  furtherLocAlgHom_self g (IsLocalization.Away.awayToAwayLeft g g) _ hI
    (awayToAwayLeft_self_eq g)

/-- The composite `e⁻¹ ∘ e` of an algebra equivalence, as algebra maps, is the identity. -/
theorem algEquiv_symm_toAlgHom_comp_toAlgHom {A₀ B₀ : Type u} [CommRing A₀] [CommRing B₀]
    [Algebra R A₀] [Algebra R B₀] (e : A₀ ≃ₐ[R] B₀) :
    e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id R A₀ := by
  refine AlgHom.ext fun z => ?_
  simp

/-- `(T ≪≫ W)⁻¹ ∘ W = T⁻¹` on algebra maps: the right factor `W` of a composite equivalence cancels
against its inverse. -/
theorem trans_symm_comp_toAlgHom {X Y Z : Type u} [CommRing X] [CommRing Y] [CommRing Z]
    [Algebra R X] [Algebra R Y] [Algebra R Z] (T : X ≃ₐ[R] Y) (W : Y ≃ₐ[R] Z) :
    (T.trans W).symm.toAlgHom.comp W.toAlgHom = T.symm.toAlgHom := by
  refine AlgHom.ext fun z => ?_
  simp

/-- `W ∘ (W ≪≫ T)⁻¹ = T⁻¹` on algebra maps: the left factor `W` of a composite equivalence cancels
against its inverse (mirror used by the self-multiply *expand* closers). -/
theorem trans_symm_comp_symm_toAlgHom {X Y Z : Type u} [CommRing X] [CommRing Y] [CommRing Z]
    [Algebra R X] [Algebra R Y] [Algebra R Z] (W : X ≃ₐ[R] Y) (T : Y ≃ₐ[R] Z) :
    W.toAlgHom.comp (W.trans T).symm.toAlgHom = T.symm.toAlgHom := by
  refine AlgHom.ext fun z => ?_
  simp

end SelfMulBridge

/-! ### Self-multiply collapse/expand of a triple composite

The mixed leaves feed a factor `τ.trans (S.trans C)` (resp. `C.trans (S.trans τ)`) whose inverse is
composed against a `furtherLoc` embed; after the two inner atoms cancel the embed to the identity,
only the genuine transition `τ` survives. These two lemmas package that peeling once and for all. -/

section TransCollapse

variable {R : Type u} [CommRing R]

/-- Inverse-of-composite on algebra maps: `(e ≪≫ f).symm = e.symm ∘ f.symm`. -/
theorem trans_symm_toAlgHom {X Y Z : Type u} [CommRing X] [CommRing Y] [CommRing Z]
    [Algebra R X] [Algebra R Y] [Algebra R Z] (e : X ≃ₐ[R] Y) (f : Y ≃ₐ[R] Z) :
    (e.trans f).symm.toAlgHom = e.symm.toAlgHom.comp f.symm.toAlgHom := by
  refine AlgHom.ext fun z => ?_
  simp [AlgEquiv.symm_trans_apply]

/-- **Self-multiply collapse.** If the two inner factors `S`, `C` cancel the embed `bT` to the
identity, then `(τ.trans (S.trans C)).symm ∘ bT = τ.symm` (on algebra maps). -/
theorem trans_selfMul_symm_comp {P Q V W : Type u} [CommRing P] [CommRing Q] [CommRing V]
    [CommRing W] [Algebra R P] [Algebra R Q] [Algebra R V] [Algebra R W]
    (τ : P ≃ₐ[R] Q) (S : Q ≃ₐ[R] V) (C : V ≃ₐ[R] W) (bT : Q →ₐ[R] W)
    (h : S.symm.toAlgHom.comp (C.symm.toAlgHom.comp bT) = AlgHom.id R Q) :
    (τ.trans (S.trans C)).symm.toAlgHom.comp bT = τ.symm.toAlgHom := by
  have key : (τ.trans (S.trans C)).symm.toAlgHom =
      τ.symm.toAlgHom.comp (S.symm.toAlgHom.comp C.symm.toAlgHom) := by
    refine AlgHom.ext fun z => ?_
    simp [AlgEquiv.symm_trans_apply]
  rw [key, AlgHom.comp_assoc, AlgHom.comp_assoc, h, AlgHom.comp_id]

/-- **Self-multiply expand.** For the target-side shape `C.trans (S.symm.trans τ)`, its inverse
(as an algebra map) is `bS ∘ τ.symm`, where `bS = C.symm ∘ S` is the freshly-created embed. -/
theorem trans_expand_symm_toAlgHom {P Q V W : Type u} [CommRing P] [CommRing Q] [CommRing V]
    [CommRing W] [Algebra R P] [Algebra R Q] [Algebra R V] [Algebra R W]
    (C : P ≃ₐ[R] Q) (S : V ≃ₐ[R] Q) (τ : V ≃ₐ[R] W) (bS : V →ₐ[R] P)
    (h : C.symm.toAlgHom.comp S.toAlgHom = bS) :
    (C.trans (S.symm.trans τ)).symm.toAlgHom = bS.comp τ.symm.toAlgHom := by
  have key : (C.trans (S.symm.trans τ)).symm.toAlgHom =
      (C.symm.toAlgHom.comp S.toAlgHom).comp τ.symm.toAlgHom := by
    refine AlgHom.ext fun z => ?_
    simp [AlgEquiv.symm_trans_apply]
  rw [key, h]

end TransCollapse

/-! ### `mapSpf` argument congruence -/

section MapSpfCongr

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
variable [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra R B']

/-- Congruence of `mapSpf` in its two algebra-map arguments. -/
theorem mapSpf_congr (hI : I.FG) {f f' : A →ₐ[R] A'} {g g' : B →ₐ[R] B'}
    (hf : f = f') (hg : g = g') :
    haveI := isAdicRing R I A B hI
    haveI := isAdicRing R I A' B' hI
    CompletedTensorProduct.mapSpf hI f g = CompletedTensorProduct.mapSpf hI f' g' := by
  rw [hf, hg]

end MapSpfCongr

/-! ### Index-transport compatibility with the structure map -/

section IdxTrans

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {JX JY : Type u}
variable {A : JX → Type u} {B : JY → Type u}
variable [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]

/-- **Index-transport compatibility (`A` factor).** The index transport `awayIdxTransA` intertwines
the structure maps `IsScalarTower.toAlgHom` along the shared-coordinate transport `eqAlgEquivA`. -/
theorem awayIdxTransA_scalarTower_compat {i i' : JX} (h : i = i') (g : ∀ x : JX, A x) :
    (awayIdxTransA (I := I) h g).symm.toAlgHom.comp
        (IsScalarTower.toAlgHom R (A i')
          (awayCompletion (I.map (algebraMap R (A i'))) (g i'))) =
      (IsScalarTower.toAlgHom R (A i)
          (awayCompletion (I.map (algebraMap R (A i))) (g i))).comp
        (eqAlgEquivA (R := R) h).symm.toAlgHom := by
  subst h; rfl

/-- **Index-transport compatibility (`B` factor).** -/
theorem awayIdxTransB_scalarTower_compat {j j' : JY} (h : j = j') (g : ∀ y : JY, B y) :
    (awayIdxTransB (I := I) h g).symm.toAlgHom.comp
        (IsScalarTower.toAlgHom R (B j')
          (awayCompletion (I.map (algebraMap R (B j'))) (g j'))) =
      (IsScalarTower.toAlgHom R (B j)
          (awayCompletion (I.map (algebraMap R (B j))) (g j))).comp
        (eqAlgEquivB (R := R) h).symm.toAlgHom := by
  subst h; rfl

/-! #### Self-multiply collapse atoms (family)

`awayCongrElt*` transports a `furtherLoc*` embed back to the repeated-element case, and there the
`awaySelfMul*` isomorphism cancels it (self-multiply bridge). -/

theorem awayCongrEltA_symm_comp_furtherLocFst {i : JX} (s s' : A i) (heq : s * s = s * s')
    (hss : s' = s) (hI : I.FG) :
    (awayCongrEltA heq).symm.toAlgHom.comp (furtherLocFst I s s' hI) =
      furtherLocFst I s s hI := by
  subst hss; rfl

theorem awayCongrEltB_symm_comp_furtherLocFst {j : JY} (s s' : B j) (heq : s * s = s * s')
    (hss : s' = s) (hI : I.FG) :
    (awayCongrEltB heq).symm.toAlgHom.comp (furtherLocFst I s s' hI) =
      furtherLocFst I s s hI := by
  subst hss; rfl

theorem awaySelfMulA_symm_comp_furtherLocFst_self {i : JX} (s : A i) (hI : I.FG) :
    (awaySelfMulA hI s).symm.toAlgHom.comp (furtherLocFst I s s hI) =
      AlgHom.id R (awayCompletion (I.map (algebraMap R (A i))) s) := by
  rw [furtherLocFst_self]
  exact algEquiv_symm_toAlgHom_comp_toAlgHom _

theorem awaySelfMulB_symm_comp_furtherLocFst_self {j : JY} (s : B j) (hI : I.FG) :
    (awaySelfMulB hI s).symm.toAlgHom.comp (furtherLocFst I s s hI) =
      AlgHom.id R (awayCompletion (I.map (algebraMap R (B j))) s) := by
  rw [furtherLocFst_self]
  exact algEquiv_symm_toAlgHom_comp_toAlgHom _

/-! #### Self-multiply *expand* atoms (family)

The mirror of the collapse atoms: the self-multiply isomorphism `awaySelfMul*` composed (after an
element congruence) *creates* the further-localization embed to a distinct element. -/

theorem awayCongrEltA_symm_comp_awaySelfMulA {i : JX} (s s' : A i) (heq : s * s' = s * s)
    (hss : s' = s) (hI : I.FG) :
    (awayCongrEltA heq).symm.toAlgHom.comp (awaySelfMulA hI s).toAlgHom =
      furtherLocFst I s s' hI := by
  subst hss
  rw [furtherLocFst_self]
  rfl

theorem awayCongrEltB_symm_comp_awaySelfMulB {j : JY} (s s' : B j) (heq : s * s' = s * s)
    (hss : s' = s) (hI : I.FG) :
    (awayCongrEltB heq).symm.toAlgHom.comp (awaySelfMulB hI s).toAlgHom =
      furtherLocFst I s s' hI := by
  subst hss
  rw [furtherLocFst_self]
  rfl

/-! #### `furtherLocSnd` variants of the collapse/expand atoms

The same atoms with `furtherLocSnd` in place of `furtherLocFst` (needed when the target leg is the
`snd`-based embed). `furtherLocSnd I s s = awaySelfMul` on the diagonal, so the self-multiply
cancellations are identical after `furtherLocSnd_self`. -/

theorem awayCongrEltA_symm_comp_furtherLocSnd {i : JX} (s s' : A i) (heq : s * s = s' * s)
    (hss : s' = s) (hI : I.FG) :
    (awayCongrEltA heq).symm.toAlgHom.comp (furtherLocSnd I s' s hI) =
      furtherLocSnd I s s hI := by
  subst hss; rfl

theorem awayCongrEltB_symm_comp_furtherLocSnd {j : JY} (s s' : B j) (heq : s * s = s' * s)
    (hss : s' = s) (hI : I.FG) :
    (awayCongrEltB heq).symm.toAlgHom.comp (furtherLocSnd I s' s hI) =
      furtherLocSnd I s s hI := by
  subst hss; rfl

theorem awaySelfMulA_symm_comp_furtherLocSnd_self {i : JX} (s : A i) (hI : I.FG) :
    (awaySelfMulA hI s).symm.toAlgHom.comp (furtherLocSnd I s s hI) =
      AlgHom.id R (awayCompletion (I.map (algebraMap R (A i))) s) := by
  rw [furtherLocSnd_self]
  exact algEquiv_symm_toAlgHom_comp_toAlgHom _

theorem awaySelfMulB_symm_comp_furtherLocSnd_self {j : JY} (s : B j) (hI : I.FG) :
    (awaySelfMulB hI s).symm.toAlgHom.comp (furtherLocSnd I s s hI) =
      AlgHom.id R (awayCompletion (I.map (algebraMap R (B j))) s) := by
  rw [furtherLocSnd_self]
  exact algEquiv_symm_toAlgHom_comp_toAlgHom _

theorem awayCongrEltA_symm_comp_awaySelfMulA_snd {i : JX} (s s' : A i) (heq : s' * s = s * s)
    (hss : s' = s) (hI : I.FG) :
    (awayCongrEltA heq).symm.toAlgHom.comp (awaySelfMulA hI s).toAlgHom =
      furtherLocSnd I s' s hI := by
  subst hss
  rw [furtherLocSnd_self]
  rfl

theorem awayCongrEltB_symm_comp_awaySelfMulB_snd {j : JY} (s s' : B j) (heq : s' * s = s * s)
    (hss : s' = s) (hI : I.FG) :
    (awayCongrEltB heq).symm.toAlgHom.comp (awaySelfMulB hI s).toAlgHom =
      furtherLocSnd I s' s hI := by
  subst hss
  rw [furtherLocSnd_self]
  rfl

end IdxTrans

/-! ### The further-localization swap via `mul_comm`

For the genuine-σ mixed leaves whose target leg reorders the away element (via
`awayCongrElt (mul_comm …)` in the `bothAlgDataT'` definition), the inverse element-congruence turns
`furtherLocFst I a b` into `furtherLocSnd I b a`. Both underlying completion maps agree on the dense
image of `Localization.Away a` (they fix `algebraMap`), so they coincide by
`hom_ext_of_continuous`. -/

section MulCommSwap

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {JX JY : Type u}
variable {A : JX → Type u} {B : JY → Type u}
variable [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]

/-- Congruence of the away-completion of an arbitrary `R`-algebra `D` along an equality of the away
element. This is the base-ring-agnostic version of `awayCongrEltA`/`awayCongrEltB`; it is defined
identically (`subst h; exact AlgEquiv.refl`), so the family versions are definitional instances. -/
private def awayCongrGen {D : Type u} [CommRing D] [Algebra R D] {g g' : D} (h : g = g') :
    awayCompletion (I.map (algebraMap R D)) g ≃ₐ[R]
      awayCompletion (I.map (algebraMap R D)) g' := by
  subst h; exact AlgEquiv.refl

/-- The inverse congruence fixes the image of `D`: `(awayCongrGen h).symm (algebraMap D _ x) =
algebraMap D _ x` (both sides are the transported structural image, so it holds after `subst`). -/
private theorem awayCongrGen_symm_algebraMap {D : Type u} [CommRing D] [Algebra R D] {g g' : D}
    (h : g = g') (x : D) :
    (awayCongrGen (I := I) h).symm
        (algebraMap D (awayCompletion (I.map (algebraMap R D)) g') x) =
      algebraMap D (awayCompletion (I.map (algebraMap R D)) g) x := by
  subst h; rfl

/-- Continuity of the inverse congruence: it carries the powers of the ideal of definition on the
`g'` side into the powers on the `g` side (trivially so, being transport of the identity). -/
private theorem awayCongrGen_symm_mem_pow {D : Type u} [CommRing D] [Algebra R D] {g g' : D}
    (h : g = g') (m : ℕ) (x : awayCompletion (I.map (algebraMap R D)) g')
    (hx : x ∈ (awayCompletionIdeal (I.map (algebraMap R D)) g') ^ m) :
    (awayCongrGen (I := I) h).symm x ∈ (awayCompletionIdeal (I.map (algebraMap R D)) g) ^ m := by
  subst h; exact hx

/-- Continuity of `furtherLocFst` in filtration form. -/
private theorem furtherLocFst_mem_pow {D : Type u} [CommRing D] [Algebra R D] (g₁ g₂ : D)
    (hI : I.FG) (m : ℕ) {x : awayCompletion (I.map (algebraMap R D)) g₁}
    (hx : x ∈ (((I.map (algebraMap R D)).map (algebraMap D (Localization.Away g₁))) ^ m • ⊤ :
      Submodule (Localization.Away g₁) (awayCompletion (I.map (algebraMap R D)) g₁))) :
    furtherLocFst I g₁ g₂ hI x ∈
      (awayCompletionIdeal (I.map (algebraMap R D)) (g₁ * g₂)) ^ m :=
  AdicCompletion.mapCompletion_mem_pow (IsLocalization.Away.awayToAwayRight g₁ g₂)
    (le_of_eq (by
      rw [Ideal.map_map]
      congr 1
      exact RingHom.ext fun a => by
        rw [RingHom.comp_apply]
        exact IsLocalization.Away.awayToAwayRight_eq g₁ g₂ a))
    ((hI.map (algebraMap R D)).map (algebraMap D (Localization.Away (g₁ * g₂))))
    ((hI.map (algebraMap R D)).map (algebraMap D (Localization.Away g₁))) m hx

/-- Continuity of `furtherLocSnd` in filtration form. -/
private theorem furtherLocSnd_mem_pow {D : Type u} [CommRing D] [Algebra R D] (g₁ g₂ : D)
    (hI : I.FG) (m : ℕ) {x : awayCompletion (I.map (algebraMap R D)) g₂}
    (hx : x ∈ (((I.map (algebraMap R D)).map (algebraMap D (Localization.Away g₂))) ^ m • ⊤ :
      Submodule (Localization.Away g₂) (awayCompletion (I.map (algebraMap R D)) g₂))) :
    furtherLocSnd I g₁ g₂ hI x ∈
      (awayCompletionIdeal (I.map (algebraMap R D)) (g₁ * g₂)) ^ m :=
  AdicCompletion.mapCompletion_mem_pow (IsLocalization.Away.awayToAwayLeft g₂ g₁)
    (le_of_eq (by
      rw [Ideal.map_map]
      congr 1
      exact RingHom.ext fun a => by
        rw [RingHom.comp_apply]
        exact IsLocalization.Away.awayToAwayLeft_eq g₂ g₁ a))
    ((hI.map (algebraMap R D)).map (algebraMap D (Localization.Away (g₁ * g₂))))
    ((hI.map (algebraMap R D)).map (algebraMap D (Localization.Away g₂))) m hx

/-- **Generic further-localization swap via `mul_comm`.** The inverse of the element-congruence
`away(b·a) ≃ away(a·b)` composed with the first further localization `away(a) → away(a·b)` is the
second further localization `away(a) → away(b·a)`. -/
theorem awayCongr_mulComm_symm_comp_furtherLocFst_gen {D : Type u} [CommRing D] [Algebra R D]
    (a b : D) (hI : I.FG) :
    (awayCongrGen (I := I) (mul_comm b a)).symm.toAlgHom.comp (furtherLocFst I a b hI) =
      furtherLocSnd I b a hI := by
  haveI : IsAdicComplete
      (AdicCompletion.idealOfDefinition
        ((I.map (algebraMap R D)).map (algebraMap D (Localization.Away (b * a)))))
      (awayCompletion (I.map (algebraMap R D)) (b * a)) :=
    (AdicCompletion.isAdicRing_map _ ((hI.map (algebraMap R D)).map _)).toIsAdicComplete
  refine AlgHom.coe_ringHom_injective ?_
  refine AdicCompletion.hom_ext_of_continuous
    ((I.map (algebraMap R D)).map (algebraMap D (Localization.Away a)))
    (AdicCompletion.idealOfDefinition
      ((I.map (algebraMap R D)).map (algebraMap D (Localization.Away (b * a)))))
    ((hI.map (algebraMap R D)).map (algebraMap D (Localization.Away a)))
    (fun m x hx => ?_) (fun m x hx => ?_) (fun c => ?_)
  · exact awayCongrGen_symm_mem_pow (mul_comm b a) m _ (furtherLocFst_mem_pow a b hI m hx)
  · exact furtherLocSnd_mem_pow b a hI m hx
  · have hR :
        (↑((awayCongrGen (I := I) (mul_comm b a)).symm.toAlgHom.comp (furtherLocFst I a b hI)) :
            awayCompletion (I.map (algebraMap R D)) a →+*
              awayCompletion (I.map (algebraMap R D)) (b * a)).comp
          (algebraMap (Localization.Away a) (awayCompletion (I.map (algebraMap R D)) a)) =
        (↑(furtherLocSnd I b a hI) :
            awayCompletion (I.map (algebraMap R D)) a →+*
              awayCompletion (I.map (algebraMap R D)) (b * a)).comp
          (algebraMap (Localization.Away a) (awayCompletion (I.map (algebraMap R D)) a)) := by
      refine IsLocalization.ringHom_ext (Submonoid.powers a) ?_
      refine RingHom.ext fun c0 => ?_
      simp only [RingHom.comp_apply,
        ← IsScalarTower.algebraMap_apply D (Localization.Away a)
          (awayCompletion (I.map (algebraMap R D)) a),
        AlgHom.coe_toRingHom, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
        furtherLocFst_algebraMap, awayCongrGen_symm_algebraMap, furtherLocSnd_algebraMap]
    exact RingHom.congr_fun hR c

/-- **`A`-factor further-localization swap via `mul_comm`.** -/
theorem awayCongrEltA_mulComm_symm_comp_furtherLocFst {i : JX} (a b : A i) (hI : I.FG) :
    (awayCongrEltA (mul_comm b a)).symm.toAlgHom.comp (furtherLocFst I a b hI) =
      furtherLocSnd I b a hI :=
  awayCongr_mulComm_symm_comp_furtherLocFst_gen a b hI

/-- **`B`-factor further-localization swap via `mul_comm`.** -/
theorem awayCongrEltB_mulComm_symm_comp_furtherLocFst {j : JY} (a b : B j) (hI : I.FG) :
    (awayCongrEltB (mul_comm b a)).symm.toAlgHom.comp (furtherLocFst I a b hI) =
      furtherLocSnd I b a hI :=
  awayCongr_mulComm_symm_comp_furtherLocFst_gen a b hI

end MulCommSwap

end AlgebraicGeometry
