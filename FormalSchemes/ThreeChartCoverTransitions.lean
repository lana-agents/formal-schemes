import FormalSchemes.ThreeChartCoverCharts

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The transitions of the three-chart open cover

The `τ` and `σ` fields of the open-cover datum of `FormalSchemes.ThreeChartCoverDatum`, and their
three laws. Both families factor through the *common* completed localization downstairs on `A`:

```
τ i j :  A{1/f_i}{1/g_ij}  ←N—  A{1/(f_i f_j)}  —τ⁰→  A{1/(f_j f_i)}  —N→  A{1/f_j}{1/g_ji}
σ i j k : A{1/f_i}{1/(g_ij g_ik)} ←N— A{1/(f_i f_j · f_i f_k)} —σ⁰→ … —N→ A{1/f_j}{1/(g_jk g_ji)}
```

where `N` is the chart identification of `FormalSchemes.ThreeChartCoverCharts` and `τ⁰`, `σ⁰` are
594's comparison isomorphisms `ThreeChart.tau`, `ThreeChart.sigma` on `A` itself — the very same
maps, reused rather than rebuilt.

## The conjugation lemmas, and why they are stated abstractly

Each of the three laws is an instance of a general fact: *a transition datum conjugated by
isomorphisms that intertwine the two further-localization legs satisfies the laws as soon as the
original one does.* `tau_symm_conj`, `sigma_tau_conj` and `sigma_cocycle_conj` below say exactly
that, with the chart algebras `A₁ A₂ A₃` left as **variables**.

This is not stylistic. The chart algebras of an open cover are completed localizations, so the
chart-local double overlaps are *doubly nested* completions, and any proof step that makes the
kernel reduce one of them costs minutes and gigabytes (see the cost note in
`FormalSchemes.ThreeChartCoverCharts`). Proving the laws with `A₁ A₂ A₃` abstract keeps every such
step inside a small, cheap proof; the concrete instances below are then pure substitution.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open CompletedTensorAwayInterchange

universe u

namespace AlgebraicGeometry

namespace ThreeChartCover

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {A : Type u} [CommRing A] [Algebra R A]

/-! ### Conjugation of a transition datum -/

section Conjugation

variable {A₁ A₂ A₃ : Type u} [CommRing A₁] [CommRing A₂] [CommRing A₃]
variable [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]

/-- **Conjugation preserves `τ_symm`.** -/
theorem tau_symm_conj {u v : A} {a₁ : A₁} {b₂ : A₂}
    (τ₀ : awayCompletion (I.map (algebraMap R A)) u ≃ₐ[R]
      awayCompletion (I.map (algebraMap R A)) v)
    (N₁ : awayCompletion (I.map (algebraMap R A)) u ≃ₐ[R]
      awayCompletion (I.map (algebraMap R A₁)) a₁)
    (N₁' : awayCompletion (I.map (algebraMap R A)) v ≃ₐ[R]
      awayCompletion (I.map (algebraMap R A₂)) b₂) :
    N₁'.symm.trans (τ₀.symm.trans N₁) = (N₁.symm.trans (τ₀.trans N₁')).symm :=
  AlgEquiv.ext fun _ => rfl

/-- **Conjugation preserves the σ/τ restriction compatibility `hστ`**, provided the conjugating
isomorphisms intertwine the two further-localization legs (`hfst`, `hsnd`). -/
theorem sigma_tau_conj (hI : I.FG) {u u' v w : A} {a₁ b₁ : A₁} {a₂ b₂ : A₂}
    (τ₀ : awayCompletion (I.map (algebraMap R A)) u ≃ₐ[R]
      awayCompletion (I.map (algebraMap R A)) v)
    (σ₀ : awayCompletion (I.map (algebraMap R A)) (u * u') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R A)) (w * v))
    (N₁ : awayCompletion (I.map (algebraMap R A)) u ≃ₐ[R]
      awayCompletion (I.map (algebraMap R A₁)) a₁)
    (N₁' : awayCompletion (I.map (algebraMap R A)) v ≃ₐ[R]
      awayCompletion (I.map (algebraMap R A₂)) b₂)
    (N₂ : awayCompletion (I.map (algebraMap R A)) (u * u') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R A₁)) (a₁ * b₁))
    (N₂' : awayCompletion (I.map (algebraMap R A)) (w * v) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R A₂)) (a₂ * b₂))
    (h₁ : IsUnit (algebraMap A₁ (Localization.Away (a₁ * b₁)) a₁))
    (h₂ : IsUnit (algebraMap A₂ (Localization.Away (a₂ * b₂)) b₂))
    (h₃ : IsUnit (algebraMap A (Localization.Away (u * u')) u))
    (h₄ : IsUnit (algebraMap A (Localization.Away (w * v)) v))
    (hfst : ∀ x, awayCongrHom I a₁ (a₁ * b₁) hI h₁ (N₁ x) =
      N₂ (awayCongrHom I u (u * u') hI h₃ x))
    (hsnd : ∀ y, awayCongrHom I b₂ (a₂ * b₂) hI h₂ (N₁' y) =
      N₂' (awayCongrHom I v (w * v) hI h₄ y))
    (hlaw : ∀ y, σ₀.symm (furtherLocSnd I w v hI y) = furtherLocFst I u u' hI (τ₀.symm y)) :
    (N₂.symm.trans (σ₀.trans N₂')).symm.toAlgHom.comp (furtherLocSnd I a₂ b₂ hI) =
      (furtherLocFst I a₁ b₁ hI).comp (N₁.symm.trans (τ₀.trans N₁')).symm.toAlgHom := by
  rw [furtherLocFst_eq_awayCongrHom I a₁ b₁ hI h₁, furtherLocSnd_eq_awayCongrHom I a₂ b₂ hI h₂]
  refine AlgHom.ext fun x => ?_
  obtain ⟨y, rfl⟩ : ∃ y, N₁' y = x := ⟨_, N₁'.apply_symm_apply x⟩
  have hτ : (N₁.symm.trans (τ₀.trans N₁')).symm (N₁' y) = N₁ (τ₀.symm y) := by
    rw [AlgEquiv.symm_trans_apply, AlgEquiv.symm_trans_apply, AlgEquiv.symm_apply_apply,
      AlgEquiv.symm_symm]
  have hσ : ∀ z, (N₂.symm.trans (σ₀.trans N₂')).symm (N₂' z) = N₂ (σ₀.symm z) := fun z => by
    rw [AlgEquiv.symm_trans_apply, AlgEquiv.symm_trans_apply, AlgEquiv.symm_apply_apply,
      AlgEquiv.symm_symm]
  have hlaw' : ∀ z, σ₀.symm (furtherLocSnd I w v hI z) =
      awayCongrHom I u (u * u') hI h₃ (τ₀.symm z) := by
    rw [← furtherLocFst_eq_awayCongrHom I u u' hI h₃]
    exact hlaw
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  rw [hsnd y, hσ, hτ, hfst (τ₀.symm y), ← hlaw' y, furtherLocSnd_eq_awayCongrHom I w v hI h₄]

/-- **Conjugation preserves the algebra triple cocycle `hσc`**: the conjugating isomorphisms
telescope. -/
theorem sigma_cocycle_conj {s₁ s₂ s₃ : A} {c₁ : A₁} {c₂ : A₂} {c₃ : A₃}
    (σ₁ : awayCompletion (I.map (algebraMap R A)) s₁ ≃ₐ[R]
      awayCompletion (I.map (algebraMap R A)) s₂)
    (σ₂ : awayCompletion (I.map (algebraMap R A)) s₂ ≃ₐ[R]
      awayCompletion (I.map (algebraMap R A)) s₃)
    (σ₃ : awayCompletion (I.map (algebraMap R A)) s₃ ≃ₐ[R]
      awayCompletion (I.map (algebraMap R A)) s₁)
    (M₁ : awayCompletion (I.map (algebraMap R A)) s₁ ≃ₐ[R]
      awayCompletion (I.map (algebraMap R A₁)) c₁)
    (M₂ : awayCompletion (I.map (algebraMap R A)) s₂ ≃ₐ[R]
      awayCompletion (I.map (algebraMap R A₂)) c₂)
    (M₃ : awayCompletion (I.map (algebraMap R A)) s₃ ≃ₐ[R]
      awayCompletion (I.map (algebraMap R A₃)) c₃)
    (hc : σ₁.trans (σ₂.trans σ₃) = AlgEquiv.refl) :
    (M₁.symm.trans (σ₁.trans M₂)).trans
        ((M₂.symm.trans (σ₂.trans M₃)).trans (M₃.symm.trans (σ₃.trans M₁))) =
      AlgEquiv.refl := by
  refine AlgEquiv.ext fun x => ?_
  have hkey := AlgEquiv.ext_iff.mp hc (M₁.symm x)
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, AlgEquiv.coe_refl, id_eq] at hkey ⊢
  rw [hkey]
  exact M₁.apply_symm_apply x

end Conjugation

/-! ### The transitions -/

variable (f : ULift.{u} (Fin 3) → A)

/-- **The single-overlap transition** `A{1/f_i}{1/g_ij} ≃ₐ[R] A{1/f_j}{1/g_ji}`: the two
chart-local presentations of the overlap `D(f_i) ∩ D(f_j)` are compared by passing to the common
presentation `A{1/(f_i f_j)}` downstairs and applying 594's comparison isomorphism there. -/
def tau (hI : I.FG) (i j : ULift.{u} (Fin 3)) :
    awayCompletion (I.map (algebraMap R (chartAlgebra I f i))) (overlapElt I f i j) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (chartAlgebra I f j))) (overlapElt I f j i) :=
  (chartOverlapEquiv I f hI i j).symm.trans
    ((ThreeChart.tau hI f i j).trans (chartOverlapEquiv I f hI j i))

/-- **The double-overlap transition**, built the same way from `ThreeChart.sigma`. -/
def sigma (hI : I.FG) (i j k : ULift.{u} (Fin 3)) :
    awayCompletion (I.map (algebraMap R (chartAlgebra I f i)))
        (overlapElt I f i j * overlapElt I f i k) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (chartAlgebra I f j)))
        (overlapElt I f j k * overlapElt I f j i) :=
  (chartTripleEquiv I f hI i j k).symm.trans
    ((ThreeChart.sigma hI f i j k).trans (chartTripleEquiv I f hI j k i))

/-- **The transitions are mutually inverse** (the `τ_symm` field): `tau_symm_conj` applied to
594's `ThreeChart.tau_symm`. -/
theorem tau_symm (hI : I.FG) (i j : ULift.{u} (Fin 3)) :
    tau I f hI j i = (tau I f hI i j).symm := by
  rw [tau, tau, ThreeChart.tau_symm]
  exact tau_symm_conj I (ThreeChart.tau hI f i j) (chartOverlapEquiv I f hI i j)
    (chartOverlapEquiv I f hI j i)

/-- **σ/τ restriction compatibility** (the `hστ` hypothesis of the smart constructors):
`sigma_tau_conj` applied to 594's `ThreeChart.sigma_tau`, with the two intertwining hypotheses
supplied by the naturality of the chart identifications. -/
theorem sigma_tau (hI : I.FG) (i j k : ULift.{u} (Fin 3)) :
    (sigma I f hI i j k).symm.toAlgHom.comp
        (furtherLocSnd I (overlapElt I f j k) (overlapElt I f j i) hI) =
      (furtherLocFst I (overlapElt I f i j) (overlapElt I f i k) hI).comp
        (tau I f hI i j).symm.toAlgHom := by
  rw [tau, sigma]
  exact sigma_tau_conj I hI (ThreeChart.tau hI f i j) (ThreeChart.sigma hI f i j k)
    (chartOverlapEquiv I f hI i j) (chartOverlapEquiv I f hI j i)
    (chartTripleEquiv I f hI i j k) (chartTripleEquiv I f hI j k i)
    (isUnit_overlapElt_mul I f i j k) (isUnit_overlapElt_mul_right I f j i k)
    (isUnit_mul_triple f i j k) (isUnit_mul_triple' f j i k)
    (awayCongrHom_chartOverlapEquiv I f hI i j k)
    (awayCongrHom_chartOverlapEquiv' I f hI j i k)
    (fun y => by
      simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] using
        AlgHom.congr_fun (ThreeChart.sigma_tau hI f i j k) y)

/-- **The algebra triple cocycle** (the `hσc` hypothesis): `sigma_cocycle_conj` applied to 594's
`ThreeChart.sigma_cocycle`. -/
theorem sigma_cocycle (hI : I.FG) (i j k : ULift.{u} (Fin 3)) :
    (sigma I f hI i j k).trans ((sigma I f hI j k i).trans (sigma I f hI k i j)) =
      AlgEquiv.refl (R := R)
        (A₁ := awayCompletion (I.map (algebraMap R (chartAlgebra I f i)))
          (overlapElt I f i j * overlapElt I f i k)) := by
  rw [sigma, sigma, sigma]
  exact sigma_cocycle_conj I (ThreeChart.sigma hI f i j k) (ThreeChart.sigma hI f j k i)
    (ThreeChart.sigma hI f k i j) (chartTripleEquiv I f hI i j k) (chartTripleEquiv I f hI j k i)
    (chartTripleEquiv I f hI k i j) (ThreeChart.sigma_cocycle hI f i j k)

end ThreeChartCover

end AlgebraicGeometry

end
