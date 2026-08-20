import FormalSchemes.CompletedTensorAwayInterchangePullbackLegs

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Comparison maps of completed localizations, and their rigidity

Fix an adic base `(R, I)` and an `R`-algebra `A`. For `s : A` the completed localization
`A{1/s} = FormalSpectrum.awayCompletion (I·A) s` is the chart of `Spf A` over the basic open
`D(s)`. Two such charts are compared by completing the unique `A`-algebra map between the
localizations:

* if `x` becomes a **unit** in `A_y` — geometrically `D(y) ⊆ D(x)` — there is a comparison map
  `A{1/x} →ₐ[R] A{1/y}`;
* if moreover `y` becomes a unit in `A_x` — so `D(x) = D(y)` — the two comparison maps are mutually
  inverse and give a comparison **isomorphism** `A{1/x} ≃ₐ[R] A{1/y}`.

## Rigidity, and why it matters

The load-bearing statement of this file is not the construction but the **rigidity**
`furtherLocAlgHom_eq_awayCongrHom`: *every* completed localization map `A{1/x} →ₐ[R] A{1/y}`
induced by an `A`-compatible localization map is *the* comparison map. Localization maps out of
`A_x` are determined by their restriction to `A` (`IsLocalization.ringHom_ext`), and
`AdicCompletion.mapCompletion` depends on nothing else, so any two composites of further
localizations with the same source and target are equal.

That turns the compatibility obligations of `AffineChartedFibreDatum.ofAlgebraData` /
`AffineChartedFibreDatumX.ofAlgebraData` (`hστ`, `hσc`, `τ_symm`) into bookkeeping whenever the
transition data of a glued formal scheme is built from comparison maps: both sides of each equation
are automatically the same comparison map. The three-chart datum of
`FormalSchemes.ThreeChartDatum` is built exactly this way.

## Main definitions and results

* `CompletedTensorAwayInterchange.furtherLocAlgHom_congr`, `..._comp`, `..._self`: the completion
  functor's rigidity, composition and identity laws for `furtherLocAlgHom`.
* `CompletedTensorAwayInterchange.awayCongrHom`: the comparison map `A{1/x} →ₐ[R] A{1/y}`, with
  `awayCongrHom_comp` and `awayCongrHom_self`.
* `CompletedTensorAwayInterchange.awayCongrEquiv`: the comparison isomorphism when `D(x) = D(y)`.
* `CompletedTensorAwayInterchange.furtherLocFst_eq_awayCongrHom` and `furtherLocSnd_eq_...`: the
  two further localizations `A{1/g₁} → A{1/(g₁·g₂)}`, `A{1/g₂} → A{1/(g₁·g₂)}` are comparison maps.
* `CompletedTensorAwayInterchange.isUnit_algebraMap_away_of_dvd_pow`,
  `..._trans`: the two ways units are produced in practice.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1 (10.1.4), §10.7.
-/

noncomputable section

open FormalSpectrum

universe u

namespace CompletedTensorAwayInterchange

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {A : Type u} [CommRing A] [Algebra R A]

/-- **Rigidity of the completed localization maps.** Two `A`-compatible localization maps
`A_s → A_t` are equal (`IsLocalization.ringHom_ext`), hence so are their completions: the completed
map `A{1/s} →ₐ[R] A{1/t}` does not depend on which localization map it was built from. -/
theorem furtherLocAlgHom_congr (s t : A) (hI : I.FG)
    (ρ₁ ρ₂ : Localization.Away s →+* Localization.Away t)
    (hρ₁ : ρ₁.comp (algebraMap A (Localization.Away s)) = algebraMap A (Localization.Away t))
    (hρ₂ : ρ₂.comp (algebraMap A (Localization.Away s)) = algebraMap A (Localization.Away t)) :
    furtherLocAlgHom I s t hI ρ₁ hρ₁ = furtherLocAlgHom I s t hI ρ₂ hρ₂ := by
  obtain rfl : ρ₁ = ρ₂ :=
    IsLocalization.ringHom_ext (Submonoid.powers s) (hρ₁.trans hρ₂.symm)
  rfl

/-- **Composition law.** The completion of a composite of `A`-compatible localization maps is the
composite of the completions (`AdicCompletion.mapCompletion_comp`). -/
theorem furtherLocAlgHom_comp (s t u : A) (hI : I.FG)
    (ρ : Localization.Away s →+* Localization.Away t)
    (ρ' : Localization.Away t →+* Localization.Away u)
    (hρ : ρ.comp (algebraMap A (Localization.Away s)) = algebraMap A (Localization.Away t))
    (hρ' : ρ'.comp (algebraMap A (Localization.Away t)) = algebraMap A (Localization.Away u)) :
    (furtherLocAlgHom I t u hI ρ' hρ').comp (furtherLocAlgHom I s t hI ρ hρ) =
      furtherLocAlgHom I s u hI (ρ'.comp ρ)
        (by rw [RingHom.comp_assoc, hρ, hρ']) := by
  have hle : ((I.map (algebraMap R A)).map (algebraMap A (Localization.Away s))).map ρ ≤
      (I.map (algebraMap R A)).map (algebraMap A (Localization.Away t)) :=
    le_of_eq (by rw [Ideal.map_map, hρ])
  have hle' : ((I.map (algebraMap R A)).map (algebraMap A (Localization.Away t))).map ρ' ≤
      (I.map (algebraMap R A)).map (algebraMap A (Localization.Away u)) :=
    le_of_eq (by rw [Ideal.map_map, hρ'])
  refine AlgHom.ext fun x => ?_
  exact RingHom.congr_fun
    (AdicCompletion.mapCompletion_comp ρ ρ' hle hle'
      ((hI.map (algebraMap R A)).map (algebraMap A (Localization.Away t)))
      ((hI.map (algebraMap R A)).map (algebraMap A (Localization.Away u)))
      ((hI.map (algebraMap R A)).map (algebraMap A (Localization.Away s)))) x

/-- **Identity law.** A completed localization map from a chart to itself is the identity: by
rigidity it is the completion of `RingHom.id`, which is `AdicCompletion.mapCompletion_id`. -/
theorem furtherLocAlgHom_self (s : A) (hI : I.FG)
    (ρ : Localization.Away s →+* Localization.Away s)
    (hρ : ρ.comp (algebraMap A (Localization.Away s)) = algebraMap A (Localization.Away s)) :
    furtherLocAlgHom I s s hI ρ hρ =
      AlgHom.id R (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) s) := by
  rw [furtherLocAlgHom_congr I s s hI ρ (RingHom.id _) hρ (RingHom.id_comp _)]
  refine AlgHom.ext fun x => ?_
  exact RingHom.congr_fun
    (AdicCompletion.mapCompletion_id
      ((hI.map (algebraMap R A)).map (algebraMap A (Localization.Away s)))) x

/-! ### The comparison map of two completed localizations with the same basic open -/

/-- **The comparison map `A{1/x} →ₐ[R] A{1/y}`** available whenever `x` becomes a unit in `A_y`
(geometrically: `D(y) ⊆ D(x)`). It is the completion of `IsLocalization.Away.lift`, i.e. of the
unique `A`-algebra map `A_x → A_y`. -/
def awayCongrHom (x y : A) (hI : I.FG) (hxy : IsUnit (algebraMap A (Localization.Away y) x)) :
    FormalSpectrum.awayCompletion (I.map (algebraMap R A)) x →ₐ[R]
      FormalSpectrum.awayCompletion (I.map (algebraMap R A)) y :=
  furtherLocAlgHom I x y hI (IsLocalization.Away.lift x hxy)
    (IsLocalization.Away.lift_comp x hxy)

/-- **Rigidity**: *every* completed localization map `A{1/x} →ₐ[R] A{1/y}` induced by an
`A`-compatible localization map is the comparison map. In particular there is at most one such map,
so any two composites of further-localization maps with the same source and target agree. -/
theorem furtherLocAlgHom_eq_awayCongrHom (x y : A) (hI : I.FG)
    (ρ : Localization.Away x →+* Localization.Away y)
    (hρ : ρ.comp (algebraMap A (Localization.Away x)) = algebraMap A (Localization.Away y))
    (hxy : IsUnit (algebraMap A (Localization.Away y) x)) :
    furtherLocAlgHom I x y hI ρ hρ = awayCongrHom I x y hI hxy :=
  furtherLocAlgHom_congr I x y hI _ _ _ _

/-- Unit-ness composes along the comparison maps: if `x` is a unit in `A_y` and `y` is a unit in
`A_z`, then `x` is a unit in `A_z` (transport `hxy` along the map `A_y → A_z`). -/
theorem isUnit_algebraMap_away_trans {x y z : A}
    (hxy : IsUnit (algebraMap A (Localization.Away y) x))
    (hyz : IsUnit (algebraMap A (Localization.Away z) y)) :
    IsUnit (algebraMap A (Localization.Away z) x) := by
  have h := hxy.map (IsLocalization.Away.lift y hyz)
  rwa [IsLocalization.Away.lift_eq] at h

/-- The comparison maps compose. -/
theorem awayCongrHom_comp (x y z : A) (hI : I.FG)
    (hxy : IsUnit (algebraMap A (Localization.Away y) x))
    (hyz : IsUnit (algebraMap A (Localization.Away z) y)) :
    (awayCongrHom I y z hI hyz).comp (awayCongrHom I x y hI hxy) =
      awayCongrHom I x z hI (isUnit_algebraMap_away_trans hxy hyz) := by
  rw [awayCongrHom, awayCongrHom, furtherLocAlgHom_comp]
  exact furtherLocAlgHom_eq_awayCongrHom I x z hI _ _ _

/-- The comparison map from a chart to itself is the identity. -/
theorem awayCongrHom_self (x : A) (hI : I.FG)
    (hxx : IsUnit (algebraMap A (Localization.Away x) x)) :
    awayCongrHom I x x hI hxx =
      AlgHom.id R (FormalSpectrum.awayCompletion (I.map (algebraMap R A)) x) :=
  furtherLocAlgHom_self I x hI _ _

/-- **The comparison isomorphism `A{1/x} ≃ₐ[R] A{1/y}`** of two completed localizations at
elements cutting out the same basic open (`D(x) = D(y)`, in the form "each becomes a unit after
inverting the other"). -/
def awayCongrEquiv (x y : A) (hI : I.FG)
    (hxy : IsUnit (algebraMap A (Localization.Away y) x))
    (hyx : IsUnit (algebraMap A (Localization.Away x) y)) :
    FormalSpectrum.awayCompletion (I.map (algebraMap R A)) x ≃ₐ[R]
      FormalSpectrum.awayCompletion (I.map (algebraMap R A)) y :=
  AlgEquiv.ofAlgHom (awayCongrHom I x y hI hxy) (awayCongrHom I y x hI hyx)
    (by rw [awayCongrHom_comp I y x y hI hyx hxy, awayCongrHom_self])
    (by rw [awayCongrHom_comp I x y x hI hxy hyx, awayCongrHom_self])

@[simp]
theorem awayCongrEquiv_toAlgHom (x y : A) (hI : I.FG)
    (hxy : IsUnit (algebraMap A (Localization.Away y) x))
    (hyx : IsUnit (algebraMap A (Localization.Away x) y)) :
    (awayCongrEquiv I x y hI hxy hyx).toAlgHom = awayCongrHom I x y hI hxy :=
  AlgEquiv.toAlgHom_ofAlgHom _ _ _ _

@[simp]
theorem awayCongrEquiv_symm (x y : A) (hI : I.FG)
    (hxy : IsUnit (algebraMap A (Localization.Away y) x))
    (hyx : IsUnit (algebraMap A (Localization.Away x) y)) :
    (awayCongrEquiv I x y hI hxy hyx).symm = awayCongrEquiv I y x hI hyx hxy :=
  AlgEquiv.ofAlgHom_symm _ _ _ _

@[simp]
theorem awayCongrEquiv_symm_toAlgHom (x y : A) (hI : I.FG)
    (hxy : IsUnit (algebraMap A (Localization.Away y) x))
    (hyx : IsUnit (algebraMap A (Localization.Away x) y)) :
    (awayCongrEquiv I x y hI hxy hyx).symm.toAlgHom = awayCongrHom I y x hI hyx := by
  rw [awayCongrEquiv_symm, awayCongrEquiv_toAlgHom]

/-! ### Units, and the two further localizations as comparison maps -/

/-- An element dividing a power of the away element becomes a unit in the localization. This is the
practical form of "`D(y) ⊆ D(x)`" for the comparison maps above: `x` need only divide *some power*
of `y`, not `y` itself. -/
theorem isUnit_algebraMap_away_of_dvd_pow {x y : A} (n : ℕ) (h : x ∣ y ^ n) :
    IsUnit (algebraMap A (Localization.Away y) x) :=
  isUnit_of_dvd_unit (map_dvd _ h)
    (by rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit y).pow n)

/-- The first further localization `A{1/g₁} →ₐ[R] A{1/(g₁·g₂)}` is the comparison map. -/
theorem furtherLocFst_eq_awayCongrHom (g₁ g₂ : A) (hI : I.FG)
    (h : IsUnit (algebraMap A (Localization.Away (g₁ * g₂)) g₁)) :
    furtherLocFst I g₁ g₂ hI = awayCongrHom I g₁ (g₁ * g₂) hI h := by
  rw [furtherLocFst]
  exact furtherLocAlgHom_eq_awayCongrHom I _ _ hI _ _ h

/-- The second further localization `A{1/g₂} →ₐ[R] A{1/(g₁·g₂)}` is the comparison map. -/
theorem furtherLocSnd_eq_awayCongrHom (g₁ g₂ : A) (hI : I.FG)
    (h : IsUnit (algebraMap A (Localization.Away (g₁ * g₂)) g₂)) :
    furtherLocSnd I g₁ g₂ hI = awayCongrHom I g₂ (g₁ * g₂) hI h := by
  rw [furtherLocSnd]
  exact furtherLocAlgHom_eq_awayCongrHom I _ _ hI _ _ h

end CompletedTensorAwayInterchange

end
