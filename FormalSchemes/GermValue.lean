import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.RingTheory.Localization.AtPrime.Basic

set_option linter.style.header false

/-!
# Germs of sections of the structure sheaf versus their values

A section `t` of the structure sheaf of `Spec A` over an open `W` has, at every point `p ∈ W`,
both a *germ* in the stalk at `p` and a *value* in `Localization.AtPrime p.asIdeal` (sections
are, by construction, dependent functions valued in the localizations). This file relates
invertibility of the two: over a basic open, the germ of `t` at `p` is a unit if and only if
its value at `p` is a unit (`AlgebraicGeometry.StructureSheaf.isUnit_germ_iff_isUnit_value`).

The proof identifies the composite `sections → stalk ≃ Localization.AtPrime p` with the value
map by the uniqueness of `A`-algebra maps out of a localization: over a basic open `D(g) ∋ p`,
the section ring is a localization of `A` away from `g`, and both maps agree on the image
of `A`.

This is the mechanism by which invertibility of germs transfers along the maps of structure
sheaves induced by ring homomorphisms (whose effect on values is `Localization.localRingHom`,
a local ring homomorphism); it is used to prove that the morphisms of formal spectra are
morphisms of locally ringed spaces.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.StructureSheaf

variable {A : Type u} [CommRing A]

/-- Evaluation of a section of the structure sheaf at a point of its domain, as a ring
homomorphism to the localization at the corresponding prime. -/
def sectionValue (W : Opens (PrimeSpectrum.Top A)) (p : PrimeSpectrum.Top A) (hp : p ∈ W) :
    ((Spec.structureSheaf A).presheaf.obj (op W) : Type u) →+*
      Localization.AtPrime p.asIdeal where
  toFun t := t.1 ⟨p, hp⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem sectionValue_apply (W : Opens (PrimeSpectrum.Top A)) (p : PrimeSpectrum.Top A)
    (hp : p ∈ W) (t : (Spec.structureSheaf A).presheaf.obj (op W)) :
    sectionValue W p hp t = t.1 ⟨p, hp⟩ :=
  rfl

theorem sectionValue_algebraMap (W : Opens (PrimeSpectrum.Top A)) (p : PrimeSpectrum.Top A)
    (hp : p ∈ W) (a : A) :
    sectionValue W p hp (algebraMap A _ a) = algebraMap A _ a :=
  rfl

theorem sectionValue_res (W W' : Opens (PrimeSpectrum.Top A)) (i : W' ⟶ W)
    (p : PrimeSpectrum.Top A) (hp : p ∈ W')
    (t : (Spec.structureSheaf A).presheaf.obj (op W)) :
    sectionValue W' p hp (((Spec.structureSheaf A).presheaf.map i.op).hom t) =
      sectionValue W p (leOfHom i hp) t :=
  rfl

/-- Over a basic open `D(g)`, the composite of the germ map at `p ∈ D(g)` with the canonical
identification of the stalk with `Localization.AtPrime p` is evaluation at `p`: both are
`A`-algebra maps out of a localization of `A`, so they agree because they agree on `A`. -/
theorem algEquiv_germ_eq_sectionValue (g : A) (p : PrimeSpectrum.Top A)
    (hp : p ∈ PrimeSpectrum.basicOpen g) :
    ((IsLocalization.algEquiv p.asIdeal.primeCompl
        ((Spec.structureSheaf A).presheaf.stalk p)
        (Localization.AtPrime p.asIdeal)).toRingEquiv.toRingHom.comp
      ((Spec.structureSheaf A).presheaf.germ (PrimeSpectrum.basicOpen g) p hp).hom) =
      sectionValue (PrimeSpectrum.basicOpen g) p hp := by
  apply IsLocalization.ringHom_ext (Submonoid.powers g)
  refine RingHom.ext fun a => ?_
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe]
  rw [sectionValue_algebraMap]
  have hgerm : ((Spec.structureSheaf A).presheaf.germ (PrimeSpectrum.basicOpen g) p hp).hom
      ((algebraMap A ((Spec.structureSheaf A).presheaf.obj
        (op (PrimeSpectrum.basicOpen g)))) a) =
      algebraMap A ((Spec.structureSheaf A).presheaf.stalk p) a := by
    have h := algebraMap_germ_apply (PrimeSpectrum.basicOpen g) p hp a
    rw [stalkAlgebra_map]
    exact h
  rw [hgerm]
  exact (IsLocalization.algEquiv p.asIdeal.primeCompl _ _).commutes a

/-- **Germs are units precisely where values are units** (over a basic open): for a section `t`
of the structure sheaf over `D(g)` and `p ∈ D(g)`, the germ of `t` at `p` is a unit in the
stalk if and only if the value `t(p)` is a unit in `Localization.AtPrime p`. -/
theorem isUnit_germ_iff_isUnit_value (g : A) (p : PrimeSpectrum.Top A)
    (hp : p ∈ PrimeSpectrum.basicOpen g)
    (t : (Spec.structureSheaf A).presheaf.obj (op (PrimeSpectrum.basicOpen g))) :
    IsUnit (((Spec.structureSheaf A).presheaf.germ (PrimeSpectrum.basicOpen g) p hp).hom t) ↔
      IsUnit (sectionValue (PrimeSpectrum.basicOpen g) p hp t) := by
  have key := DFunLike.congr_fun (algEquiv_germ_eq_sectionValue g p hp) t
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe] at key
  constructor
  · intro h
    rw [← key]
    exact h.map _
  · intro h
    rw [← key] at h
    have h2 := h.map (IsLocalization.algEquiv p.asIdeal.primeCompl
      ((Spec.structureSheaf A).presheaf.stalk p)
      (Localization.AtPrime p.asIdeal)).toRingEquiv.symm
    rwa [RingEquiv.symm_apply_apply] at h2

end AlgebraicGeometry.StructureSheaf
