import FormalSchemes.GlobalSectionsHom
import FormalSchemes.LocallyRingedSpaceBasisComponent

set_option linter.style.header false

/-!
# Sections of a morphism into a formal spectrum over a basic open, and the sheaf half on a basis

`FormalSchemes/GlobalSectionsHom.lean` reads the **global** sections of a morphism
`f : X ⟶ Spf R` out of an arbitrary locally ringed space, as a ring homomorphism
`R →+* Γ(X, 𝒪_X)`. This file does the same one open down. Over the basic open `D(g)` the sections
of `𝒪_{Spf R}` are the completed localization `FormalSpectrum.awayCompletion I g`
(`FormalSpectrum.sectionsBasicOpenEquiv`, EGA I, 10.1.4), so the comparison map of `f` at `D(g)`
reads as a ring homomorphism

> `FormalSpectrum.basicOpenSectionsHom I X f g : R{1/g} →+* Γ(X, f⁻¹ D(g))`

with no sheaf on the source side, and it is `FormalSpectrum.globalSectionsHom`'s exact analogue —
the component of `f.c` precomposed with the identification of the source ring.

The two facts this file exists for:

* the comparison at `D(g)` is invertible exactly when `basicOpenSectionsHom … g` is **bijective**
  (`FormalSpectrum.isIso_c_app_basicOpen_iff_bijective`), which is
  `FormalSpectrum.isIso_c_app_top_of_bijective_globalSectionsHom`
  (`FormalSchemes.TateInvNodeChartDescentIso`) at a general basic open and as an equivalence;
* the basic opens are a basis (`FormalSpectrum.isBasis_basicOpen`), so a `∀ O` obligation on the
  sheaf half of an isomorphism criterion for a morphism into `Spf R` is a `∀ g : R` obligation
  (`FormalSpectrum.isIso_c_app_iff_basicOpen`), by
  `AlgebraicGeometry.LocallyRingedSpace.isIso_c_app_iff_isBasis`.

Composing them, the sheaf half is a statement about ring homomorphisms out of the completed
localizations of `R` and nothing else
(`FormalSpectrum.isIso_c_app_iff_bijective_basicOpenSectionsHom`).

## What is *not* proved here

**Nothing about the target `Γ(X, f⁻¹ D(g))`.** The right-hand side of `basicOpenSectionsHom` is
the sections of `X` over the **preimage** of `D(g)` along `f.base`, and this file gives no
description of that open. For a source that is not itself a formal spectrum this is where the
content is, and computing it needs the base map — which is exactly why the two halves of
`AlgebraicGeometry.LocallyRingedSpace.isIso_iff_isIso_base_and_isIso_c_app` are not independent in
practice even though the statement separates them (issue 1752).

**Nothing about `g = 1` beyond the equality of opens.** `FormalSpectrum.basicOpen_one` gives
`D(1) = ⊤`, so `FormalSpectrum.isIso_c_app_basicOpen_one_iff` transports the criterion at `⊤` to
the basic open at `1`. The source rings are **not** identified: `awayCompletion I 1` is the
`I`-adic completion of `Localization.Away 1` and no isomorphism of it with `R` is produced here,
so `FormalSpectrum.globalSectionsHom` is not recovered as a value of `basicOpenSectionsHom`.

**No surjectivity or injectivity criterion in terms of the ring `R`.** Bijectivity of
`basicOpenSectionsHom … g` is restated, not decided.

## Main definitions and results

* `FormalSpectrum.isIso_c_app_iff_basicOpen`: the sheaf half of an isomorphism criterion for a
  morphism into `Spf R` is a statement about the basic opens.
* `FormalSpectrum.basicOpenSectionsHom`: the sections homomorphism `R{1/g} →+* Γ(X, f⁻¹ D(g))`,
  and `FormalSpectrum.basicOpenSectionsHom_comp`, its functoriality in the source.
* `FormalSpectrum.isIso_c_app_basicOpen_iff_bijective`: the comparison at `D(g)` is invertible
  exactly when that homomorphism is bijective.
* `FormalSpectrum.isIso_c_app_iff_bijective_basicOpenSectionsHom`: the two combined.
* `FormalSpectrum.injective_basicOpenSectionsHom_comp_iff`: precomposing with a morphism that is
  injective on sections — a quotient projection, say — does not change injectivity at `D(g)`.
* `FormalSpectrum.isIso_c_app_basicOpen_one_iff`: the basic open at `1` is the top open.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1 (10.1.4), §10.4.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The sheaf half of an isomorphism criterion, on the basic opens.** For a morphism
`f : X ⟶ Spf R` out of an arbitrary locally ringed space, "every comparison map of `f` is
invertible" is equivalent to "the comparison map at `D(g)` is invertible for every `g : R`".

`AlgebraicGeometry.LocallyRingedSpace.isIso_c_app_iff_isBasis` at
`FormalSpectrum.isBasis_basicOpen`. Note the index type of the basis is `R` itself, so the
right-hand side is a family indexed by the whole ring and not by the opens of a space. -/
theorem isIso_c_app_iff_basicOpen (X : LocallyRingedSpace.{u})
    (f : X ⟶ locallyRingedSpaceObj I) :
    (∀ g : R, IsIso (f.c.app (op (basicOpen I g)))) ↔
      ∀ O : (Opens (FormalSpectrum I))ᵒᵖ, IsIso (f.c.app O) :=
  LocallyRingedSpace.isIso_c_app_iff_isBasis f (isBasis_basicOpen I)

/-- **Sections of a morphism into a formal spectrum over a basic open.** The ring homomorphism
`R{1/g} →+* Γ(X, f⁻¹ D(g))` induced by `f : X ⟶ Spf R`: the component of `f.c` at `D(g)`
precomposed with the identification `R{1/g} ≃+* Γ(Spf R, D(g))` of
`FormalSpectrum.sectionsBasicOpenEquiv` (EGA I, 10.1.4).

This is `FormalSpectrum.globalSectionsHom` with `⊤` replaced by `D(g)`; as there, the target of
`f.c.app (op (basicOpen I g))` is `Γ(X, f⁻¹ D(g))` definitionally and no transport is needed. -/
def basicOpenSectionsHom (X : LocallyRingedSpace.{u}) (f : X ⟶ locallyRingedSpaceObj I) (g : R) :
    awayCompletion I g →+* X.presheaf.obj (op ((Opens.map f.base).obj (basicOpen I g))) :=
  (f.c.app (op (basicOpen I g))).hom.comp (sectionsBasicOpenEquiv I g).symm.toRingHom

omit [TopologicalSpace R] [IsAdicRing I] in
theorem basicOpenSectionsHom_apply (X : LocallyRingedSpace.{u})
    (f : X ⟶ locallyRingedSpaceObj I) (g : R) (a : awayCompletion I g) :
    basicOpenSectionsHom I X f g a =
      (f.c.app (op (basicOpen I g))).hom ((sectionsBasicOpenEquiv I g).symm a) :=
  rfl

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Functoriality in the source.** Restricting `f : X ⟶ Spf R` along `h : Z ⟶ X` restricts its
sections homomorphism at `D(g)` along the comparison map of `h` at the preimage of `D(g)`.

Definitional, exactly as `FormalSpectrum.globalSectionsHom_comp` is: only the source end is wrapped
through an identification, and that end is untouched by the composition. -/
theorem basicOpenSectionsHom_comp {Z X : LocallyRingedSpace.{u}} (h : Z ⟶ X)
    (f : X ⟶ locallyRingedSpaceObj I) (g : R) :
    basicOpenSectionsHom I Z (h ≫ f) g =
      (h.c.app (op ((Opens.map f.base).obj (basicOpen I g)))).hom.comp
        (basicOpenSectionsHom I X f g) :=
  rfl

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The comparison at `D(g)` is invertible exactly when the sections homomorphism is bijective.**
The two differ by the isomorphism `FormalSpectrum.sectionsBasicOpenEquiv`, so
`ConcreteCategory.isIso_iff_bijective` and cancellation of a bijection is the whole proof.

At `g = 1` and through `FormalSpectrum.basicOpen_one` this is
`FormalSpectrum.isIso_c_app_top_of_bijective_globalSectionsHom`
(`FormalSchemes.TateInvNodeChartDescentIso`) — except that that one is stated at `⊤` and against
`FormalSpectrum.globalSectionsHom`, whose source ring is `R` and not `awayCompletion I 1`; the two
source rings are not identified here. -/
theorem isIso_c_app_basicOpen_iff_bijective (X : LocallyRingedSpace.{u})
    (f : X ⟶ locallyRingedSpaceObj I) (g : R) :
    IsIso (f.c.app (op (basicOpen I g))) ↔ Function.Bijective (basicOpenSectionsHom I X f g) := by
  have he : ⇑(CommRingCat.Hom.hom (f.c.app (op (basicOpen I g)))) =
      ⇑(basicOpenSectionsHom I X f g) ∘ ⇑(sectionsBasicOpenEquiv I g) :=
    funext fun s => congrArg _ ((sectionsBasicOpenEquiv I g).symm_apply_apply s).symm
  rw [ConcreteCategory.isIso_iff_bijective, he]
  exact Function.Bijective.of_comp_iff _ (sectionsBasicOpenEquiv I g).bijective

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Precomposing with a morphism that is injective on sections does not change injectivity at
`D(g)`.** If the comparison map of `h : Z ⟶ X` at the preimage of `D(g)` is injective — which is
what a quotient projection gives, at every open — then the sections homomorphism of `h ≫ f` at
`D(g)` is injective exactly when that of `f` is.

`FormalSpectrum.basicOpenSectionsHom_comp` and nothing else: injectives compose, and a composite
that is injective has an injective right factor. -/
theorem injective_basicOpenSectionsHom_comp_iff {Z X : LocallyRingedSpace.{u}} (h : Z ⟶ X)
    (f : X ⟶ locallyRingedSpaceObj I) (g : R)
    (hinj : Function.Injective (h.c.app (op ((Opens.map f.base).obj (basicOpen I g)))).hom) :
    Function.Injective (basicOpenSectionsHom I Z (h ≫ f) g) ↔
      Function.Injective (basicOpenSectionsHom I X f g) := by
  rw [basicOpenSectionsHom_comp]
  refine ⟨fun H x y hxy => H ?_, fun H x y hxy => H (hinj hxy)⟩
  exact congrArg ⇑(h.c.app (op ((Opens.map f.base).obj (basicOpen I g)))).hom hxy

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The sheaf half, written out.** For a morphism `f : X ⟶ Spf R`, every comparison map of `f`
is invertible exactly when, for every `g : R`, the sections homomorphism
`R{1/g} →+* Γ(X, f⁻¹ D(g))` is bijective.

The left-hand side mentions no sheaf, no open of `Spf R` and no category: it is a family of ring
homomorphisms out of the completed localizations of `R`, indexed by `R`. What it does still mention
is `Γ(X, f⁻¹ D(g))`, whose open is taken along `f.base`; see the `## What is *not* proved here` of
this file. -/
theorem isIso_c_app_iff_bijective_basicOpenSectionsHom (X : LocallyRingedSpace.{u})
    (f : X ⟶ locallyRingedSpaceObj I) :
    (∀ g : R, Function.Bijective (basicOpenSectionsHom I X f g)) ↔
      ∀ O : (Opens (FormalSpectrum I))ᵒᵖ, IsIso (f.c.app O) :=
  (forall_congr' fun g => (isIso_c_app_basicOpen_iff_bijective I X f g).symm).trans
    (isIso_c_app_iff_basicOpen I X f)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The basic open at `1` is the top open**, so the comparison map there is the one at `⊤`.
`FormalSpectrum.basicOpen_one`, recorded because it is the honest measure of how much of a `∀ g`
obligation a statement about `⊤` discharges: exactly one member of a family indexed by `R`. -/
theorem isIso_c_app_basicOpen_one_iff (X : LocallyRingedSpace.{u})
    (f : X ⟶ locallyRingedSpaceObj I) :
    IsIso (f.c.app (op (basicOpen I (1 : R)))) ↔
      IsIso (f.c.app (op (⊤ : Opens (FormalSpectrum I)))) := by
  rw [basicOpen_one]

end FormalSpectrum

end
