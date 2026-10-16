import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import UniversalCoefficient.Degreewise

/-!
# Flat submodules over a principal ideal domain

These results allow tensoring the kernel–image sequence with arbitrary
coefficients without assuming a finite basis or a chosen splitting.
-/

namespace UniversalCoefficient

open CategoryTheory

universe u v

variable {R : Type v} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

/-- Every submodule of a free module over a PID is flat, with no rank restriction. -/
theorem submodule_flat_of_free [Module.Free R M] (P : Submodule R M) :
    Module.Flat R P := by
  infer_instance

theorem range_flat_of_free [Module.Free R N] (f : M →ₗ[R] N) :
    Module.Flat R (LinearMap.range f) :=
  submodule_flat_of_free (LinearMap.range f)

theorem kernel_flat_of_free [Module.Free R M] (f : M →ₗ[R] N) :
    Module.Flat R (LinearMap.ker f) :=
  submodule_flat_of_free (LinearMap.ker f)

/-- Flatness of the image suffices for the tensor of the kernel inclusion to
remain injective. The coefficient module need not be flat. -/
theorem kernel_subtype_lTensor_injective [Module.Free R N] (f : M →ₗ[R] N)
    (D : Type*) [AddCommGroup D] [Module R D] :
    Function.Injective (f.ker.subtype.lTensor D) := by
  have : Module.Flat R (LinearMap.range f) := range_flat_of_free f
  apply LinearMap.lTensor_injective_of_exact_of_flat f.rangeRestrict
    (by rintro ⟨y, x, rfl⟩; exact ⟨x, rfl⟩) f.ker.subtype f.ker.injective_subtype
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, congrArg Subtype.val hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact Subtype.ext y.property

/-- The kernel–image sequence tensored on the left with a coefficient module. -/
def lTensorKernelImageShortComplex (f : M →ₗ[R] N)
    (D : Type u) [AddCommGroup D] [Module R D] : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk (f.ker.subtype.lTensor D) (f.rangeRestrict.lTensor D) (by
    rw [← LinearMap.lTensor_comp]
    have h : f.rangeRestrict.comp f.ker.subtype = 0 := by
      ext x
      exact x.property
    rw [h, LinearMap.lTensor_zero])

/-- A free codomain makes the image flat; consequently the kernel–image
sequence remains short exact after tensoring with arbitrary coefficients. -/
theorem lTensorKernelImageShortComplex_shortExact [Module.Free R N]
    (f : M →ₗ[R] N) (D : Type u) [AddCommGroup D] [Module R D] :
    (lTensorKernelImageShortComplex f D).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · apply lTensor_exact D
    · intro x
      constructor
      · intro hx
        exact ⟨⟨x, congrArg Subtype.val hx⟩, rfl⟩
      · rintro ⟨y, rfl⟩
        exact Subtype.ext y.property
    · rintro ⟨y, x, rfl⟩
      exact ⟨x, rfl⟩
  · exact kernel_subtype_lTensor_injective f D
  · apply LinearMap.lTensor_surjective
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩

end UniversalCoefficient
