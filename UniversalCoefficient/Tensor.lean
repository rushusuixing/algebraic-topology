import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import UniversalCoefficient.CyclesSequence
import UniversalCoefficient.PIDFlat

/-!
# Tensoring the cycles sequence

Tensoring a split short complex preserves its splitting and hence short exactness.
The general splitting lemma takes an explicit splitting as input. For the
cycles sequence of a degreewise free complex over a PID, flatness of each image
proves short exactness after tensoring without choosing any splitting.
-/

open CategoryTheory CategoryTheory.MonoidalCategory

namespace UniversalCoefficient

noncomputable section

universe u

variable {R : Type u} [CommRing R]

/-- Tensor every object and map in a short complex on the right with `D`. -/
def tensorShortComplex (S : ShortComplex (ModuleCat.{u} R)) (D : ModuleCat.{u} R) :
    ShortComplex (ModuleCat.{u} R) :=
  S.map (tensorRight D)

/-- An explicit splitting remains a splitting after tensoring with any module. -/
def tensorShortComplexSplitting {S : ShortComplex (ModuleCat.{u} R)}
    (s : S.Splitting) (D : ModuleCat.{u} R) :
    (tensorShortComplex S D).Splitting :=
  s.map (tensorRight D)

/-- Tensoring a split sequence with arbitrary coefficients is short exact. -/
theorem tensorShortComplex_shortExact {S : ShortComplex (ModuleCat.{u} R)}
    (s : S.Splitting) (D : ModuleCat.{u} R) :
    (tensorShortComplex S D).ShortExact :=
  (tensorShortComplexSplitting s D).shortExact

/-- Tensor a chain complex with a coefficient module on the right. -/
def tensorChainFunctor (D : ModuleCat.{u} R) :
    ChainComplex (ModuleCat.{u} R) ℤ ⥤ ChainComplex (ModuleCat.{u} R) ℤ :=
  (tensorRight D).mapHomologicalComplex (ComplexShape.down ℤ)

instance (D : ModuleCat.{u} R) : (tensorChainFunctor D).Additive :=
  inferInstanceAs (((tensorRight D).mapHomologicalComplex (ComplexShape.down ℤ)).Additive)

/-- The canonical cycles sequence after tensoring every term and differential. -/
def tensorCyclesSequence (C : ChainComplex (ModuleCat.{u} R) ℤ)
    (D : ModuleCat.{u} R) : ShortComplex (ChainComplex (ModuleCat.{u} R) ℤ) :=
  (cyclesSequence C).map (tensorChainFunctor D)

/-- Degreewise splittings suffice; a splitting by chain maps is not required. -/
theorem tensorCyclesSequence_shortExact_of_splittings
    (C : ChainComplex (ModuleCat.{u} R) ℤ) (D : ModuleCat.{u} R)
    (s : ∀ n, (kernelImageShortComplex (C.d n (n - 1)).hom).Splitting) :
    (tensorCyclesSequence C D).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact tensorShortComplex_shortExact (s n) D

variable [IsDomain R] [IsPrincipalIdealRing R]

/-- The right tensor of the kernel–image sequence remains short exact when
the differential has free codomain over a PID. No rank restriction is used. -/
theorem tensorKernelImageShortComplex_shortExact
    {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Free R N] (f : M →ₗ[R] N) (D : ModuleCat.{u} R) :
    (tensorShortComplex (kernelImageShortComplex f) D).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · apply rTensor_exact D
    · intro x
      constructor
      · intro hx
        exact ⟨⟨x, congrArg Subtype.val hx⟩, rfl⟩
      · rintro ⟨y, rfl⟩
        exact Subtype.ext y.property
    · rintro ⟨y, x, rfl⟩
      exact ⟨x, rfl⟩
  · exact (LinearMap.lTensor_inj_iff_rTensor_inj D f.ker.subtype).mp
      (kernel_subtype_lTensor_injective f D)
  · apply LinearMap.rTensor_surjective
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩

/-- Over a PID, tensoring the canonical cycles sequence of a degreewise free
complex with arbitrary coefficients produces a short exact sequence of complexes. -/
theorem tensorCyclesSequence_shortExact
    (C : ChainComplex (ModuleCat.{u} R) ℤ) (D : ModuleCat.{u} R)
    [∀ n, Module.Free R (C.X n)] : (tensorCyclesSequence C D).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact tensorKernelImageShortComplex_shortExact (C.d n (n - 1)).hom D

end

end UniversalCoefficient
