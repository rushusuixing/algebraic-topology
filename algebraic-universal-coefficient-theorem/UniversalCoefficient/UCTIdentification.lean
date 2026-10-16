import UniversalCoefficient.BoundaryComparison
import UniversalCoefficient.LengthOne
import UniversalCoefficient.PIDFree
import UniversalCoefficient.ConnectingFormula

/-!
# Identifying the algebraic end terms in the universal coefficient sequence

The cokernel of the tensor boundary inclusion is homology tensored with the
coefficients. Its kernel is Mathlib's `Tor'` in degree one, deriving the first
variable. All boundary and cycle modules are proved projective using the
arbitrary-rank submodule theorem over a PID.
-/

namespace UniversalCoefficient

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

noncomputable section

universe u

variable {R : Type u} [CommRing R]

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Right tensoring a short exact presentation still computes its cokernel. -/
def tensorPresentationCokernelIso (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (D : ModuleCat.{u} R) :
    cokernel ((tensorRight D).map S.f) ≅ (tensorRight D).obj S.X₃ := by
  let T := S.map (tensorRight D)
  have he : T.Exact := by
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mpr
    change Function.Exact (S.f.hom.rTensor D) (S.g.hom.rTensor D)
    exact rTensor_exact D
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact)
      hS.moduleCat_surjective_g
  have : Epi T.g := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    exact LinearMap.rTensor_surjective D hS.moduleCat_surjective_g
  exact (cokernelIsCokernel _).coconePointUniqueUpToIso he.gIsCokernel

/-- The homology presentation whose boundary and cycle modules use exactly
the indices of `boundaryToCycles C n`. -/
def boundaryPresentation (C : ChainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    ShortComplex (ModuleCat.{u} R) :=
  ambientHomologyPresentation (C.sc' n (n - 1) (n - 1 - 1))

theorem boundaryPresentation_shortExact
    (C : ChainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (boundaryPresentation C n).ShortExact :=
  ambientHomologyPresentation_shortExact _

theorem boundaryPresentation_f
    (C : ChainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (boundaryPresentation C n).f = ModuleCat.ofHom (boundaryToCycles C n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- The presentation uses Mathlib's standard homology with an explicit
comparison of the predecessor and successor indices. -/
def boundaryPresentationHomologyIso
    (C : ChainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (boundaryPresentation C n).X₃ ≅ C.homology (n - 1) :=
  (C.homologyIsoSc' n (n - 1) (n - 1 - 1)
    ((ComplexShape.down ℤ).prev_eq' (by change n - 1 + 1 = n; omega))
    ((ComplexShape.down ℤ).next_eq' (by change n - 1 - 1 + 1 = n - 1; omega))).symm

/-- Cokernel identification, indexed by the incoming boundary differential. -/
def boundaryTensorCokernelIsoHomology
    (C : ChainComplex (ModuleCat.{u} R) ℤ) (D : ModuleCat.{u} R) (n : ℤ) :
    cokernel ((tensorRight D).map (ModuleCat.ofHom (boundaryToCycles C n))) ≅
      ModuleCat.of R ((C.homology (n - 1)) ⊗[R] D) :=
  cokernelIsoOfEq (congrArg (tensorRight D).map (boundaryPresentation_f C n).symm) ≪≫
    tensorPresentationCokernelIso _ (boundaryPresentation_shortExact C n) D ≪≫
    (tensorRight D).mapIso (boundaryPresentationHomologyIso C n)

/-- The cokernel entering the UCT in degree `n` is `H_n(C) ⊗ D`. -/
def previousBoundaryTensorCokernelIsoHomology
    (C : ChainComplex (ModuleCat.{u} R) ℤ) (D : ModuleCat.{u} R) (n : ℤ) :
    cokernel ((tensorRight D).map (ModuleCat.ofHom (boundaryToCycles C (n + 1)))) ≅
      ModuleCat.of R ((C.homology n) ⊗[R] D) := by
  have h : n + 1 - 1 = n := by omega
  exact boundaryTensorCokernelIsoHomology C D (n + 1) ≪≫
    (tensorRight D).mapIso (eqToIso (congrArg (fun k : ℤ => C.homology k) h))

variable [IsDomain R] [IsPrincipalIdealRing R]

/-- Kernel identification with Mathlib `Tor'`, which derives the homology
variable. Projectivity of both presentation modules is proved, not assumed. -/
def boundaryTensorKernelIsoTor
    (C : ChainComplex (ModuleCat.{u} R) ℤ) (D : ModuleCat.{u} R)
    [∀ n, Module.Free R (C.X n)] (n : ℤ) :
    kernel ((tensorRight D).map (ModuleCat.ofHom (boundaryToCycles C n))) ≅
      (((Tor' (ModuleCat R) 1).obj (C.homology (n - 1))).obj D) := by
  let S := boundaryPresentation C n
  have : Module.Free R S.X₁ := by
    change Module.Free R (LinearMap.range (C.d n (n - 1)).hom)
    exact submodule_free_of_pid _
  have : Module.Free R S.X₂ := by
    change Module.Free R (LinearMap.ker (C.d (n - 1) (n - 1 - 1)).hom)
    exact submodule_free_of_pid _
  exact kernelIsoOfEq
      (congrArg (tensorRight D).map (boundaryPresentation_f C n).symm) ≪≫
    (torOneIsoKernel S (boundaryPresentation_shortExact C n) D).symm ≪≫
    ((Tor' (ModuleCat R) 1).mapIso (boundaryPresentationHomologyIso C n)).app D

end

end UniversalCoefficient
