import UniversalCoefficient.Tensor
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Homology of the zero-differential ends of the tensor cycles sequence

The canonical homology objects are identified with their degree objects using
Mathlib's canonical cycles inclusion and homology projection isomorphisms.
These identifications require no PID or freeness assumptions.
-/

open CategoryTheory
open scoped TensorProduct

namespace UniversalCoefficient

noncomputable section

universe u

variable {R : Type u} [CommRing R]

/-- Homology of a zero-differential complex is canonically its degree object. -/
def zeroDifferentialHomologyIso (K : ChainComplex (ModuleCat.{u} R) ℤ)
    (h : ∀ i j, K.d i j = 0) (n : ℤ) : K.homology n ≅ K.X n :=
  (K.isoHomologyπ _ n rfl (h _ n)).symm ≪≫ K.iCyclesIso n _ rfl (h n _)

/-- The zero-differential cycles complex tensored with the coefficient module. -/
def tensorCycleComplex (C : ChainComplex (ModuleCat.{u} R) ℤ) (D : ModuleCat.{u} R) :
    ChainComplex (ModuleCat.{u} R) ℤ :=
  (tensorChainFunctor D).obj (cycleComplex C)

/-- The zero-differential reindexed boundaries complex tensored with coefficients. -/
def tensorPreviousBoundaryComplex (C : ChainComplex (ModuleCat.{u} R) ℤ)
    (D : ModuleCat.{u} R) : ChainComplex (ModuleCat.{u} R) ℤ :=
  (tensorChainFunctor D).obj (previousBoundaryComplex C)

theorem tensorCycleComplex_d (C : ChainComplex (ModuleCat.{u} R) ℤ)
    (D : ModuleCat.{u} R) (i j : ℤ) : (tensorCycleComplex C D).d i j = 0 := by
  change (CategoryTheory.MonoidalCategory.tensorRight D).map 0 = 0
  exact (CategoryTheory.MonoidalCategory.tensorRight D).map_zero _ _

theorem tensorPreviousBoundaryComplex_d (C : ChainComplex (ModuleCat.{u} R) ℤ)
    (D : ModuleCat.{u} R) (i j : ℤ) : (tensorPreviousBoundaryComplex C D).d i j = 0 := by
  change (CategoryTheory.MonoidalCategory.tensorRight D).map 0 = 0
  exact (CategoryTheory.MonoidalCategory.tensorRight D).map_zero _ _

/-- The left end's homology is the tensor product of the original cycles and coefficients. -/
def tensorCycleComplexHomologyIso (C : ChainComplex (ModuleCat.{u} R) ℤ)
    (D : ModuleCat.{u} R) (n : ℤ) :
    (tensorCycleComplex C D).homology n ≅
      ModuleCat.of R ((LinearMap.ker (C.d n (n - 1)).hom) ⊗[R] D) :=
  zeroDifferentialHomologyIso _ (tensorCycleComplex_d C D) n

/-- The right end's homology is the tensor product of the previous boundaries and coefficients. -/
def tensorPreviousBoundaryComplexHomologyIso (C : ChainComplex (ModuleCat.{u} R) ℤ)
    (D : ModuleCat.{u} R) (n : ℤ) :
    (tensorPreviousBoundaryComplex C D).homology n ≅
      ModuleCat.of R ((LinearMap.range (C.d n (n - 1)).hom) ⊗[R] D) :=
  zeroDifferentialHomologyIso _ (tensorPreviousBoundaryComplex_d C D) n

end

end UniversalCoefficient
