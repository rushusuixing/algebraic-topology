import UniversalCoefficient.CyclesSequence
import Mathlib.Algebra.Category.ModuleCat.Projective

open CategoryTheory

namespace UniversalCoefficient

noncomputable section

universe u v

variable {R : Type v} [CommRing R]

/-- This intermediate construction uses projectivity only of the image, not of
its ambient module. For the final free-chain theorem this hypothesis must be
proved for every boundary module over a PID. -/
def kernelImageSplitting {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N)
    [Module.Projective R (LinearMap.range f)] :
    (kernelImageShortComplex f).Splitting := by
  letI : CategoryTheory.Projective (kernelImageShortComplex f).X₃ := by
    change CategoryTheory.Projective (ModuleCat.of R (LinearMap.range f))
    infer_instance
  exact (kernelImageShortComplex_shortExact f).splittingOfProjective

/-- A degreewise splitting; these choices need not commute with differentials. -/
def cyclesSequenceDegreewiseSplitting (C : ChainComplex (ModuleCat R) ℤ)
    [∀ n, Module.Projective R (LinearMap.range (C.d n (n - 1)).hom)] (n : ℤ) :
    ((cyclesSequence C).map (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℤ) n)).Splitting :=
  kernelImageSplitting (C.d n (n - 1)).hom

end
end UniversalCoefficient
