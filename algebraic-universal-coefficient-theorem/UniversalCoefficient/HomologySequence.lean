import Mathlib.Algebra.Homology.HomologySequence
import UniversalCoefficient.Tensor

/-!
# The homology sequence after tensoring the cycles sequence

For a degreewise free complex over a PID and arbitrary coefficients, the
short exact sequence of tensor complexes gives a connecting map and three
successive exact pairs. Identifying the connecting map and its kernel with
the usual UCT objects is a subsequent algebraic step.
-/

namespace UniversalCoefficient

open CategoryTheory

noncomputable section

universe u

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (C : ChainComplex (ModuleCat.{u} R) ℤ) (D : ModuleCat.{u} R)
    [∀ n, Module.Free R (C.X n)]

/-- The connecting map lowers the integer degree by one. -/
def tensorConnecting (n : ℤ) :
    (tensorCyclesSequence C D).X₃.homology n ⟶
      (tensorCyclesSequence C D).X₁.homology (n - 1) :=
  (tensorCyclesSequence_shortExact C D).δ n (n - 1) (by
    change n - 1 + 1 = n
    omega)

@[reassoc (attr := simp)]
theorem tensorConnecting_comp (n : ℤ) :
    tensorConnecting C D n ≫
      HomologicalComplex.homologyMap (tensorCyclesSequence C D).f (n - 1) = 0 :=
  (tensorCyclesSequence_shortExact C D).δ_comp n (n - 1) _

@[reassoc (attr := simp)]
theorem comp_tensorConnecting (n : ℤ) :
    HomologicalComplex.homologyMap (tensorCyclesSequence C D).g n ≫
      tensorConnecting C D n = 0 :=
  (tensorCyclesSequence_shortExact C D).comp_δ n (n - 1) _

/-- Exactness at the homology of the tensor of the cycle complex. -/
theorem tensorHomology_exact₁ (n : ℤ) :
    (ShortComplex.mk (tensorConnecting C D n)
      (HomologicalComplex.homologyMap (tensorCyclesSequence C D).f (n - 1))
      (tensorConnecting_comp C D n)).Exact :=
  (tensorCyclesSequence_shortExact C D).homology_exact₁ n (n - 1) _

/-- Exactness at the homology of the original tensor complex. -/
theorem tensorHomology_exact₂ (n : ℤ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (tensorCyclesSequence C D).f n)
      (HomologicalComplex.homologyMap (tensorCyclesSequence C D).g n)
      (by rw [← HomologicalComplex.homologyMap_comp,
        (tensorCyclesSequence C D).zero, HomologicalComplex.homologyMap_zero])).Exact :=
  (tensorCyclesSequence_shortExact C D).homology_exact₂ n

/-- Exactness at the homology of the tensor of the previous-boundary complex. -/
theorem tensorHomology_exact₃ (n : ℤ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (tensorCyclesSequence C D).g n)
      (tensorConnecting C D n) (comp_tensorConnecting C D n)).Exact :=
  (tensorCyclesSequence_shortExact C D).homology_exact₃ n (n - 1) _

end

end UniversalCoefficient
