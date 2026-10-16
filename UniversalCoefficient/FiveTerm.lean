import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Basic

open CategoryTheory CategoryTheory.Limits

namespace UniversalCoefficient
noncomputable section

variable {V : Type*} [Category V] [Abelian V]
  {A B H D E : V} (a : A ⟶ B) (b : B ⟶ H) (c : H ⟶ D) (d : D ⟶ E)
  (hab : a ≫ b = 0) (hbc : b ≫ c = 0) (hcd : c ≫ d = 0)

/-- Compress five exact terms to cokernel–middle–kernel. -/
def fiveTermShortComplex : ShortComplex V :=
  ShortComplex.mk (cokernel.desc a b hab) (kernel.lift d c hcd) (by
    apply (cancel_epi (cokernel.π a)).mp
    apply (cancel_mono (kernel.ι d)).mp
    simp [Category.assoc, hbc])

theorem fiveTermShortComplex_shortExact
    (h₁ : (ShortComplex.mk a b hab).Exact)
    (h₂ : (ShortComplex.mk b c hbc).Exact)
    (h₃ : (ShortComplex.mk c d hcd).Exact) :
    (fiveTermShortComplex a b c d hab hbc hcd).ShortExact := by
  have hdesc : cokernel.desc a b hab ≫ c = 0 := by
    apply (cancel_epi (cokernel.π a)).mp
    simpa using hbc
  let T := ShortComplex.mk (cokernel.desc a b hab) c hdesc
  let φ : ShortComplex.mk b c hbc ⟶ T :=
    { τ₁ := cokernel.π a
      τ₂ := 𝟙 H
      τ₃ := 𝟙 D
      comm₁₂ := by simp [T]
      comm₂₃ := by simp [T] }
  have hT : T.Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp h₂
  let ψ : fiveTermShortComplex a b c d hab hbc hcd ⟶ T :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 H
      τ₃ := kernel.ι d
      comm₁₂ := by simp [fiveTermShortComplex, T]
      comm₂₃ := by simp [fiveTermShortComplex, T] }
  have : Epi ψ.τ₁ := inferInstanceAs (Epi (𝟙 (cokernel a)))
  have : IsIso ψ.τ₂ := inferInstanceAs (IsIso (𝟙 H))
  have : Mono ψ.τ₃ := inferInstanceAs (Mono (kernel.ι d))
  exact
    { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).mpr hT
      mono_f := h₁.mono_cokernelDesc
      epi_g := h₃.epi_kernelLift }

end
end UniversalCoefficient
