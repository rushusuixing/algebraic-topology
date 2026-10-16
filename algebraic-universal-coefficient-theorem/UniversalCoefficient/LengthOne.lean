import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
open CategoryTheory Limits ZeroObject
namespace UniversalCoefficient
noncomputable section
universe u
variable {R : Type u} [CommRing R] (S : ShortComplex (ModuleCat.{u} R))
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The two-term complex associated to a presentation. -/
def lengthOneComplex : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (fun n => match n with | 0 => S.X₂ | 1 => S.X₁ | _ + 2 => 0)
    (fun n => match n with | 0 => S.f | _ + 1 => 0)
    (by intro n; cases n <;> simp)

@[simp] theorem lengthOneComplex_d₁₀ : (lengthOneComplex S).d 1 0 = S.f := by
  simp [lengthOneComplex, ChainComplex.of.d]
@[simp] theorem lengthOneComplex_d_succ (n : ℕ) :
    (lengthOneComplex S).d (n + 2) (n + 1) = 0 := by
  simp [lengthOneComplex, ChainComplex.of.d]

/-- The augmentation of the two-term presentation complex. -/
def lengthOneAugmentation : lengthOneComplex S ⟶ (ChainComplex.single₀ _).obj S.X₃ :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨S.g, by simp⟩

@[simp] theorem lengthOneAugmentation_f_zero : (lengthOneAugmentation S).f 0 = S.g := by
  apply ChainComplex.toSingle₀Equiv_symm_apply_f_zero

 theorem lengthOneComplex_exact_succ (hS : S.ShortExact) (n : ℕ) :
    (lengthOneComplex S).ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)]
  cases n with
  | zero =>
    rw [ShortComplex.exact_iff_mono _ (by simp)]
    simpa using hS.mono_f
  | succ n =>
    apply ShortComplex.exact_of_isZero_X₂
    change IsZero (0 : ModuleCat R)
    apply isZero_zero

 theorem lengthOneAugmentation_quasiIso (hS : S.ShortExact) :
    QuasiIso (lengthOneAugmentation S) := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff]
    rw [ShortComplex.quasiIso_iff_of_zeros' _ (by simp) (by simp) (by simp)]
    constructor
    · simpa [HomologicalComplex.shortComplexFunctor', HomologicalComplex.sc',
        lengthOneAugmentation_f_zero, lengthOneComplex, ChainComplex.of.d] using hS.exact
    · simpa using hS.epi_g
  | succ n =>
    rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)]
    exact lengthOneComplex_exact_succ S hS n

/-- A genuinely short exact presentation by projectives gives a length-one resolution. -/
def lengthOneResolution (hS : S.ShortExact) [Projective S.X₁] [Projective S.X₂] :
    ProjectiveResolution S.X₃ where
  complex := lengthOneComplex S
  projective n := by
    cases n with
    | zero => exact inferInstanceAs (Projective S.X₂)
    | succ n => cases n with
      | zero => exact inferInstanceAs (Projective S.X₁)
      | succ n => exact IsZero.projective (isZero_zero _)
  π := lengthOneAugmentation S
  quasiIso := lengthOneAugmentation_quasiIso S hS

/-- Tor computed from an arbitrary short exact presentation by projectives. -/
def torOneIsoKernel (hS : S.ShortExact) [Projective S.X₁] [Projective S.X₂]
    (D : ModuleCat R) :
    (((Tor' (ModuleCat R) 1).obj S.X₃).obj D) ≅
      kernel ((MonoidalCategory.tensorRight D).map S.f) := by
  let F := MonoidalCategory.tensorRight D
  let K := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (lengthOneComplex S)
  refine (lengthOneResolution S hS).isoLeftDerivedObj F 1 ≪≫ ?_
  change K.homology 1 ≅ _
  refine K.homologyIsoSc' 2 1 0 (by simp) (by simp) ≪≫ ?_
  have hf : (K.sc' 2 1 0).f = 0 := by
    change F.map ((lengthOneComplex S).d 2 1) = 0
    simp
  refine (ShortComplex.LeftHomologyData.ofHasKernel (K.sc' 2 1 0) hf).homologyIso ≪≫ ?_
  change kernel (F.map ((lengthOneComplex S).d 1 0)) ≅ kernel (F.map S.f)
  rw [lengthOneComplex_d₁₀]

/-- The same comparison, with the ordinary linear kernel as target. -/
def torOneIsoLinearKernel (hS : S.ShortExact) [Projective S.X₁] [Projective S.X₂]
    (D : ModuleCat R) :
    (((Tor' (ModuleCat R) 1).obj S.X₃).obj D) ≅
      ModuleCat.of R (((MonoidalCategory.tensorRight D).map S.f).hom.ker) :=
  torOneIsoKernel S hS D ≪≫ ModuleCat.kernelIsoKer _

end
end UniversalCoefficient
