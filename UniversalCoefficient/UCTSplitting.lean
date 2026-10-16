import UniversalCoefficient.FiveTerm
import UniversalCoefficient.ConnectingFormula
import UniversalCoefficient.DegreewiseSplitting
import UniversalCoefficient.PIDFree

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace UniversalCoefficient
noncomputable section
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (C : ChainComplex (ModuleCat.{u} R) ℤ) (D : ModuleCat.{u} R)
    [∀ n, Module.Free R (C.X n)]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The preceding connecting map, with its target written in exactly degree `n`. -/
def tensorPreviousConnecting (n : ℤ) :
    (tensorCyclesSequence C D).X₃.homology (n+1) ⟶
      (tensorCyclesSequence C D).X₁.homology n :=
  (tensorCyclesSequence_shortExact C D).δ (n+1) n (by change n+1=n+1; rfl)

/-- The compressed homology sequence, before identifying its end terms as tensor and Tor. -/
def tensorKernelSequence (n : ℤ) : ShortComplex (ModuleCat R) :=
  fiveTermShortComplex (tensorPreviousConnecting C D n)
    (HomologicalComplex.homologyMap (tensorCyclesSequence C D).f n)
    (HomologicalComplex.homologyMap (tensorCyclesSequence C D).g n)
    (tensorConnecting C D n)
    ((tensorCyclesSequence_shortExact C D).δ_comp (n+1) n _)
    (by rw [← HomologicalComplex.homologyMap_comp, (tensorCyclesSequence C D).zero,
      HomologicalComplex.homologyMap_zero])
    (comp_tensorConnecting C D n)

theorem tensorKernelSequence_shortExact (n : ℤ) :
    (tensorKernelSequence C D n).ShortExact :=
  fiveTermShortComplex_shortExact _ _ _ _ _ _ _
    ((tensorCyclesSequence_shortExact C D).homology_exact₁ (n+1) n _)
    (tensorHomology_exact₂ C D n) (tensorHomology_exact₃ C D n)

/-- A choice of section of the tensor boundary projection in a single degree. -/
def tensorBoundarySection (n : ℤ) :
    (tensorCyclesSequence C D).X₃.X n ⟶ (tensorCyclesSequence C D).X₂.X n := by
  letI : Module.Free R (LinearMap.range (C.d n (n-1)).hom) :=
    submodule_free_of_pid _
  exact ((kernelImageSplitting (C.d n (n-1)).hom).map (tensorRight D)).s

@[reassoc (attr := simp)] theorem tensorBoundarySection_comp (n : ℤ) :
    tensorBoundarySection C D n ≫ (tensorCyclesSequence C D).g.f n = 𝟙 _ := by
  unfold tensorBoundarySection
  exact ShortComplex.Splitting.s_g _

/-- Restrict a chosen boundary section to the kernel of the connecting map. -/
def tensorKernelLift (n : ℤ) :
    kernel (tensorConnecting C D n) ⟶ (tensorCyclesSequence C D).X₂.X n :=
  kernel.ι _ ≫ (tensorPreviousBoundaryComplexHomologyIso C D n).hom ≫
    tensorBoundarySection C D n

 theorem tensorKernelLift_d (n : ℤ) :
    tensorKernelLift C D n ≫ (tensorCyclesSequence C D).X₂.d n (n-1) = 0 := by
  let b := (tensorRight D).map (ModuleCat.ofHom (boundaryToCycles C n))
  have hδ : (tensorPreviousBoundaryComplexHomologyIso C D n).hom ≫ b =
      tensorConnecting C D n ≫ (tensorCycleComplexHomologyIso C D (n-1)).hom := by
    have h := congrArg (fun f => (tensorPreviousBoundaryComplexHomologyIso C D n).hom ≫ f)
      (tensorConnecting_formula C D n)
    simpa [Category.assoc, b] using h.symm
  rw [← tensor_boundaryToCycles_factorization C D n]
  simp only [tensorKernelLift, Category.assoc]
  rw [← Category.assoc (tensorBoundarySection C D n), tensorBoundarySection_comp]
  simp only [Category.id_comp]
  change kernel.ι _ ≫ (tensorPreviousBoundaryComplexHomologyIso C D n).hom ≫ b ≫ _ = 0
  rw [← Category.assoc (tensorPreviousBoundaryComplexHomologyIso C D n).hom]
  rw [hδ]
  simp [← Category.assoc]

/-- A (generally nonnatural) section on homology. -/
def tensorKernelSection (n : ℤ) :
    kernel (tensorConnecting C D n) ⟶ (tensorCyclesSequence C D).X₂.homology n :=
  (tensorCyclesSequence C D).X₂.liftCycles (tensorKernelLift C D n) (n-1)
    (by simp) (tensorKernelLift_d C D n) ≫
      (tensorCyclesSequence C D).X₂.homologyπ n

 theorem tensorKernelSection_comp_homologyMap (n : ℤ) :
    tensorKernelSection C D n ≫
      HomologicalComplex.homologyMap (tensorCyclesSequence C D).g n =
        kernel.ι (tensorConnecting C D n) := by
  apply (cancel_mono (tensorPreviousBoundaryComplexHomologyIso C D n).hom).mp
  unfold tensorKernelSection
  simp only [Category.assoc, HomologicalComplex.homologyπ_naturality_assoc]
  rw [← Category.assoc, HomologicalComplex.liftCycles_comp_cyclesMap]
  have h := liftCycles_homologyProjection_zeroDifferentialHomologyIso
    (tensorPreviousBoundaryComplex C D) (tensorPreviousBoundaryComplex_d C D)
    (tensorKernelLift C D n ≫ (tensorCyclesSequence C D).g.f n) (n-1) (by simp)
    (by rw [tensorPreviousBoundaryComplex_d]; simp)
  exact h.trans (by
    simp only [tensorKernelLift, Category.assoc, tensorBoundarySection_comp]
    exact (Category.assoc _ _ _).symm.trans (Category.comp_id _))

/-- The algebraic UCT sequence splits; this choice need not be natural in `C`. -/
def tensorKernelSequenceSplitting (n : ℤ) : (tensorKernelSequence C D n).Splitting := by
  apply ShortComplex.Splitting.ofExactOfSection _ (tensorKernelSequence_shortExact C D n).exact
    (tensorKernelSection C D n)
  · apply (cancel_mono (kernel.ι (tensorConnecting C D n))).mp
    change tensorKernelSection C D n ≫
      kernel.lift (tensorConnecting C D n)
        (HomologicalComplex.homologyMap (tensorCyclesSequence C D).g n) _ ≫
          kernel.ι (tensorConnecting C D n) = _
    simpa only [Category.assoc, kernel.lift_ι, Category.id_comp] using
      tensorKernelSection_comp_homologyMap C D n
  · exact (tensorKernelSequence_shortExact C D n).mono_f

end
end UniversalCoefficient
