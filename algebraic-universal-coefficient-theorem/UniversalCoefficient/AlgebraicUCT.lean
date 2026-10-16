import UniversalCoefficient.UCTSplitting
import UniversalCoefficient.UCTIdentification

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace UniversalCoefficient
noncomputable section
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (C : ChainComplex (ModuleCat.{u} R) ℤ) (D : ModuleCat.{u} R)
    [∀ n, Module.Free R (C.X n)]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Connecting maps respect an explicit equality of target degrees. -/
theorem connecting_target_transport (i j k : ℤ)
    (hij : (ComplexShape.down ℤ).Rel i j) (hik : (ComplexShape.down ℤ).Rel i k)
    (h : j = k) :
    (tensorCyclesSequence_shortExact C D).δ i j hij ≫
      eqToHom (congrArg (fun t => (tensorCyclesSequence C D).X₁.homology t) h) =
        (tensorCyclesSequence_shortExact C D).δ i k hik := by
  subst k
  simp

/-- Cokernel of a connecting map, with its literal target degree. -/
def tensorConnectingCokernelIso (n : ℤ) :
    cokernel (tensorConnecting C D n) ≅ ModuleCat.of R ((C.homology (n-1)) ⊗[R] D) := by
  let b := (tensorRight D).map (ModuleCat.ofHom (boundaryToCycles C n))
  have w : tensorConnecting C D n ≫ (tensorCycleComplexHomologyIso C D (n-1)).hom =
      (tensorPreviousBoundaryComplexHomologyIso C D n).hom ≫ b := by
    have h := congrArg (fun f => (tensorPreviousBoundaryComplexHomologyIso C D n).hom ≫ f)
      (tensorConnecting_formula C D n)
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h
  exact cokernel.mapIso (tensorConnecting C D n) b
    (tensorPreviousBoundaryComplexHomologyIso C D n)
    (tensorCycleComplexHomologyIso C D (n-1)) w ≪≫ boundaryTensorCokernelIsoHomology C D n

/-- The left end of the compressed sequence is homology tensored with coefficients. -/
def tensorKernelSequenceLeftIso (n : ℤ) :
    (tensorKernelSequence C D n).X₁ ≅ ModuleCat.of R ((C.homology n) ⊗[R] D) := by
  have hidx : n = n+1-1 := by omega
  let q : (tensorCyclesSequence C D).X₁.homology n ≅
      (tensorCyclesSequence C D).X₁.homology (n+1-1) :=
    eqToIso (congrArg (fun t => (tensorCyclesSequence C D).X₁.homology t) hidx)
  have w : tensorPreviousConnecting C D n ≫ q.hom =
      (𝟙 _) ≫ tensorConnecting C D (n+1) := by
    simpa only [tensorPreviousConnecting, tensorConnecting, q, eqToIso.hom,
      Category.id_comp] using connecting_target_transport C D (n+1) n (n+1-1) _ _ hidx
  exact cokernel.mapIso (tensorPreviousConnecting C D n) (tensorConnecting C D (n+1))
    (Iso.refl _) q w ≪≫ tensorConnectingCokernelIso C D (n+1) ≪≫
    (tensorRight D).mapIso (eqToIso (congrArg (fun k => C.homology k) hidx.symm))

/-- The right end is the standard library Tor functor derived in its first variable. -/
def tensorKernelSequenceRightIso (n : ℤ) :
    (tensorKernelSequence C D n).X₃ ≅
      (((Tor' (ModuleCat R) 1).obj (C.homology (n - 1))).obj D) := by
  let b := (tensorRight D).map (ModuleCat.ofHom (boundaryToCycles C n))
  have w : tensorConnecting C D n ≫ (tensorCycleComplexHomologyIso C D (n - 1)).hom =
      (tensorPreviousBoundaryComplexHomologyIso C D n).hom ≫ b := by
    have h := congrArg (fun f => (tensorPreviousBoundaryComplexHomologyIso C D n).hom ≫ f)
      (tensorConnecting_formula C D n)
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h
  exact kernel.mapIso (tensorConnecting C D n) b (tensorPreviousBoundaryComplexHomologyIso C D n)
    (tensorCycleComplexHomologyIso C D (n - 1)) w ≪≫ boundaryTensorKernelIsoTor C D n

/-- The canonical algebraic universal coefficient sequence. `Tor'` is Mathlib's
standard Tor obtained by deriving the first (homology) variable. -/
def algebraicUCT (n : ℤ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk
    ((tensorKernelSequenceLeftIso C D n).inv ≫ (tensorKernelSequence C D n).f)
    ((tensorKernelSequence C D n).g ≫ (tensorKernelSequenceRightIso C D n).hom)
    (by simp only [Category.assoc, ShortComplex.zero_assoc, zero_comp, comp_zero])

/-- Comparison to the compressed long exact sequence; the middle object is unchanged. -/
def algebraicUCTIso (n : ℤ) : tensorKernelSequence C D n ≅ algebraicUCT C D n :=
  ShortComplex.isoMk (tensorKernelSequenceLeftIso C D n) (Iso.refl _)
    (tensorKernelSequenceRightIso C D n) (by simp [algebraicUCT]) (by simp [algebraicUCT])

/-- Algebraic UCT over a PID, for arbitrary-rank free chains and arbitrary coefficients. -/
theorem algebraicUCT_shortExact (n : ℤ) : (algebraicUCT C D n).ShortExact :=
  ShortComplex.shortExact_of_iso (algebraicUCTIso C D n) (tensorKernelSequence_shortExact C D n)

/-- A choice of splitting of the algebraic UCT. No naturality of this choice is claimed. -/
def algebraicUCTSplitting (n : ℤ) : (algebraicUCT C D n).Splitting :=
  (tensorKernelSequenceSplitting C D n).ofIso (algebraicUCTIso C D n)

/-- The three literal objects in the UCT, stated independently of the construction. -/
theorem algebraicUCT_objects (n : ℤ) :
    (algebraicUCT C D n).X₁ = ModuleCat.of R ((C.homology n) ⊗[R] D) ∧
    (algebraicUCT C D n).X₂ = ((tensorChainFunctor D).obj C).homology n ∧
    (algebraicUCT C D n).X₃ = (((Tor' (ModuleCat R) 1).obj (C.homology (n-1))).obj D) :=
  ⟨rfl, rfl, rfl⟩

/-- The classical algebraic UCT, with all three objects written explicitly. -/
theorem algebraic_uct (n : ℤ) :
    ∃ (ι : ModuleCat.of R ((C.homology n) ⊗[R] D) ⟶
        ((tensorChainFunctor D).obj C).homology n)
      (π : ((tensorChainFunctor D).obj C).homology n ⟶
        (((Tor' (ModuleCat R) 1).obj (C.homology (n-1))).obj D))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact ∧ Nonempty (ShortComplex.mk ι π h).Splitting :=
  ⟨(algebraicUCT C D n).f, (algebraicUCT C D n).g, (algebraicUCT C D n).zero,
    algebraicUCT_shortExact C D n, ⟨algebraicUCTSplitting C D n⟩⟩

/-- The noncanonical direct-sum form of the algebraic UCT. -/
def algebraicUCTDirectSumIso (n : ℤ) :
    ((tensorChainFunctor D).obj C).homology n ≅
      biprod (ModuleCat.of R ((C.homology n) ⊗[R] D))
        (((Tor' (ModuleCat R) 1).obj (C.homology (n-1))).obj D) :=
  (algebraicUCTSplitting C D n).isoBinaryBiproduct

end
end UniversalCoefficient
