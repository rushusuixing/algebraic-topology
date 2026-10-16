import UniversalCoefficient.HomologySequence
import UniversalCoefficient.ZeroDifferential

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Limits

namespace UniversalCoefficient

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

variable {R : Type u} [CommRing R]

/-- A boundary represented by `d_n` is a cycle in degree `n-1`. -/
def boundaryToCycles (C : ChainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    LinearMap.range (C.d n (n - 1)).hom →ₗ[R]
      LinearMap.ker (C.d (n - 1) (n - 1 - 1)).hom :=
  (LinearMap.range (C.d n (n - 1)).hom).subtype.codRestrict _ (by
    rintro ⟨y, x, rfl⟩
    exact congrArg (fun f => f.hom x) (C.d_comp_d n (n - 1) (n - 1 - 1)))

theorem liftCycles_homologyProjection_zeroDifferentialHomologyIso
    (K : ChainComplex (ModuleCat.{u} R) ℤ) (h : ∀ i j, K.d i j = 0)
    {A : ModuleCat.{u} R} {n : ℤ} (x : A ⟶ K.X n) (j : ℤ)
    (hj : (ComplexShape.down ℤ).next n = j) (hx : x ≫ K.d n j = 0) :
    K.liftCycles x j hj hx ≫ K.homologyπ n ≫
      (zeroDifferentialHomologyIso K h n).hom = x := by
  simp [zeroDifferentialHomologyIso]

/-- The degreewise factorization of the differential used in computing the connecting map. -/
theorem tensor_boundaryToCycles_factorization
    (C : ChainComplex (ModuleCat.{u} R) ℤ) (D : ModuleCat.{u} R) (n : ℤ) :
    (tensorCyclesSequence C D).g.f n ≫
      (tensorRight D).map (ModuleCat.ofHom (boundaryToCycles C n)) ≫
      (tensorCyclesSequence C D).f.f (n - 1) =
        (tensorCyclesSequence C D).X₂.d n (n - 1) := by
  change (tensorRight D).map (ModuleCat.ofHom (C.d n (n - 1)).hom.rangeRestrict) ≫
    (tensorRight D).map (ModuleCat.ofHom (boundaryToCycles C n)) ≫
    (tensorRight D).map (ModuleCat.ofHom
      (LinearMap.ker (C.d (n - 1) (n - 1 - 1)).hom).subtype) = _
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

variable [IsDomain R] [IsPrincipalIdealRing R]

/-- Under the canonical identifications of zero-differential homology, the
connecting homomorphism is the inclusion of boundaries into cycles tensored with `D`. -/
theorem tensorConnecting_formula
    (C : ChainComplex (ModuleCat.{u} R) ℤ) (D : ModuleCat.{u} R)
    [∀ n, Module.Free R (C.X n)] (n : ℤ) :
    (tensorPreviousBoundaryComplexHomologyIso C D n).inv ≫ tensorConnecting C D n ≫
      (tensorCycleComplexHomologyIso C D (n - 1)).hom =
      (tensorRight D).map (ModuleCat.ofHom (boundaryToCycles C n)) := by
  let S := tensorCyclesSequence C D
  let hS := tensorCyclesSequence_shortExact C D
  let b := (tensorRight D).map (ModuleCat.ofHom (boundaryToCycles C n))
  have hij : (ComplexShape.down ℤ).Rel n (n - 1) := by
    change n - 1 + 1 = n
    omega
  have := hS.epi_g
  apply (cancel_epi (S.g.f n)).mp
  have h := hS.δ_eq n (n - 1) hij (S.g.f n) (by
    rw [show S.X₃.d n (n - 1) = 0 from tensorPreviousBoundaryComplex_d C D n (n - 1)]
    simp) (𝟙 _) (by dsimp [S]; simp only [Category.id_comp]) (S.g.f n ≫ b)
    (by
      rw [Category.id_comp, Category.assoc]
      exact tensor_boundaryToCycles_factorization C D n)
    ((ComplexShape.down ℤ).next (n - 1)) rfl
  have h' := congrArg (fun f => f ≫ (tensorCycleComplexHomologyIso C D (n - 1)).hom) h
  have hr := liftCycles_homologyProjection_zeroDifferentialHomologyIso
    (tensorCycleComplex C D) (tensorCycleComplex_d C D)
    (S.g.f n ≫ b) _ rfl (by simp [tensorCycleComplex_d])
  have hl := liftCycles_homologyProjection_zeroDifferentialHomologyIso
    (tensorPreviousBoundaryComplex C D) (tensorPreviousBoundaryComplex_d C D)
    (S.g.f n) _ ((ComplexShape.down ℤ).next_eq' hij)
    (by rw [tensorPreviousBoundaryComplex_d]; exact comp_zero)
  have hl' : S.X₃.liftCycles (S.g.f n) (n - 1)
      ((ComplexShape.down ℤ).next_eq' hij) (by
        change S.g.f n ≫ (tensorPreviousBoundaryComplex C D).d n (n - 1) = 0
        rw [tensorPreviousBoundaryComplex_d]
        exact comp_zero) ≫
      S.X₃.homologyπ n = S.g.f n ≫ (tensorPreviousBoundaryComplexHomologyIso C D n).inv := by
    apply (cancel_mono (tensorPreviousBoundaryComplexHomologyIso C D n).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact hl
  rw [← Category.assoc, hl'] at h'
  simpa [tensorConnecting, tensorCycleComplexHomologyIso, S, hS, b, Category.assoc] using
    h'.trans hr

end

end UniversalCoefficient
