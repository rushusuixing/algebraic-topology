import UniversalCoefficient.HomologyPresentation

open CategoryTheory

namespace UniversalCoefficient
noncomputable section
universe u v
variable {R : Type v} [Ring R] (S : ShortComplex (ModuleCat.{u} R))
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Identifies the image inside the cycles with the image inside the ambient module. -/
def boundaryRangeEquiv : LinearMap.range S.moduleCatToCycles ≃ₗ[R] LinearMap.range S.f.hom where
  toFun x := ⟨x.val.val, by
    obtain ⟨a, ha⟩ := x.property
    exact ⟨a, congrArg Subtype.val ha⟩⟩
  invFun y := ⟨⟨y.val, by
    obtain ⟨a, ha⟩ := y.property
    rw [← ha]
    exact S.moduleCat_zero_apply a⟩, by
      obtain ⟨a, ha⟩ := y.property
      exact ⟨a, Subtype.ext ha⟩⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl
  map_add' x y := rfl
  map_smul' r x := rfl

/-- The actual ambient boundary image included in the kernel of the outgoing differential. -/
def boundaryInclusion : LinearMap.range S.f.hom →ₗ[R] LinearMap.ker S.g.hom :=
  S.moduleCatToCycles.range.subtype.comp (boundaryRangeEquiv S).symm.toLinearMap

@[simp] theorem boundaryInclusion_val (x : LinearMap.range S.f.hom) :
    (boundaryInclusion S x).val = x.val := rfl

/-- The homology presentation with boundaries represented in the ambient module. -/
def ambientHomologyPresentation : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk (boundaryInclusion S) (homologyPresentation S).g.hom (by
    ext x
    have h := congrArg (fun f => f.hom ((boundaryRangeEquiv S).symm x))
      (homologyPresentation S).zero
    exact h)

theorem ambientHomologyPresentation_shortExact : (ambientHomologyPresentation S).ShortExact := by
  have h := homologyPresentation_shortExact S
  have he : Function.Exact (homologyPresentation S).f (homologyPresentation S).g :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp h.exact
  apply ModuleCat.shortComplex_shortExact
  · intro x
    change (homologyPresentation S).g x = 0 ↔ ∃ y, boundaryInclusion S y = x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := (he x).mp hx
      refine ⟨boundaryRangeEquiv S y, ?_⟩
      change y.val = x at hy
      change ((boundaryRangeEquiv S).symm (boundaryRangeEquiv S y)).val = x
      simpa only [LinearEquiv.symm_apply_apply] using hy
    · rintro ⟨y, rfl⟩
      exact (he _).mpr ⟨(boundaryRangeEquiv S).symm y, rfl⟩
  · exact S.moduleCatToCycles.range.injective_subtype.comp (boundaryRangeEquiv S).symm.injective
  · exact h.moduleCat_surjective_g

end
end UniversalCoefficient
