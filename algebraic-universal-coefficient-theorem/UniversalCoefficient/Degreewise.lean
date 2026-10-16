import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The degreewise kernel–image exact sequence

For an arbitrary homomorphism of abelian groups, this constructs the standard
short exact sequence `0 → ker f → M → range f → 0`.  Applied to a chain
differential it is the degreewise sequence underlying the homological
universal coefficient theorem.  No freeness assumption is needed here.
-/

namespace UniversalCoefficient

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u v

variable {R : Type v} {M N : Type u} [Ring R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]

/-- The kernel inclusion and the differential with codomain restricted to its image. -/
def kernelImageShortComplex (f : M →ₗ[R] N) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk f.ker.subtype f.rangeRestrict (by
    apply LinearMap.ext
    intro x
    exact Subtype.ext x.property)

/-- Each differential gives a short exact sequence from its kernel to its image. -/
theorem kernelImageShortComplex_shortExact (f : M →ₗ[R] N) :
    (kernelImageShortComplex f).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · intro x
    constructor
    · intro hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      exact congrArg Subtype.val hx
    · rintro ⟨y, rfl⟩
      apply Subtype.ext
      exact y.property
  · exact f.ker.injective_subtype
  · rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩

end UniversalCoefficient
