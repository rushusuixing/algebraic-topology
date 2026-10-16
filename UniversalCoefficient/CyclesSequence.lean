import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import UniversalCoefficient.Degreewise

open CategoryTheory

namespace UniversalCoefficient

noncomputable section

variable {R : Type*} [CommRing R] (C : ChainComplex (ModuleCat R) ℤ)

/-- The graded cycles, regarded as a complex with zero differential. -/
def cycleComplex : ChainComplex (ModuleCat R) ℤ where
  X n := ModuleCat.of R (LinearMap.ker (C.d n (n - 1)).hom)
  d _ _ := 0

/-- Degree `n` is the image of `d_n`, namely the boundaries in degree `n-1`.
This is an explicitly reindexed zero-differential complex, not a claim about
the sign convention of Mathlib's categorical shift. -/
def previousBoundaryComplex : ChainComplex (ModuleCat R) ℤ where
  X n := ModuleCat.of R (LinearMap.range (C.d n (n - 1)).hom)
  d _ _ := 0

def cyclesInclusion : cycleComplex C ⟶ C where
  f n := ModuleCat.ofHom (LinearMap.ker (C.d n (n - 1)).hom).subtype
  comm' i j hij := by
    have hji : j = i - 1 := by
      change j + 1 = i at hij
      omega
    subst j
    apply ModuleCat.hom_ext
    ext x
    exact x.property

def differentialToBoundaries : C ⟶ previousBoundaryComplex C where
  f n := ModuleCat.ofHom (C.d n (n - 1)).hom.rangeRestrict
  comm' i j _ := by
    apply ModuleCat.hom_ext
    ext x
    apply Subtype.ext
    change 0 = C.d j (j - 1) (C.d i j x)
    have h := congrArg (fun f => f.hom x) (C.d_comp_d i j (j - 1))
    exact h.symm

/-- The canonical sequence `0 → Z(C) → C → B(C)[-1] → 0`, prior to
tensoring. Exactness is established degreewise. -/
def cyclesSequence : ShortComplex (ChainComplex (ModuleCat R) ℤ) :=
  ShortComplex.mk (cyclesInclusion C) (differentialToBoundaries C) (by
    ext n x
    apply Subtype.ext
    exact x.property)

theorem cyclesSequence_shortExact : (cyclesSequence C).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact kernelImageShortComplex_shortExact (C.d n (n - 1)).hom

end

end UniversalCoefficient
