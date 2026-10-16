import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

open CategoryTheory

namespace UniversalCoefficient
noncomputable section
universe u v
variable {R : Type v} [Ring R] (S : ShortComplex (ModuleCat.{u} R))
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The canonical boundary–cycle–homology sequence, using Mathlib's standard homology. -/
def homologyPresentation : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk S.moduleCatToCycles.range.subtype
    (S.moduleCatHomologyIso.inv.hom.comp S.moduleCatToCycles.range.mkQ) (by
      ext x
      change S.moduleCatHomologyIso.inv.hom (S.moduleCatToCycles.range.mkQ x.val) = 0
      have hq : S.moduleCatToCycles.range.mkQ x.val = 0 := (Submodule.Quotient.mk_eq_zero _).mpr x.property
      exact (congrArg S.moduleCatHomologyIso.inv.hom hq).trans (map_zero _))

theorem homologyPresentation_shortExact : (homologyPresentation S).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · intro x
    change S.moduleCatHomologyIso.inv.hom (S.moduleCatToCycles.range.mkQ x) = 0 ↔
      ∃ y : S.moduleCatToCycles.range, y.val = x
    have hi : Function.Injective S.moduleCatHomologyIso.inv.hom :=
      (ModuleCat.mono_iff_injective S.moduleCatHomologyIso.inv).mp inferInstance
    constructor
    · intro hx
      have hq : S.moduleCatToCycles.range.mkQ x = 0 := hi (hx.trans (map_zero _).symm)
      exact ⟨⟨x, (Submodule.Quotient.mk_eq_zero _).mp hq⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      have hq : S.moduleCatToCycles.range.mkQ y.val = 0 := (Submodule.Quotient.mk_eq_zero _).mpr y.property
      exact (congrArg S.moduleCatHomologyIso.inv.hom hq).trans (map_zero _)
  · exact S.moduleCatToCycles.range.injective_subtype
  · exact ((ModuleCat.epi_iff_surjective S.moduleCatHomologyIso.inv).mp inferInstance).comp
      S.moduleCatToCycles.range.mkQ_surjective

/-- The boundary–cycle presentation of the standard homology of a chain complex. -/
def chainHomologyPresentation (C : ChainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    ShortComplex (ModuleCat.{u} R) :=
  homologyPresentation (C.sc n)

theorem chainHomologyPresentation_shortExact (C : ChainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (chainHomologyPresentation C n).ShortExact :=
  homologyPresentation_shortExact (C.sc n)

end
end UniversalCoefficient
