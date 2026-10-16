import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.SetTheory.Cardinal.Order

/-!
# Submodules of free modules over a PID, without a rank restriction

Well-order the ambient basis. At each index, choose a vector realizing a
generator of the ideal of leading coordinates of vectors supported up to
that index. The nonzero choices are independent by their leading coordinate,
and span by well-founded elimination of the largest support index.
-/

namespace UniversalCoefficient

open Submodule Module

noncomputable section

variable {R ι : Type*} [CommRing R] [IsDomain R]

/-- A triangular family with nonzero diagonal is linearly independent.
Only finite supports are used here; the index order need not be well-founded. -/
theorem triangular_finsupp_linearIndependent [LinearOrder ι] (A : Set ι)
    (v : A → ι →₀ R) (hv : ∀ i j, i.val < j → v i j = 0)
    (hd : ∀ i, v i i.val ≠ 0) : LinearIndependent R v := by
  classical
  rw [linearIndependent_iff]
  intro l hl
  by_contra hne
  have hs := Finsupp.support_nonempty_iff.mpr hne
  let i := l.support.max' hs
  have hi : i ∈ l.support := l.support.max'_mem hs
  have he := congrArg (fun x : ι →₀ R => x i.val) hl
  change (∑ j ∈ l.support, l j • v j) i.val = 0 at he
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul] at he
  have he' : ∑ j ∈ l.support, l j * v j i.val = l i * v i i.val := by
    apply Finset.sum_eq_single i
    · intro j hj hji
      have hlt : j.val < i.val :=
        lt_of_le_of_ne (l.support.le_max' j hj) (by
          intro h
          exact hji (Subtype.ext h))
      rw [hv j i.val hlt, mul_zero]
    · exact fun h => (h hi).elim
  rw [he'] at he
  exact (mul_ne_zero (Finsupp.mem_support_iff.mp hi) (hd i)) he

variable [IsPrincipalIdealRing R]

/-- A submodule of a well-ordered direct sum of copies of a PID is free. -/
theorem finsupp_submodule_free_of_pid [LinearOrder ι] [WellFoundedLT ι]
    (N : Submodule R (ι →₀ R)) : Module.Free R N := by
  classical
  let I : ι → Ideal R := fun i =>
    (N ⊓ Finsupp.supported R R (Set.Iic i)).map (Finsupp.lapply i)
  have hex : ∀ i, ∃ x : ι →₀ R, x ∈ N ∧
      (∀ j, i < j → x j = 0) ∧ x i = Submodule.IsPrincipal.generator (I i) := by
    intro i
    have hm := Submodule.IsPrincipal.generator_mem (I i)
    obtain ⟨x, hx, hxi⟩ := hm
    refine ⟨x, hx.1, ?_, hxi⟩
    intro j hj
    exact (Finsupp.mem_supported' R x).mp hx.2 j (not_le.mpr hj)
  choose x hxN hxbound hxdiag using hex
  let A : Set ι := {i | I i ≠ ⊥}
  let v : A → N := fun i => ⟨x i.val, hxN i.val⟩
  have hvdiag : ∀ i : A, (v i).val i.val ≠ 0 := by
    intro i
    change x i.val i.val ≠ 0
    rw [hxdiag]
    exact fun h => i.property ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero _).mpr h)
  have hli : LinearIndependent R v := by
    apply LinearIndependent.of_comp N.subtype
    apply triangular_finsupp_linearIndependent A
    · exact fun i j hij => hxbound i.val j hij
    · exact hvdiag
  let P := Submodule.span R (Set.range v)
  have hspan : ∀ i, ∀ y : N, (∀ j, i < j → y.val j = 0) → y ∈ P := by
    intro i
    refine (wellFounded_lt : WellFounded ((· < ·) : ι → ι → Prop)).induction
      (C := fun i => ∀ y : N, (∀ j, i < j → y.val j = 0) → y ∈ P) i ?_
    intro i ih
    have lower : ∀ y : N, (∀ j, i < j → y.val j = 0) → y.val i = 0 → y ∈ P := by
      intro y hy hyi
      by_cases hz : y = 0
      · simp [hz]
      have hne : y.val ≠ 0 := by
        intro h
        exact hz (Subtype.ext h)
      have hs := Finsupp.support_nonempty_iff.mpr hne
      let j := y.val.support.max' hs
      have hjmem : j ∈ y.val.support := y.val.support.max'_mem hs
      have hjne : y.val j ≠ 0 := Finsupp.mem_support_iff.mp hjmem
      have hji : j < i := by
        apply lt_of_le_of_ne
        · by_contra h
          exact hjne (hy j (lt_of_not_ge h))
        · intro h
          exact hjne (by simpa [h] using hyi)
      apply ih j hji y
      intro k hjk
      apply Finsupp.notMem_support_iff.mp
      intro hk
      exact (not_lt_of_ge (y.val.support.le_max' k hk)) hjk
    intro y hy
    have hymem : y.val i ∈ I i := by
      refine ⟨y.val, ⟨y.property, ?_⟩, rfl⟩
      apply (Finsupp.mem_supported' R y.val).mpr
      intro j hj
      exact hy j (lt_of_not_ge hj)
    by_cases hi : I i = ⊥
    · apply lower y hy
      simpa [hi] using hymem
    obtain ⟨r, hr⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator (I i)).mp hymem
    let a : A := ⟨i, hi⟩
    have hres : y - r • v a ∈ P := by
      apply lower
      · intro j hij
        change y.val j - r * x i j = 0
        rw [hy j hij, hxbound i j hij, mul_zero, sub_self]
      · change y.val i - r * x i i = 0
        rw [hxdiag, hr]
        exact sub_self _
    have hva : v a ∈ P := Submodule.subset_span (Set.mem_range_self a)
    have hadd := P.add_mem hres (P.smul_mem r hva)
    have hcancel : y - r • v a + r • v a = y := by
      apply Subtype.ext
      ext j
      change y.val j - r * (v a).val j + r * (v a).val j = y.val j
      exact sub_add_cancel _ _
    exact hcancel ▸ hadd
  have htop : ⊤ ≤ P := by
    intro y _
    by_cases hz : y = 0
    · simp [hz]
    have hne : y.val ≠ 0 := fun h => hz (Subtype.ext h)
    have hs := Finsupp.support_nonempty_iff.mpr hne
    apply hspan (y.val.support.max' hs) y
    intro j hj
    apply Finsupp.notMem_support_iff.mp
    intro hmem
    exact (not_lt_of_ge (y.val.support.le_max' j hmem)) hj
  exact Module.Free.of_basis (Basis.mk hli htop)

/-- Every submodule of an arbitrary-rank free module over a PID is free. -/
theorem submodule_free_of_pid {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Free R M] (N : Submodule R M) : Module.Free R N := by
  classical
  let b := Module.Free.chooseBasis R M
  obtain ⟨lo, hw⟩ := exists_wellFoundedLT (Module.Free.ChooseBasisIndex R M)
  let := lo
  let := hw
  have : Module.Free R (N.map b.repr.toLinearMap) :=
    finsupp_submodule_free_of_pid _
  exact Module.Free.of_equiv (b.repr.submoduleMap N).symm

end

end UniversalCoefficient
