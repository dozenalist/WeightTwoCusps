module

public import Dimension.Gamma_0.Index
public import Dimension.Gamma_1.TorsionFree
public import Mathlib.Tactic.LinearCombination

/-! # Absence of elliptic elements in `Γ₀(N)` when `4 ∣ N` -/

@[expose] public section

open scoped MatrixGroups

namespace WeightTwoCusps

/-- The two elementary root obstructions exclude elliptic traces. -/
theorem Gamma0_trace_ne_of_no_roots (N : ℕ)
    (h₂ : ∀ a : ZMod N, a ^ 2 + 1 ≠ 0)
    (h₃ : ∀ a : ZMod N, a ^ 2 + a + 1 ≠ 0)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 1 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ -1 := by
  let a : ZMod N := (γ 0 0 : ℤ)
  let d : ZMod N := (γ 1 1 : ℤ)
  have hc := CongruenceSubgroup.Gamma0_mem.mp hγ
  have hdet : a * d = 1 := by
    have h := congrArg (Int.cast : ℤ → ZMod N) γ.det_coe
    simp only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one,
      hc, mul_zero, sub_zero] at h
    exact h
  have htrace (t : ℤ) (ht : (γ : Matrix (Fin 2) (Fin 2) ℤ).trace = t) :
      a + d = (t : ZMod N) := by
    simpa [Matrix.trace_fin_two, a, d] using congrArg (Int.cast : ℤ → ZMod N) ht
  refine ⟨fun ht => ?_, fun ht => ?_, fun ht => ?_⟩
  · apply h₂ a
    have htr := htrace 0 ht
    linear_combination a * htr - hdet
  · apply h₃ (-a)
    have htr := htrace 1 ht
    linear_combination a * htr - hdet
  · apply h₃ a
    have htr := htrace (-1) ht
    linear_combination a * htr - hdet

/-- At level four every invertible residue is a sign, so the projective groups agree. -/
theorem Gamma0_four_eq_projectiveClosure_Gamma1_four :
    CongruenceSubgroup.Gamma0 4 = projectiveClosure (CongruenceSubgroup.Gamma1 4) := by
  apply le_antisymm
  · intro γ hγ
    have hc := CongruenceSubgroup.Gamma0_mem.mp hγ
    have hdet := congrArg (Int.cast : ℤ → ZMod 4) γ.det_coe
    simp only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one,
      hc, mul_zero, sub_zero] at hdet
    have hsign : ∀ a d : ZMod 4, a * d = 1 →
        (a = 1 ∧ d = 1) ∨ (a = -1 ∧ d = -1) := by decide
    apply (mem_projectiveClosure_iff _ γ).mpr
    rcases hsign _ _ hdet with h | h
    · left
      exact (CongruenceSubgroup.Gamma1_mem 4 γ).mpr ⟨h.1, h.2, hc⟩
    · right
      rw [CongruenceSubgroup.Gamma1_mem]
      simpa [h.1, h.2, hc]
  · apply sup_le (CongruenceSubgroup.Gamma1_in_Gamma0 4)
    apply Subgroup.zpowers_le.mpr
    rw [CongruenceSubgroup.Gamma0_mem]
    simp

theorem Gamma0_le_Gamma0_four (N : ℕ) (hN : 4 ∣ N) :
    CongruenceSubgroup.Gamma0 N ≤ CongruenceSubgroup.Gamma0 4 := by
  intro γ hγ
  rw [CongruenceIndex.mem_Gamma0_iff_dvd] at hγ ⊢
  exact dvd_trans (Int.natCast_dvd_natCast.mpr hN) hγ

/-- Multiples of four have no elliptic elements in `Γ₀(N)`. -/
theorem Gamma0_trace_ne_of_four_dvd (N : ℕ) (hN : 4 ∣ N) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 1 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ -1 := by
  apply projectiveClosure_Gamma1_trace_ne 4 (by decide) γ
  rw [← Gamma0_four_eq_projectiveClosure_Gamma1_four]
  exact Gamma0_le_Gamma0_four N hN hγ

end WeightTwoCusps
