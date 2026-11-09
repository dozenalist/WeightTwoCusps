module

public import Dimension.Gamma_1.ProjectiveIndex
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

/-! # Absence of elliptic elements in `±Γ₁(N)` for `N ≥ 4` -/

open scoped MatrixGroups

namespace WeightTwoCusps

/-- A matrix in `Γ₁(N)` has trace congruent to two modulo `N`. -/
theorem Gamma1_dvd_two_sub_trace (N : ℕ) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma1 N) :
    (N : ℤ) ∣ 2 - (γ : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  have hdiag := (CongruenceSubgroup.Gamma1_mem N γ).mp hγ
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ 2 N).mp
  simpa [Matrix.trace_fin_two, hdiag.1, hdiag.2.1] using
    (one_add_one_eq_two : (1 : ZMod N) + 1 = 2)

/-- The projective group `Γ₁(N)` has no elliptic elements when `N ≥ 4`. -/
theorem projectiveClosure_Gamma1_trace_ne (N : ℕ) (hN : 4 ≤ N) (γ : SL(2, ℤ))
    (hγ : γ ∈ projectiveClosure (CongruenceSubgroup.Gamma1 N)) :
    (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 1 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ -1 := by
  have base : ∀ g ∈ CongruenceSubgroup.Gamma1 N,
      (g : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 0 ∧
        (g : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 1 ∧
        (g : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ -1 := by
    intro g hg
    have hd := Gamma1_dvd_two_sub_trace N g hg
    refine ⟨fun ht => ?_, fun ht => ?_, fun ht => ?_⟩ <;>
      rw [ht] at hd <;>
      have := Int.le_of_dvd (by norm_num) hd <;>
      omega
  rcases (mem_projectiveClosure_iff _ γ).mp hγ with h | h
  · exact base γ h
  · have hb := base (-γ) h
    rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg] at hb
    omega

end WeightTwoCusps
