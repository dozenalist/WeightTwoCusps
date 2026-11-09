module

public import Dimension.Gamma_0.Basic
public import Dimension.Gamma_0.ProjectiveIndex
public import Dimension.Gamma_0.TorsionFree
public import Dimension.Periods.Descent
public import Dimension.GroupTheory.ParabolicRank

/-! # The exact weight-two `Γ₀(N)` relation in terms of parabolic rank -/

@[expose] public section

noncomputable section

open scoped MatrixGroups

namespace WeightTwoCusps

/-- The actual number of `Γ₀(N)` cusp classes. -/
abbrev gamma0GeometricCuspCount (N : ℕ) : ℕ :=
  Nat.card (subgroupCusps (CongruenceSubgroup.Gamma0 N))

/-- This comparison is unconditional and does not need cusp or elliptic counts. -/
theorem gamma0CuspForms_parabolic_dimension_relation (N : ℕ) (hN : 2 ≤ N) :
    2 * Module.finrank ℂ (gamma0CuspForms N) =
      Module.finrank ℚ (ModularCurve.Period.parabolicHoms ℚ (CongruenceSubgroup.Gamma0 N) ℚ) := by
  letI : NeZero N := ⟨by omega⟩
  apply two_mul_finrank_cuspForms_eq_parabolicHoms_of_Gamma_le _ N hN
  intro γ hγ
  exact CongruenceSubgroup.Gamma0_mem.mpr (CongruenceSubgroup.Gamma_mem.mp hγ).2.2.1

/-- The remaining group-theoretic calculation is the ordinary homomorphism rank. -/
theorem gamma0CuspForms_geometric_dimension_relation (N : ℕ) (hN : 2 ≤ N) :
    2 * Module.finrank ℂ (gamma0CuspForms N) + gamma0GeometricCuspCount N =
      Module.finrank ℚ (Additive (CongruenceSubgroup.Gamma0 N) →+ ℚ) + 1 := by
  letI : NeZero N := ⟨by omega⟩
  rw [gamma0CuspForms_parabolic_dimension_relation N hN]
  exact parabolicHoms_finrank_add_cusps _ (neg_one_mem_Gamma0 N)

/-- The integral genus formula for the infinite family `4 ∣ N`, with geometric cusps. -/
theorem gamma0CuspForms_geometric_dimension_relation_of_trace_ne (N : ℕ) [NeZero N]
    (hN : 2 ≤ N)
    (htrace : ∀ γ ∈ CongruenceSubgroup.Gamma0 N,
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 1 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ -1) :
    12 * Module.finrank ℂ (gamma0CuspForms N) + 6 * gamma0GeometricCuspCount N =
      12 + (CongruenceSubgroup.Gamma0 N).index := by
  have hp := gamma0CuspForms_parabolic_dimension_relation N hN
  have hr := parabolicHoms_finrank_add_cusps_of_trace_ne (CongruenceSubgroup.Gamma0 N)
    (neg_one_mem_Gamma0 N) htrace
  rw [← hp] at hr
  change 2 * Module.finrank ℂ (gamma0CuspForms N) + gamma0GeometricCuspCount N =
    2 + (CongruenceSubgroup.Gamma0 N).index / 6 at hr
  have hdiv := six_dvd_index_of_trace_ne (CongruenceSubgroup.Gamma0 N)
    (neg_one_mem_Gamma0 N) htrace
  have hmul : (CongruenceSubgroup.Gamma0 N).index / 6 * 6 =
      (CongruenceSubgroup.Gamma0 N).index := Nat.div_mul_cancel hdiv
  omega

theorem gamma0CuspForms_geometric_dimension_relation_of_four_dvd (N : ℕ) [NeZero N]
    (hN : 4 ∣ N) :
    12 * Module.finrank ℂ (gamma0CuspForms N) + 6 * gamma0GeometricCuspCount N =
      12 + (CongruenceSubgroup.Gamma0 N).index := by
  have hNfour : 4 ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hN
  exact gamma0CuspForms_geometric_dimension_relation_of_trace_ne N (by omega)
    (Gamma0_trace_ne_of_four_dvd N hN)

end WeightTwoCusps
