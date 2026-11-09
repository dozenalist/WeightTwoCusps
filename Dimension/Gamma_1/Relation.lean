module

public import Dimension.Gamma_1.Periods
public import Dimension.Gamma_1.Index
public import Dimension.Periods.Descent

/-! # The weight-two `Γ₁(N)` relation with the actual cusp orbit count -/

@[expose] public section

noncomputable section

open scoped MatrixGroups

namespace WeightTwoCusps

/-- The exact genus relation before clearing the denominator in the index. -/
theorem gamma1CuspForms_geometric_dimension_relation_aux (N : ℕ) (hN : 4 ≤ N) :
    2 * Module.finrank ℂ (gamma1CuspForms N) + gamma1GeometricCuspCount N =
      2 + gamma1ProjectiveIndex N / 6 := by
  letI : NeZero N := ⟨by omega⟩
  let Γ := projectiveClosure (CongruenceSubgroup.Gamma1 N)
  have hinc : CongruenceSubgroup.Gamma N ≤ Γ :=
    (CongruenceIndex.Gamma_le_Gamma1 N).trans le_sup_left
  have hd := two_mul_finrank_cuspForms_eq_parabolicHoms_of_Gamma_le Γ N (by omega) hinc
  have hr := parabolicHoms_finrank_add_cusps_of_trace_ne Γ
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) (projectiveClosure_Gamma1_trace_ne N hN)
  rw [← hd] at hr
  change 2 * Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma1 N) 2) +
    gamma1GeometricCuspCount N = 2 + gamma1ProjectiveIndex N / 6
  rw [weightTwoCuspForms_finrank_projectiveClosure]
  exact hr

/-- The integral weight-two dimension relation for `Γ₁(N)`, with geometric cusps. -/
theorem gamma1CuspForms_geometric_dimension_relation (N : ℕ) (hN : 4 ≤ N) :
    12 * Module.finrank ℂ (gamma1CuspForms N) + 6 * gamma1GeometricCuspCount N =
      12 + gamma1ProjectiveIndex N := by
  letI : NeZero N := ⟨by omega⟩
  have hr := gamma1CuspForms_geometric_dimension_relation_aux N hN
  have hdiv := six_dvd_index_of_trace_ne (projectiveClosure (CongruenceSubgroup.Gamma1 N))
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) (projectiveClosure_Gamma1_trace_ne N hN)
  have hmul : gamma1ProjectiveIndex N / 6 * 6 = gamma1ProjectiveIndex N :=
    Nat.div_mul_cancel hdiv
  omega

end WeightTwoCusps
