module

public import Dimension.Gamma_1.Basic
public import Dimension.Gamma_1.TorsionFree
public import Dimension.GroupTheory.ParabolicRank

@[expose] public section

/-! # The period upper bound for weight-two `Γ₁(N)` cusp forms -/

noncomputable section

open scoped MatrixGroups

namespace WeightTwoCusps

/-- The actual cusp count expressed as a finite orbit cardinal. -/
abbrev gamma1GeometricCuspCount (N : ℕ) : ℕ :=
  Nat.card (subgroupCusps (projectiveClosure (CongruenceSubgroup.Gamma1 N)))

/-- The period argument gives the genus bound for every `N ≥ 4`.
Identifying the cusp orbit cardinal with the divisor sum is a separate step. -/
theorem gamma1CuspForms_dimension_upper_bound (N : ℕ) (hN : 4 ≤ N) :
    2 * Module.finrank ℂ (gamma1CuspForms N) + gamma1GeometricCuspCount N ≤
      2 + gamma1ProjectiveIndex N / 6 := by
  letI : NeZero N := ⟨by omega⟩
  change 2 * Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma1 N) 2) +
    gamma1GeometricCuspCount N ≤ 2 + gamma1ProjectiveIndex N / 6
  rw [weightTwoCuspForms_finrank_projectiveClosure]
  exact weightTwoCuspForms_dimension_upper_bound_of_trace_ne _
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) (projectiveClosure_Gamma1_trace_ne N hN)

end WeightTwoCusps
