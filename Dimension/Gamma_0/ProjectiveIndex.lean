module

public import Dimension.Gamma_0.Index
public import Dimension.GroupTheory.ProjectiveSubgroup

@[expose] public section

open scoped MatrixGroups

namespace WeightTwoCusps

theorem neg_one_mem_Gamma0 (N : ℕ) : (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 N := by
  rw [CongruenceSubgroup.Gamma0_mem]
  simp

/-- `Γ₀(N)` already contains the centre. -/
theorem projectiveClosure_Gamma0 (N : ℕ) :
    projectiveClosure (CongruenceSubgroup.Gamma0 N) = CongruenceSubgroup.Gamma0 N :=
  sup_eq_left.mpr (Subgroup.zpowers_le.mpr (neg_one_mem_Gamma0 N))

/-- The `Γ₀(N)` index needs no factor of two. -/
theorem gamma0ProjectiveIndex_eq_prime_product (N : ℕ) [NeZero N] :
    ((projectiveClosure (CongruenceSubgroup.Gamma0 N)).index : ℚ) =
      N * ∏ p ∈ N.primeFactors, (1 + 1 / (p : ℚ)) := by
  rw [projectiveClosure_Gamma0, CongruenceIndex.Gamma0_index', CongruenceIndex.psi]

end WeightTwoCusps
