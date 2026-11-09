module

public import Dimension.Gamma_1.Index
public import Dimension.GroupTheory.ProjectiveSubgroup
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

open scoped MatrixGroups

noncomputable section

namespace WeightTwoCusps

/-- The index of the image of `Γ₁(N)` in `PSL₂(ℤ)`. -/
abbrev gamma1ProjectiveIndex (N : ℕ) : ℕ :=
  (projectiveClosure (CongruenceSubgroup.Gamma1 N)).index

theorem neg_one_not_mem_Gamma1 (N : ℕ) (hN : 3 ≤ N) :
    (-1 : SL(2, ℤ)) ∉ CongruenceSubgroup.Gamma1 N := by
  letI : Fact (2 < N) := ⟨by omega⟩
  intro h
  have ha := ((CongruenceSubgroup.Gamma1_mem N (-1 : SL(2, ℤ))).mp h).1
  have hneg : (-1 : ZMod N) = 1 := by simpa using ha
  exact ZMod.neg_one_ne_one hneg

/-- For `N ≥ 3`, passage to the effective action halves the index. -/
theorem two_mul_gamma1ProjectiveIndex (N : ℕ) (hN : 3 ≤ N) :
    2 * gamma1ProjectiveIndex N = (CongruenceSubgroup.Gamma1 N).index :=
  two_mul_projectiveClosure_index _ (neg_one_not_mem_Gamma1 N hN)

/-- The prime-product index used in the weight-two `Γ₁(N)` dimension formula. -/
theorem gamma1ProjectiveIndex_eq_prime_product (N : ℕ) (hN : 3 ≤ N) :
    (gamma1ProjectiveIndex N : ℚ) =
      (N : ℚ) ^ 2 / 2 * ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) := by
  letI : NeZero N := ⟨by omega⟩
  have h : (2 : ℚ) * gamma1ProjectiveIndex N =
      ((CongruenceSubgroup.Gamma1 N).index : ℚ) := by
    exact_mod_cast two_mul_gamma1ProjectiveIndex N hN
  rw [CongruenceIndex.index_Gamma1_eq_prime_product] at h
  linarith

end WeightTwoCusps
