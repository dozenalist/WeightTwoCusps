module

public import Dimension.Gamma.Arithmetic
public import Dimension.Gamma.CongruenceIndex
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

open scoped MatrixGroups

namespace WeightTwoCusps

/-- At level two the central element already belongs to the principal group. -/
theorem projectiveIndex_two : projectiveIndex 2 = 6 := by
  have hneg : (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma 2 := by
    rw [CongruenceSubgroup.Gamma_mem]
    simp [ZMod.neg_one_eq_one_iff]
  have heq : projectiveIndex 2 = (CongruenceSubgroup.Gamma 2).index := by
    rw [projectiveIndex, sup_eq_left.mpr (Subgroup.zpowers_le.mpr hneg)]
  rw [heq]
  have h := CongruenceIndex.index_Gamma' 2
  norm_num [Nat.prime_two.primeFactors] at h
  exact_mod_cast h

private theorem neg_one_ne_one_mod {N : ℕ} (hN : 3 ≤ N) :
    (-1 : SL(2, ZMod N)) ≠ 1 := by
  letI : Fact (2 < N) := ⟨by omega⟩
  intro h
  have hentry := congrArg (fun g : SL(2, ZMod N) => g 0 0) h
  have h' : (-1 : ZMod N) = 1 := by simpa using hentry
  exact ZMod.neg_one_ne_one h'

/-- Passing from the full modular group to its effective action divides the
principal-level index by two once `N ≥ 3`. -/
theorem two_mul_projectiveIndex (N : ℕ) (hN : 3 ≤ N) :
    2 * projectiveIndex N = (CongruenceSubgroup.Gamma N).index := by
  letI := CongruenceSubgroup.Gamma_normal N
  have hrel : (CongruenceSubgroup.Gamma N).relIndex
      (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) = 2 := by
    rw [Subgroup.relIndex_sup_left, CongruenceSubgroup.Gamma,
      Subgroup.relIndex_ker, MonoidHom.map_zpowers]
    have hmap : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N))
        (-1 : SL(2, ℤ)) = -1 := by
      ext i j
      simp [Matrix.SpecialLinearGroup.map_apply_coe]
    rw [hmap, Nat.card_zpowers]
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by simp [sq]) (neg_one_ne_one_mod hN)
  simpa only [hrel] using
    (Subgroup.relIndex_mul_index (show CongruenceSubgroup.Gamma N ≤
      CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) from le_sup_left))

/-- The classical prime-product expression for the effective principal-level index. -/
theorem projectiveIndex_eq_prime_product (N : ℕ) (hN : 3 ≤ N) :
    (projectiveIndex N : ℚ) =
      (N : ℚ) ^ 3 / 2 * ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) := by
  letI : NeZero N := ⟨by omega⟩
  have h : (2 : ℚ) * (projectiveIndex N : ℚ) =
      ((CongruenceSubgroup.Gamma N).index : ℚ) := by
    exact_mod_cast two_mul_projectiveIndex N hN
  rw [CongruenceIndex.index_Gamma'] at h
  linarith

end WeightTwoCusps
