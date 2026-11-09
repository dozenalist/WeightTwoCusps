module

public import Dimension.Periods.Basic
public import Dimension.Gamma.Basic
public import Dimension.FLT.P2M.Sol.S_ModularCurve_six_mul_level_mul_finrank_parabolicHoms_Gamma_add_eq

@[expose] public section

noncomputable section

open scoped MatrixGroups

namespace WeightTwoCusps

/-- The upper half of the principal-level weight-two dimension formula. -/
theorem gammaCuspForms_dimension_upper_bound (N : ℕ) (hN : 2 ≤ N) :
    12 * N * Module.finrank ℂ (gammaCuspForms N) +
        6 * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ≤
      12 * N + N *
        (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
  letI : NeZero N := ⟨by omega⟩
  have h := Nat.mul_le_mul_left (6 * N)
    (two_mul_finrank_cuspForms_le_intParabolicHoms (CongruenceSubgroup.Gamma N))
  have hb := ModularCurve.six_mul_level_mul_finrank_parabolicHoms_Gamma_add_eq N hN
  nlinarith

/-- At level six the period argument bounds the dimension by one. -/
theorem gammaCuspForms_finrank_six_le_one :
    Module.finrank ℂ (gammaCuspForms 6) ≤ 1 := by
  have h := gammaCuspForms_dimension_upper_bound 6 (by decide)
  omega

end WeightTwoCusps
