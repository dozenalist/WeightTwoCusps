module

public import Dimension.Gamma.Periods
public import Dimension.FLT.P2M.Sol.S_ModularCurve_twelve_mul_add_mul_index_le_finrank_cuspForm_Gamma
@[expose] public section

/-!
# The weight-two dimension identity

The injective real period map gives the upper bound. The lower bound comes from
Riemann--Roch, via the attributed proof copied under `Dimension/FLT`.
-/

noncomputable section

open scoped MatrixGroups

namespace WeightTwoCusps

/-- The weight-two dimension identity in terms of the projective index of `Γ(N)`.
This form avoids truncated subtraction and integer division. -/
theorem gammaCuspForms_dimension_relation (N : ℕ) (hN : 2 ≤ N) :
    12 * N * Module.finrank ℂ (gammaCuspForms N) +
        6 * (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index =
      12 * N + N *
        (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index := by
  letI : NeZero N := ⟨by omega⟩
  exact Nat.le_antisymm (gammaCuspForms_dimension_upper_bound N hN)
    (ModularCurve.twelve_mul_add_mul_index_le_finrank_cuspForm_Gamma N hN)

end WeightTwoCusps
