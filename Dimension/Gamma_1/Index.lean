/-
Copyright (c) 2026 Filip Najman.
Adapted from F-Najman/normalizer-lean, revision
1f4c27ec11da475383f69e6f82e2837a0cb54fd0. Apache 2.0.
See Dimension/Normalizer/README.md and LICENSE.
-/
module

public import Dimension.Gamma_0.Index

@[expose] public section

open Matrix MatrixGroups CongruenceSubgroup
namespace WeightTwoCusps.CongruenceIndex
noncomputable section

def diagonalMap (N : ℕ) : Gamma0 N →* (ZMod N)ˣ := (Gamma0Map N).toHomUnits

theorem diagonalMap_surjective (N : ℕ) [NeZero N] :
    Function.Surjective (diagonalMap N) := by
  intro u
  let d : ℕ := (u : ZMod N).val
  have hcop : d.Coprime N := ZMod.val_coe_unit_coprime u
  have hb := Int.gcd_eq_gcd_ab d N
  rw [Int.gcd_natCast_natCast, hcop] at hb
  have hdet : Int.gcdA d N * (d : ℤ) - (-Int.gcdB d N) * N = 1 := by
    push_cast at hb
    nlinarith only [hb]
  refine ⟨⟨mkSL _ _ _ _ hdet, Gamma0_mem.mpr ?_⟩, ?_⟩
  · simp [mkSL]
  · apply Units.ext
    change ((d : ℤ) : ZMod N) = (u : ZMod N)
    simp [d]

theorem diagonalMap_ker (N : ℕ) :
    (diagonalMap N).ker = (Gamma1 N).subgroupOf (Gamma0 N) := by
  rw [diagonalMap, MonoidHom.ker_toHomUnits]
  ext γ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Gamma1_mem]
  change ((γ : SL(2, ℤ)) 1 1 : ZMod N) = 1 ↔ _
  constructor
  · intro hd
    have hc := Gamma0_mem.mp γ.property
    have hdet := congrArg (Int.cast : ℤ → ZMod N) (γ : SL(2, ℤ)).det_coe
    simp only [det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one, hc, hd,
      mul_zero, mul_one, sub_zero] at hdet
    exact ⟨hdet, hd, hc⟩
  · exact fun h => h.2.1

theorem relIndex_Gamma1_Gamma0' (N : ℕ) [NeZero N] :
    (Gamma1 N).relIndex (Gamma0 N) = N.totient := by
  rw [Subgroup.relIndex, ← diagonalMap_ker, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (diagonalMap_surjective N), Subgroup.card_top,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-- Factoring the local factors of the second Jordan totient. -/
theorem prod_one_sub_inv_sq (N : ℕ) :
    ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) =
      (∏ p ∈ N.primeFactors, (1 - (p : ℚ)⁻¹)) *
        ∏ p ∈ N.primeFactors, (1 + 1 / (p : ℚ)) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  field_simp
  ring

/-- The full `SL₂(ℤ)` index of `Γ₁(N)`. -/
theorem index_Gamma1_eq_prime_product (N : ℕ) [NeZero N] :
    ((Gamma1 N).index : ℚ) =
      (N : ℚ) ^ 2 * ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) := by
  rw [← Subgroup.relIndex_mul_index (Gamma1_in_Gamma0 N), relIndex_Gamma1_Gamma0']
  push_cast
  rw [Gamma0_index', psi, Nat.totient_eq_mul_prod_factors, prod_one_sub_inv_sq]
  ring


end
end WeightTwoCusps.CongruenceIndex
