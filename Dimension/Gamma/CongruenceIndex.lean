/-
Copyright (c) 2026 Filip Najman.
Adapted from F-Najman/normalizer-lean, revision
1f4c27ec11da475383f69e6f82e2837a0cb54fd0. Apache 2.0.
See Dimension/Normalizer/README.md and LICENSE.
-/
module

public import Dimension.Gamma_1.Index

@[expose] public section

open Matrix MatrixGroups CongruenceSubgroup
namespace WeightTwoCusps.CongruenceIndex
noncomputable section

/-- γ ↦ b mod N on Γ₁(N). -/
def upperMap (N : ℕ) : Gamma1 N →* Multiplicative (ZMod N) where
  toFun γ := Multiplicative.ofAdd (((γ : SL(2, ℤ)) 0 1 : ℤ) : ZMod N)
  map_one' := by simp
  map_mul' γ γ' := by
    obtain ⟨ha, hd, -⟩ := (Gamma1_mem N γ).1 γ.2
    obtain ⟨ha', hd', -⟩ := (Gamma1_mem N γ').1 γ'.2
    rw [← ofAdd_add]
    congr 1
    simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, Int.cast_add, Int.cast_mul, ha, hd']
    ring

theorem upperMap_surjective (N : ℕ) [NeZero N] : Function.Surjective (upperMap N) := by
  intro x
  have h : (1 : ℤ) * 1 - (Multiplicative.toAdd x).val * 0 = 1 := by ring
  refine ⟨⟨mkSL 1 (Multiplicative.toAdd x).val 0 1 h, (Gamma1_mem N _).2 ⟨by simp [mkSL],
    by simp [mkSL], by simp [mkSL]⟩⟩, ?_⟩
  show Multiplicative.ofAdd (((Multiplicative.toAdd x).val : ℤ) : ZMod N) = x
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  rfl

theorem upperMap_ker (N : ℕ) : (upperMap N).ker = (Gamma N).subgroupOf (Gamma1 N) := by
  ext γ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Gamma_mem]
  obtain ⟨ha, hd, hc⟩ := (Gamma1_mem N γ).1 γ.2
  show Multiplicative.ofAdd _ = 1 ↔ _
  rw [ofAdd_eq_one]
  exact ⟨fun h => ⟨ha, h, hc, hd⟩, fun h => h.2.1⟩

theorem relIndex_Gamma_Gamma1' (N : ℕ) [NeZero N] : (Gamma N).relIndex (Gamma1 N) = N := by
  rw [Subgroup.relIndex, ← upperMap_ker, Subgroup.index_ker,
    MonoidHom.range_eq_top.2 (upperMap_surjective N), Subgroup.card_top]
  exact Nat.card_zmod N

/-! ### [SL₂(ℤ) : Γ(N)] -/

theorem Gamma_le_Gamma1 (N : ℕ) : Gamma N ≤ Gamma1 N := fun γ h => by
  obtain ⟨ha, -, hc, hd⟩ := Gamma_mem.1 h
  exact (Gamma1_mem N γ).2 ⟨ha, hd, hc⟩

theorem index_Gamma' (N : ℕ) [NeZero N] :
    ((Gamma N).index : ℚ) = N ^ 3 * ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) := by
  rw [← Subgroup.relIndex_mul_index (Gamma_le_Gamma1 N), relIndex_Gamma_Gamma1']
  push_cast
  rw [index_Gamma1_eq_prime_product]
  ring



end
end WeightTwoCusps.CongruenceIndex
