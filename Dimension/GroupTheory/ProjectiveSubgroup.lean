/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache 2.0 license.
The membership argument is adapted from the attributed local copy in
Dimension/FLT/P2M/Sol/S_ModularCurve_Period_existsUnique_isParabolicHom_sup_zpowers_neg_one_apply_eq.lean.
See Dimension/FLT/ATTRIBUTION_UPSTREAM.md.
-/
module

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.GroupTheory.Index

@[expose] public section

open scoped MatrixGroups

namespace WeightTwoCusps

/-- Adjoin `-I` to pass to the subgroup with the same effective action. -/
abbrev projectiveClosure (Γ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℤ) :=
  Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))

instance projectiveClosure_finiteIndex (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    (projectiveClosure Γ).FiniteIndex := Subgroup.finiteIndex_of_le le_sup_left

/-- Membership in the projective closure is membership up to sign. -/
theorem mem_projectiveClosure_iff (Γ : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) :
    g ∈ projectiveClosure Γ ↔ g ∈ Γ ∨ -g ∈ Γ := by
  letI : (Subgroup.zpowers (-1 : SL(2, ℤ))).Normal :=
    ⟨fun n hn g => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      have hc := (Commute.neg_one_right g).zpow_right k
      rw [hc.eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k⟩
  constructor
  · intro hg
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hsq : ((-1 : SL(2, ℤ)) ^ (2 : ℤ)) = 1 := by rw [zpow_two]; simp
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      simpa [← two_mul, zpow_mul, hsq] using hy
    · right
      simpa [zpow_add, zpow_mul, hsq] using hy
  · rintro (hg | hg)
    · exact Subgroup.mem_sup_left hg
    · have hm : (-1 : SL(2, ℤ)) ∈ projectiveClosure Γ :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      simpa using (projectiveClosure Γ).mul_mem hm (Subgroup.mem_sup_left hg)

/-- Adjoining `-I` doubles a subgroup when it does not already contain `-I`. -/
theorem relIndex_projectiveClosure (Γ : Subgroup SL(2, ℤ))
    (hneg : (-1 : SL(2, ℤ)) ∉ Γ) : Γ.relIndex (projectiveClosure Γ) = 2 := by
  apply Subgroup.relIndex_eq_two_iff_exists_notMem_and.mpr
  refine ⟨-1, Subgroup.mem_sup_right (Subgroup.mem_zpowers _), hneg, ?_⟩
  intro g hg
  simpa only [mul_neg_one, or_comm] using (mem_projectiveClosure_iff Γ g).mp hg

/-- The index of the effective subgroup is half the full index in this case. -/
theorem two_mul_projectiveClosure_index (Γ : Subgroup SL(2, ℤ))
    (hneg : (-1 : SL(2, ℤ)) ∉ Γ) :
    2 * (projectiveClosure Γ).index = Γ.index := by
  simpa only [relIndex_projectiveClosure Γ hneg] using
    Subgroup.relIndex_mul_index (show Γ ≤ projectiveClosure Γ from le_sup_left)

end WeightTwoCusps
