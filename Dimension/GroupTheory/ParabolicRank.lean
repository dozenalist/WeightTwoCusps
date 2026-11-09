/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache 2.0 license.
The index-divisibility argument is adapted from the attributed local copy in
Dimension/FLT/P2M/Sol/S_ModularCurve_six_mul_level_mul_finrank_parabolicHoms_Gamma_add_eq.lean.
See Dimension/FLT/ATTRIBUTION_UPSTREAM.md.
-/
module

public import Dimension.CuspForms.Projective
public import Dimension.FLT.P2M.Sol.S_ModularCurve_six_mul_level_mul_finrank_parabolicHoms_Gamma_add_eq

@[expose] public section

/-!
# Parabolic homomorphisms and cusp counts

The group-theoretic boundary relation is valid for every finite-index subgroup
containing `-I`. In the absence of elliptic elements, the free-group calculation
then gives the rank in terms of the index and cusp count.
-/

noncomputable section

open scoped MatrixGroups

namespace WeightTwoCusps

open ModularCurve.Period
open P2MW.S_ModularCurve_six_mul_level_mul_finrank_parabolicHoms_Gamma_add_eq

private theorem trace_conjugate (g u : SL(2, ℤ)) :
    ((g⁻¹ * u * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace =
      (u : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm,
    ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]

private theorem prime_dvd_index_of_trace_ne (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    (hΓ : ∀ γ ∈ Γ, (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 1 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ -1)
    (u : SL(2, ℤ)) (p : ℕ) [Fact p.Prime] (hu : u ^ p = -1)
    (htr : (u : Matrix (Fin 2) (Fin 2) ℤ).trace = 0 ∨
      (u : Matrix (Fin 2) (Fin 2) ℤ).trace = 1 ∨
      (u : Matrix (Fin 2) (Fin 2) ℤ).trace = -1) : p ∣ Γ.index := by
  classical
  letI : Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers u) (SL(2, ℤ) ⧸ Γ)) :=
    Fintype.ofFinite _
  have hper : ∀ x : SL(2, ℤ) ⧸ Γ, Function.minimalPeriod (u • ·) x = p := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H g =>
      apply Function.minimalPeriod_eq_prime
      · change (u • ·)^[p] (g : SL(2, ℤ) ⧸ Γ) = g
        rw [smul_iterate]
        change u ^ p • (g : SL(2, ℤ) ⧸ Γ) = g
        rw [hu, MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq]
        simpa using hneg
      · intro hfix
        change u • (g : SL(2, ℤ) ⧸ Γ) = g at hfix
        rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq] at hfix
        have hmem : g⁻¹ * u * g ∈ Γ := by
          simpa [mul_inv_rev, mul_assoc] using Γ.inv_mem hfix
        have hn := hΓ _ hmem
        rw [trace_conjugate] at hn
        tauto
  rw [Subgroup.index_eq_sum_minimalPeriod Γ u]
  simp only [hper, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  exact Dvd.intro_left _ rfl

/-- The projective index of a subgroup without elliptic stabilizers is divisible by six. -/
theorem six_dvd_index_of_trace_ne (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    (hΓ : ∀ γ ∈ Γ, (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 1 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ -1) : 6 ∣ Γ.index := by
  have h2 : 2 ∣ Γ.index := by
    apply prime_dvd_index_of_trace_ne Γ hneg hΓ ModularGroup.S 2
    · apply Subtype.ext
      simpa [sq] using ModularGroup.S_mul_S_eq
    · left
      rw [ModularGroup.coe_S, Matrix.trace_fin_two_of]
      norm_num
  have h3 : 3 ∣ Γ.index := by
    letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    apply prime_dvd_index_of_trace_ne Γ hneg hΓ (ModularGroup.S * ModularGroup.T) 3
    · exact BettiPrincipal.ST_pow_three
    · right; left
      rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, ModularGroup.coe_T,
        Matrix.mul_fin_two, Matrix.trace_fin_two_of]
      norm_num
  exact (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd h2 h3

/-- Cusp classes, realized as translation orbits on the cosets. -/
abbrev subgroupCusps (Γ : Subgroup SL(2, ℤ)) :=
  MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.T) (SL(2, ℤ) ⧸ Γ)

/-- The boundary relations remove one fewer generator than the number of cusps. -/
theorem parabolicHoms_finrank_add_cusps (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : SL(2, ℤ)) ∈ Γ) :
    Module.finrank ℚ (parabolicHoms ℚ Γ ℚ) + Nat.card (subgroupCusps Γ) =
      Module.finrank ℚ (Additive Γ →+ ℚ) + 1 := by
  apply Nat.le_antisymm
  · exact finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one Γ hneg ℚ
  · exact BettiPrincipal.finrank_addMonoidHom_add_one_le (Γ := Γ) hneg

/-- The Betti rank formula for a subgroup acting without elliptic stabilizers. -/
theorem parabolicHoms_finrank_add_cusps_of_trace_ne (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    (hΓ : ∀ γ ∈ Γ, (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 1 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ -1) :
    Module.finrank ℚ (parabolicHoms ℚ Γ ℚ) + Nat.card (subgroupCusps Γ) =
      2 + Γ.index / 6 := by
  rw [parabolicHoms_finrank_add_cusps Γ hneg,
    Matrix.SpecialLinearGroup.finrank_addMonoidHom_eq_of_forall_trace_ne Γ hneg hΓ ℚ]
  omega

/-- An unconditional cusp-form upper bound in the torsion-free projective case. -/
theorem weightTwoCuspForms_dimension_upper_bound_of_trace_ne
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    (hΓ : ∀ γ ∈ Γ, (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 1 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ -1) :
    2 * Module.finrank ℂ (CuspForm Γ 2) + Nat.card (subgroupCusps Γ) ≤
      2 + Γ.index / 6 := by
  have hp := parabolicHoms_finrank_add_cusps_of_trace_ne Γ hneg hΓ
  have hi := two_mul_finrank_cuspForms_le_intParabolicHoms Γ
  rw [← realParabolicHoms_finrank_eq_int Γ, realParabolicHoms_finrank_eq_rat Γ] at hi
  omega

end WeightTwoCusps
