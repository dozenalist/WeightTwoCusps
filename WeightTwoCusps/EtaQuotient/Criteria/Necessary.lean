module

public import WeightTwoCusps.EtaQuotient.Transformation.Reflection

/-! # Necessary conditions for arbitrary integer exponent functions -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace WeightTwoCusps.EtaQuotient

/-- Since `-I ∈ Γ₀(N)` and an eta quotient is nonzero, its weight is even
when the character is trivial. No parity restriction on the individual
exponents is used here. -/
theorem even_weight_of_modularForm {N : ℕ} {r : Fin N → ℤ} {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (hf : (f : ℍ → ℂ) = etaQuotient N r) : Even k := by
  rcases Int.even_or_odd k with hk | hk
  · exact hk
  · have hneg : (-1 : GL (Fin 2) ℝ) ∈
        (CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ) := by
      refine ⟨-1, ?_, ?_⟩
      · simp [CongruenceSubgroup.Gamma0_mem]
      · ext i j
        simp [Matrix.SpecialLinearGroup.mapGL]
    have he := ModularForm.eq_zero_of_neg_one_mem hneg hk f
    have hz : (f : ℍ → ℂ) UpperHalfPlane.I = 0 := by rw [he]; rfl
    rw [hf] at hz
    exact False.elim (ne_zero N r UpperHalfPlane.I hz)

/-- Both Newman congruences are necessary at every positive level. -/
theorem newmanConditions_of_modularForm {N : ℕ} (hN : 0 < N) {r : Fin N → ℤ} {k : ℤ}
    (hk : HasWeight N r k) (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (hf : (f : ℍ → ℂ) = etaQuotient N r) : NewmanConditions N r k where
  level_pos := hN
  weight := hk
  infinity_congruence := infinitySum_dvd_of_modularForm f hf
  zero_congruence := zeroSum_dvd_of_modularForm hk f hf

theorem infinitySum_nonneg_of_modularForm {N : ℕ} (hN : 0 < N) {r : Fin N → ℤ} {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (hf : (f : ℍ → ℂ) = etaQuotient N r) : 0 ≤ infinitySum N r := by
  have : NeZero N := ⟨hN.ne'⟩
  have hb := ModularFormClass.bdd_at_infty f
  rw [hf] at hb
  exact (isBoundedAtImInfty_iff N r).mp hb

theorem zeroSum_nonneg_of_modularForm {N : ℕ} (hN : 0 < N) {r : Fin N → ℤ} {k : ℤ}
    (hk : HasWeight N r k) (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (hf : (f : ℍ → ℂ) = etaQuotient N r) : 0 ≤ zeroSum N r := by
  have : NeZero N := ⟨hN.ne'⟩
  have hb := ModularFormClass.bdd_at_infty_slash f ModularGroup.S
  rw [hf] at hb
  exact (slash_S_isBoundedAtImInfty_iff hN hk).mp hb

end WeightTwoCusps.EtaQuotient
