module

public import Dimension.Gamma_0.Basic

@[expose] public section

/-! # Analytic weight-two cusp forms for `Γ₁(N)` -/

noncomputable section

namespace WeightTwoCusps

/-- Mathlib's complex vector space of weight-two cusp forms for `Γ₁(N)`. -/
abbrev gamma1CuspForms (N : ℕ) := CuspForm (CongruenceSubgroup.Gamma1 N) 2

/-- The `Γ₀(N)` space embeds into the `Γ₁(N)` space. -/
theorem gamma0CuspForms_finrank_le_gamma1 (N : ℕ) [NeZero N] :
    Module.finrank ℂ (gamma0CuspForms N) ≤ Module.finrank ℂ (gamma1CuspForms N) :=
  weightTwoCuspForms_finrank_le (CongruenceSubgroup.Gamma1_in_Gamma0 N)

end WeightTwoCusps
