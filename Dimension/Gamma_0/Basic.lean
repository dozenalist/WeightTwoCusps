module

public import Dimension.CuspForms.Restriction
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

@[expose] public section

/-! # Analytic weight-two cusp forms for `Γ₀(N)` -/

noncomputable section

namespace WeightTwoCusps

/-- Mathlib's complex vector space of weight-two cusp forms for `Γ₀(N)`. -/
abbrev gamma0CuspForms (N : ℕ) := CuspForm (CongruenceSubgroup.Gamma0 N) 2

end WeightTwoCusps
