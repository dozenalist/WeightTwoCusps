module

public import WeightTwoCusps.Tactic.EtaCoefficient

/-! # Larger-index eta coefficient checks at default Lean resource limits -/

public section

open WeightTwoCusps UpperHalfPlane

theorem eta_tau_twenty :
    (qExpansion 1 (etaQuotient 1 ![24])).coeff 20 = -7109760 := by eta_coeff

theorem eta_tau_fifty :
    (qExpansion 1 (etaQuotient 1 ![24])).coeff 50 = 611981400 := by eta_coeff

theorem eta_tau_hundred :
    (qExpansion 1 (etaQuotient 1 ![24])).coeff 100 = 37534859200 := by eta_coeff

set_option maxRecDepth 4096 in
theorem eta_tau_two_hundred :
    (qExpansion 1 (etaQuotient 1 ![24])).coeff 200 = -2154174528000 := by eta_coeff

#print axioms eta_tau_hundred
#print axioms eta_tau_two_hundred
