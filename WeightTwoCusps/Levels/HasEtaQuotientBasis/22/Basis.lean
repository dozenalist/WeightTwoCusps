module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«22».Old.«11_2_a_a_old_22_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«22».Old.«11_2_a_a_old_22_2»
public import WeightTwoCusps.Basis.Constructor

/-! # An oldform eta-quotient basis at level twenty-two -/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

/-- The basis of `S₂(Γ₀(22))` given by the two degeneracy lifts of `11.2.a.a`. -/
@[eta_simps] def level_22_etaBasis : Module.Basis (Fin 2) ℂ (gamma0CuspForms 22) :=
  cuspFormBasis ![cuspForm_11_2_a_a_old_22_1, cuspForm_11_2_a_a_old_22_2]

end WeightTwoCusps
