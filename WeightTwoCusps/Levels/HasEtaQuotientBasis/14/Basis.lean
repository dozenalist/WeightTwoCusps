module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«14».New.«14_2_a_a»
public import WeightTwoCusps.Basis.Constructor

/-! # An eta-quotient basis for the weight-two cusp forms at level fourteen -/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

/-- The singleton basis of `S₂(Γ₀(14))` given by `14.2.a.a`. -/
@[eta_simps] def level_14_etaBasis : Module.Basis (Fin 1) ℂ (gamma0CuspForms 14) :=
  cuspFormBasis ![cuspForm_14_2_a_a]


end WeightTwoCusps
