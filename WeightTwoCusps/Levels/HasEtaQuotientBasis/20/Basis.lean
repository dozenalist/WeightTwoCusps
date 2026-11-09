module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«20».New.«20_2_a_a»
public import WeightTwoCusps.Basis.Constructor

/-! # An eta-quotient basis for the weight-two cusp forms at level twenty -/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

/-- The singleton basis of `S₂(Γ₀(20))` given by `20.2.a.a`. -/
@[eta_simps] def level_20_etaBasis : Module.Basis (Fin 1) ℂ (gamma0CuspForms 20) :=
  cuspFormBasis ![cuspForm_20_2_a_a]

end WeightTwoCusps
