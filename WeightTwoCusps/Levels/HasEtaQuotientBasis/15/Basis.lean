module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«15».New.«15_2_a_a»
public import WeightTwoCusps.Basis.Constructor

/-! # An eta-quotient basis for the weight-two cusp forms at level fifteen -/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

/-- The singleton basis of `S₂(Γ₀(15))` given by `15.2.a.a`. -/
@[eta_simps] def level_15_etaBasis : Module.Basis (Fin 1) ℂ (gamma0CuspForms 15) :=
  cuspFormBasis ![cuspForm_15_2_a_a]

end WeightTwoCusps
