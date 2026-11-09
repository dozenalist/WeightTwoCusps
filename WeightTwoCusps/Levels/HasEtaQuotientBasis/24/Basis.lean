module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«24».New.«24_2_a_a»
public import WeightTwoCusps.Basis.Constructor

/-! # An eta-quotient basis for the weight-two cusp forms at level twenty-four -/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

/-- The singleton basis of `S₂(Γ₀(24))` given by `24.2.a.a`. -/
@[eta_simps] def level_24_etaBasis : Module.Basis (Fin 1) ℂ (gamma0CuspForms 24) :=
  cuspFormBasis ![cuspForm_24_2_a_a]

end WeightTwoCusps
