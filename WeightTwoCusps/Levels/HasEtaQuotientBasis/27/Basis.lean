module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«27».New.«27_2_a_a»
public import WeightTwoCusps.Basis.Constructor

/-! # An eta-quotient basis for the weight-two cusp forms at level twenty-seven -/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

/-- The singleton basis of `S₂(Γ₀(27))` given by `27.2.a.a`. -/
@[eta_simps] def level_27_etaBasis : Module.Basis (Fin 1) ℂ (gamma0CuspForms 27) :=
  cuspFormBasis ![cuspForm_27_2_a_a]

end WeightTwoCusps
