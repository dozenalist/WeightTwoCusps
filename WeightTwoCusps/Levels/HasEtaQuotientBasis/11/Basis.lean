module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«11».New.«11_2_a_a»
public import WeightTwoCusps.Basis.Constructor

/-! # An eta-quotient basis for the weight-two cusp forms at level eleven -/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

/-- The singleton basis of `S₂(Γ₀(11))` given by `11.2.a.a`. -/
abbrev level_11_etaBasis : Module.Basis (Fin 1) ℂ (gamma0CuspForms 11) :=
  cuspFormBasis ![cuspForm_11_2_a_a]

end WeightTwoCusps
