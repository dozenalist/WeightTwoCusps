module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«28».Old.«14_2_a_a_old_28_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«28».Old.«14_2_a_a_old_28_2»
public import WeightTwoCusps.Basis.Constructor

/-! # An oldform eta-quotient basis at level twenty-eight -/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

/-- The basis of `S₂(Γ₀(28))` given by the two degeneracy lifts of `14.2.a.a`. -/
@[eta_simps] def level_28_etaBasis : Module.Basis (Fin 2) ℂ (gamma0CuspForms 28) :=
  cuspFormBasis ![cuspForm_14_2_a_a_old_28_1, cuspForm_14_2_a_a_old_28_2]

end WeightTwoCusps
