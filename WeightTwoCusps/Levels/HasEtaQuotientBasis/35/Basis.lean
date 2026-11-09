module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«35».New.«35_eta_1p2_35p2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«35».New.«35_eta_1p1_5p1_7p1_35p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«35».New.«35_eta_5p2_7p2»
public import WeightTwoCusps.Basis.Constructor

/-!
# An eta-quotient basis at level 35

Every proper divisor of 35 has zero-dimensional cusp space, so all three
dimensions are new. These are eta basis vectors, not a Hecke eigenbasis.
Basis entries follow `Basis_cuspidal_eta_S2` in
[the local level table](../TABLE.md#level-35), in its original order.
-/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The complete cuspidal eta basis of `S₂(Γ₀(35))`, in report order. -/
@[eta_simps] def level_35_etaBasis : Module.Basis (Fin 3) ℂ (gamma0CuspForms 35) :=
  cuspFormBasis ![cuspForm_35_eta_1p2_35p2, cuspForm_35_eta_1p1_5p1_7p1_35p1, cuspForm_35_eta_5p2_7p2]

end WeightTwoCusps

