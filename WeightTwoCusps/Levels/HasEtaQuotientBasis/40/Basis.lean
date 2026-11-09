module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«40».Old.«20_2_a_a_old_40_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«40».Old.«20_2_a_a_old_40_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«40».New.«40_eta_1m2_2p5_4m1_5p2_10m1_20p1»
public import WeightTwoCusps.Basis.Constructor

/-!
# An eta-quotient basis at level 40

The oldspace is spanned by the dilation-one and dilation-two lifts of
`20.2.a.a`. The third entry is an eta complement, not a normalized newform.
Basis entries follow `Basis_cuspidal_eta_S2` in
[the local level table](../TABLE.md#level-40), in its original order.
-/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The complete cuspidal eta basis of `S₂(Γ₀(40))`, in report order. -/
@[eta_simps] def level_40_etaBasis : Module.Basis (Fin 3) ℂ (gamma0CuspForms 40) :=
  cuspFormBasis ![cuspForm_20_2_a_a_old_40_1, cuspForm_20_2_a_a_old_40_2,
    cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1]

end WeightTwoCusps

