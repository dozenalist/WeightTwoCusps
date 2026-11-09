module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«30».Old.«15_2_a_a_old_30_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«30».Old.«15_2_a_a_old_30_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«30».New.«30_eta_1p1_2p1_15p1_30p1»
public import WeightTwoCusps.Basis.Constructor

/-!
# An eta-quotient basis at level 30

The oldspace is spanned by the dilation-one and dilation-two lifts of
`15.2.a.a`. The third entry is an eta complement, not a normalized newform.
Basis entries follow `Basis_cuspidal_eta_S2` in
[the local level table](../TABLE.md#level-30), in its original order.
-/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The complete cuspidal eta basis of `S₂(Γ₀(30))`, in report order. -/
@[eta_simps] def level_30_etaBasis : Module.Basis (Fin 3) ℂ (gamma0CuspForms 30) :=
  cuspFormBasis ![cuspForm_15_2_a_a_old_30_1, cuspForm_15_2_a_a_old_30_2, cuspForm_30_eta_1p1_2p1_15p1_30p1]

end WeightTwoCusps

