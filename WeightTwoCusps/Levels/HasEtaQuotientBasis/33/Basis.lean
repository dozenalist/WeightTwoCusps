module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«33».Old.«11_2_a_a_old_33_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«33».Old.«11_2_a_a_old_33_3»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«33».New.«33_eta_1p1_3p1_11p1_33p1»
public import WeightTwoCusps.Basis.Constructor

/-!
# An eta-quotient basis at level 33

The oldspace is spanned by the dilation-one and dilation-three lifts of
`11.2.a.a`. The third entry is an eta complement, not a normalized newform.
Basis entries follow `Basis_cuspidal_eta_S2` in
[the local level table](../TABLE.md#level-33), in its original order.
-/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The complete cuspidal eta basis of `S₂(Γ₀(33))`, in report order. -/
@[eta_simps] def level_33_etaBasis : Module.Basis (Fin 3) ℂ (gamma0CuspForms 33) :=
  cuspFormBasis ![cuspForm_11_2_a_a_old_33_1, cuspForm_11_2_a_a_old_33_3, cuspForm_33_eta_1p1_3p1_11p1_33p1]

end WeightTwoCusps

