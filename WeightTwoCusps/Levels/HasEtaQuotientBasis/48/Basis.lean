module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«48».Old.«24_2_a_a_old_48_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«48».Old.«24_2_a_a_old_48_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«48».New.«48_eta_1m2_2p4_3p2_6m2_12p2»
public import WeightTwoCusps.Basis.Constructor

/-!
# An eta-quotient basis at level 48

Entries follow `Basis_cuspidal_eta_S2` in
[the local level table](../TABLE.md#level-48), in its original order.

0: `cuspForm_24_2_a_a_old_48_1` is the dilation-1 lift
of `cuspForm_24_2_a_a`.

1: `cuspForm_24_2_a_a_old_48_2` is the dilation-2 lift
of `cuspForm_24_2_a_a`.

2: `cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2` is a directly defined eta basis vector.

Direct eta entries are not asserted to be normalized Hecke newforms or
members of the canonical newspace. The constructor certifies the full basis.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The complete cuspidal eta basis of `S₂(Γ₀(48))`, in report order. -/
@[eta_simps] def level_48_etaBasis : Module.Basis (Fin 3) ℂ (gamma0CuspForms 48) :=
  cuspFormBasis ![
    cuspForm_24_2_a_a_old_48_1,
    cuspForm_24_2_a_a_old_48_2,
    cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2]

end WeightTwoCusps
