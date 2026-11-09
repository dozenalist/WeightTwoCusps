module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«64».Old.«32_2_a_a_old_64_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«64».Old.«32_2_a_a_old_64_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«64».New.«64_eta_1m2_2p5_4m2_8p3»
public import WeightTwoCusps.Basis.Constructor

/-!
# An eta-quotient basis at level 64

Entries follow `Basis_cuspidal_eta_S2` in
[the local level table](../TABLE.md#level-64), in its original order.

0: `cuspForm_32_2_a_a_old_64_1` is the dilation-1 lift
of `cuspForm_32_2_a_a`.

1: `cuspForm_32_2_a_a_old_64_2` is the dilation-2 lift
of `cuspForm_32_2_a_a`.

2: `cuspForm_64_eta_1m2_2p5_4m2_8p3` is a directly defined eta basis vector.

Direct eta entries are not asserted to be normalized Hecke newforms or
members of the canonical newspace. The constructor certifies the full basis.
The coefficient columns are `1, 2, 5`.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The complete cuspidal eta basis of `S₂(Γ₀(64))`, in report order. -/
@[eta_simps] def level_64_etaBasis : Module.Basis (Fin 3) ℂ (gamma0CuspForms 64) :=
  cuspFormBasis ![
    cuspForm_32_2_a_a_old_64_1,
    cuspForm_32_2_a_a_old_64_2,
    cuspForm_64_eta_1m2_2p5_4m2_8p3] (c := ![1, 2, 5])

end WeightTwoCusps
