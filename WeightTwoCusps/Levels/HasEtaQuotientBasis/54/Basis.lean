module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«54».Old.«27_2_a_a_old_54_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«54».Old.«27_2_a_a_old_54_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«54».New.«54_eta_1m1_2p2_6p2_9p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«54».New.«54_eta_1m1_2p2_3p1_18p1_27p2_54m1»
public import WeightTwoCusps.Basis.Constructor

/-!
# An eta-quotient basis at level 54

Entries follow `Basis_cuspidal_eta_S2` in
[the local level table](../TABLE.md#level-54), in its original order.

0: `cuspForm_27_2_a_a_old_54_1` is the dilation-1 lift
of `cuspForm_27_2_a_a`.

1: `cuspForm_27_2_a_a_old_54_2` is the dilation-2 lift
of `cuspForm_27_2_a_a`.

2: `cuspForm_54_eta_1m1_2p2_6p2_9p1` is a directly defined eta basis vector.

3: `cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1` is a directly defined eta basis vector.

Direct eta entries are not asserted to be normalized Hecke newforms or
members of the canonical newspace. The constructor certifies the full basis.
The coefficient columns are `1, 2, 4, 5`.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The complete cuspidal eta basis of `S₂(Γ₀(54))`, in report order. -/
@[eta_simps] def level_54_etaBasis : Module.Basis (Fin 4) ℂ (gamma0CuspForms 54) :=
  cuspFormBasis ![
    cuspForm_27_2_a_a_old_54_1,
    cuspForm_27_2_a_a_old_54_2,
    cuspForm_54_eta_1m1_2p2_6p2_9p1,
    cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1] (c := ![1, 2, 4, 5])

end WeightTwoCusps
