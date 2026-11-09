module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«84».Old.«14_2_a_a_old_84_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«84».Old.«14_2_a_a_old_84_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«84».Old.«14_2_a_a_old_84_3»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«84».Old.«14_2_a_a_old_84_6»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«84».Old.«42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_84_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«84».Old.«42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4_old_84_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«84».Old.«42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1_old_84_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«84».Old.«42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_84_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«84».Old.«42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4_old_84_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«84».New.«84_eta_1m3_2p7_3p1_4m2_6m2_12p1_14p4_28m2_42m1_84p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«84».New.«84_eta_1m3_2p7_3p2_4m2_6m3_7p1_12p1_14m3_21m2_28p2_42p7_84m3»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«84».New.«84_eta_1m3_2p8_4m3_7m1_14p2_21p2_28m1_42m2_84p2»
public import WeightTwoCusps.Basis.Constructor

/-!
# An eta-quotient basis at level 84

Entries follow `Basis_cuspidal_eta_S2` in
[the local level table](../TABLE.md#level-84), in its original order.

0: `cuspForm_14_2_a_a_old_84_1` is the dilation-1 lift
of `cuspForm_14_2_a_a`.

1: `cuspForm_14_2_a_a_old_84_2` is the dilation-2 lift
of `cuspForm_14_2_a_a`.

2: `cuspForm_14_2_a_a_old_84_3` is the dilation-3 lift
of `cuspForm_14_2_a_a`.

3: `cuspForm_14_2_a_a_old_84_6` is the dilation-6 lift
of `cuspForm_14_2_a_a`.

4: `cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_84_1` is the dilation-1 lift
of `cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1`.

5: `cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4_old_84_1` is the dilation-1 lift
of `cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4`.

6: `cuspForm_42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1_old_84_1` is the dilation-1 lift
of `cuspForm_42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1`.

7: `cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_84_2` is the dilation-2 lift
of `cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1`.

8: `cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4_old_84_2` is the dilation-2 lift
of `cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4`.

9: `cuspForm_84_eta_1m3_2p7_3p1_4m2_6m2_12p1_14p4_28m2_42m1_84p1` is a directly defined eta basis vector.

10: `cuspForm_84_eta_1m3_2p7_3p2_4m2_6m3_7p1_12p1_14m3_21m2_28p2_42p7_84m3` is a directly defined eta basis vector.

Additional imported source forms for higher levels are not appended to
this table-ordered basis:
- `cuspForm_84_eta_1m3_2p8_4m3_7m1_14p2_21p2_28m1_42m2_84p2`

Direct eta entries are not asserted to be normalized Hecke newforms or
members of the canonical newspace. The constructor certifies the full basis.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The complete cuspidal eta basis of `S₂(Γ₀(84))`, in report order. -/
@[eta_simps] def level_84_etaBasis : Module.Basis (Fin 11) ℂ (gamma0CuspForms 84) :=
  cuspFormBasis ![
    cuspForm_14_2_a_a_old_84_1,
    cuspForm_14_2_a_a_old_84_2,
    cuspForm_14_2_a_a_old_84_3,
    cuspForm_14_2_a_a_old_84_6,
    cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_84_1,
    cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4_old_84_1,
    cuspForm_42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1_old_84_1,
    cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_84_2,
    cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4_old_84_2,
    cuspForm_84_eta_1m3_2p7_3p1_4m2_6m2_12p1_14p4_28m2_42m1_84p1,
    cuspForm_84_eta_1m3_2p7_3p2_4m2_6m3_7p1_12p1_14m3_21m2_28p2_42p7_84m3]

end WeightTwoCusps
