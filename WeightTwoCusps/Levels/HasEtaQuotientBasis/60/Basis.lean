module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«60».Old.«15_2_a_a_old_60_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«60».Old.«15_2_a_a_old_60_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«60».Old.«15_2_a_a_old_60_4»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«60».Old.«20_2_a_a_old_60_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«60».Old.«20_2_a_a_old_60_3»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«60».Old.«30_eta_1p1_2p1_15p1_30p1_old_60_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«60».Old.«30_eta_1p1_2p1_15p1_30p1_old_60_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«60».New.«60_eta_1m3_2p6_3p3_4m2_5p3_6m3_10m3_12p1_15m3_20p1_30p6_60m2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«60».New.«60_eta_1m3_2p7_3p2_4m2_5p2_6m3_10m3_12p1_15m3_20p1_30p7_60m2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«60».New.«60_eta_1m3_2p8_3p1_4m3_5m3_6m2_10p8_12p1_15p1_20m3_30m2_60p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«60».New.«60_eta_1m3_2p8_3p1_4m3_5m1_6m2_10p1_12p1_15p3_30m1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«60».New.«60_eta_1m2_2p3_3p3_4m1_5p3_6m2_10m2_12p1_15m2_20p1_30p3_60m1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«60».New.«60_eta_1m2_2p4_3p2_4m1_5p2_6m2_10m2_12p1_15m2_20p1_30p4_60m1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«60».New.«60_eta_1m1_3p2_4p1_5p2_6p1_10p1_12m1_15m1_20m1_60p1»
public import WeightTwoCusps.Basis.Constructor

/-!
# An eta-quotient basis at level 60

Entries follow `Basis_cuspidal_eta_S2` in
[the local level table](../TABLE.md#level-60), in its original order.

0: `cuspForm_15_2_a_a_old_60_1` is the dilation-1 lift
of `cuspForm_15_2_a_a`.

1: `cuspForm_15_2_a_a_old_60_2` is the dilation-2 lift
of `cuspForm_15_2_a_a`.

2: `cuspForm_15_2_a_a_old_60_4` is the dilation-4 lift
of `cuspForm_15_2_a_a`.

3: `cuspForm_20_2_a_a_old_60_1` is the dilation-1 lift
of `cuspForm_20_2_a_a`.

4: `cuspForm_20_2_a_a_old_60_3` is the dilation-3 lift
of `cuspForm_20_2_a_a`.

5: `cuspForm_30_eta_1p1_2p1_15p1_30p1_old_60_1` is the dilation-1 lift
of `cuspForm_30_eta_1p1_2p1_15p1_30p1`.

6: `cuspForm_30_eta_1p1_2p1_15p1_30p1_old_60_2` is the dilation-2 lift
of `cuspForm_30_eta_1p1_2p1_15p1_30p1`.

Additional imported source forms for higher levels are not appended to
this table-ordered basis:
- `cuspForm_60_eta_1m3_2p6_3p3_4m2_5p3_6m3_10m3_12p1_15m3_20p1_30p6_60m2`
- `cuspForm_60_eta_1m3_2p7_3p2_4m2_5p2_6m3_10m3_12p1_15m3_20p1_30p7_60m2`
- `cuspForm_60_eta_1m3_2p8_3p1_4m3_5m3_6m2_10p8_12p1_15p1_20m3_30m2_60p1`
- `cuspForm_60_eta_1m3_2p8_3p1_4m3_5m1_6m2_10p1_12p1_15p3_30m1`
- `cuspForm_60_eta_1m2_2p3_3p3_4m1_5p3_6m2_10m2_12p1_15m2_20p1_30p3_60m1`
- `cuspForm_60_eta_1m2_2p4_3p2_4m1_5p2_6m2_10m2_12p1_15m2_20p1_30p4_60m1`
- `cuspForm_60_eta_1m1_3p2_4p1_5p2_6p1_10p1_12m1_15m1_20m1_60p1`

Direct eta entries are not asserted to be normalized Hecke newforms or
members of the canonical newspace. The constructor certifies the full basis.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The complete cuspidal eta basis of `S₂(Γ₀(60))`, in report order. -/
@[eta_simps] def level_60_etaBasis : Module.Basis (Fin 7) ℂ (gamma0CuspForms 60) :=
  cuspFormBasis ![
    cuspForm_15_2_a_a_old_60_1,
    cuspForm_15_2_a_a_old_60_2,
    cuspForm_15_2_a_a_old_60_4,
    cuspForm_20_2_a_a_old_60_1,
    cuspForm_20_2_a_a_old_60_3,
    cuspForm_30_eta_1p1_2p1_15p1_30p1_old_60_1,
    cuspForm_30_eta_1p1_2p1_15p1_30p1_old_60_2]

end WeightTwoCusps
