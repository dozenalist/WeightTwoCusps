module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«144».New.«144_eta_1m4_2p10_4m4_12p2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«144».New.«144_eta_1m3_2p6_3p1_4p1_6m2_8m2_12p1_24p2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«144».Old.«72_eta_1m3_2p7_3p1_4m2_6m1_12p2_old_144_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«144».New.«144_eta_1m2_2p1_3p2_4p6_6m1_8m3_24p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«144».New.«144_eta_1m2_2p1_3p8_6m4_9m2_12p2_18p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«144».New.«144_eta_1m2_2p3_3p2_4p1_6m2_8m1_12p2_18p1_36m1_72p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«144».New.«144_eta_1m2_2p3_3p3_4m1_6m1_9m1_12p1_18p1_24p2_48m1_72m1_144p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«144».New.«144_eta_1m2_2p3_3p5_4m1_6m3_9m1_12p2_36p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«144».New.«144_eta_1m2_2p5_3m1_4m2_6p2_9p1_12p1_18m1_36p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«144».New.«144_eta_1m2_2p5_4m4_8p5_12p2_16m2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«144».New.«144_eta_1m1_2m1_3p1_4p6_8m1_16m1_48p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«144».New.«144_eta_1m1_3p2_4p1_6p2_9m1_36p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«144».Old.«72_eta_1m1_3p3_4p1_12p1_old_144_1»
public import WeightTwoCusps.Basis.Constructor

/-!
# An eta-quotient basis at level 144

Entries follow `Basis_cuspidal_eta_S2` in
[the local level table](../TABLE.md#level-144), in its original order.

0: `cuspForm_144_eta_1m4_2p10_4m4_12p2` is a directly defined eta basis vector.

1: `cuspForm_144_eta_1m3_2p6_3p1_4p1_6m2_8m2_12p1_24p2` is a directly defined eta basis vector.

2: `cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2_old_144_1` is the dilation-1 lift
of `cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2`.

3: `cuspForm_144_eta_1m2_2p1_3p2_4p6_6m1_8m3_24p1` is a directly defined eta basis vector.

4: `cuspForm_144_eta_1m2_2p1_3p8_6m4_9m2_12p2_18p1` is a directly defined eta basis vector.

5: `cuspForm_144_eta_1m2_2p3_3p2_4p1_6m2_8m1_12p2_18p1_36m1_72p1` is a directly defined eta basis vector.

6: `cuspForm_144_eta_1m2_2p3_3p3_4m1_6m1_9m1_12p1_18p1_24p2_48m1_72m1_144p1` is a directly defined eta basis vector.

7: `cuspForm_144_eta_1m2_2p3_3p5_4m1_6m3_9m1_12p2_36p1` is a directly defined eta basis vector.

8: `cuspForm_144_eta_1m2_2p5_3m1_4m2_6p2_9p1_12p1_18m1_36p1` is a directly defined eta basis vector.

9: `cuspForm_144_eta_1m2_2p5_4m4_8p5_12p2_16m2` is a directly defined eta basis vector.

10: `cuspForm_144_eta_1m1_2m1_3p1_4p6_8m1_16m1_48p1` is a directly defined eta basis vector.

11: `cuspForm_144_eta_1m1_3p2_4p1_6p2_9m1_36p1` is a directly defined eta basis vector.

12: `cuspForm_72_eta_1m1_3p3_4p1_12p1_old_144_1` is the dilation-1 lift
of `cuspForm_72_eta_1m1_3p3_4p1_12p1`.

Direct eta entries are not asserted to be normalized Hecke newforms or
members of the canonical newspace. The constructor certifies the full basis.
The coefficient columns are `1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 14, 19`.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The complete cuspidal eta basis of `S₂(Γ₀(144))`, in report order. -/
@[eta_simps] def level_144_etaBasis : Module.Basis (Fin 13) ℂ (gamma0CuspForms 144) :=
  cuspFormBasis ![
    cuspForm_144_eta_1m4_2p10_4m4_12p2,
    cuspForm_144_eta_1m3_2p6_3p1_4p1_6m2_8m2_12p1_24p2,
    cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2_old_144_1,
    cuspForm_144_eta_1m2_2p1_3p2_4p6_6m1_8m3_24p1,
    cuspForm_144_eta_1m2_2p1_3p8_6m4_9m2_12p2_18p1,
    cuspForm_144_eta_1m2_2p3_3p2_4p1_6m2_8m1_12p2_18p1_36m1_72p1,
    cuspForm_144_eta_1m2_2p3_3p3_4m1_6m1_9m1_12p1_18p1_24p2_48m1_72m1_144p1,
    cuspForm_144_eta_1m2_2p3_3p5_4m1_6m3_9m1_12p2_36p1,
    cuspForm_144_eta_1m2_2p5_3m1_4m2_6p2_9p1_12p1_18m1_36p1,
    cuspForm_144_eta_1m2_2p5_4m4_8p5_12p2_16m2,
    cuspForm_144_eta_1m1_2m1_3p1_4p6_8m1_16m1_48p1,
    cuspForm_144_eta_1m1_3p2_4p1_6p2_9m1_36p1,
    cuspForm_72_eta_1m1_3p3_4p1_12p1_old_144_1] (c := ![1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 14, 19])

end WeightTwoCusps
