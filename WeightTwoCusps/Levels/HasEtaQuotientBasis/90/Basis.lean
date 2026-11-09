module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«90».Old.«15_2_a_a_old_90_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«90».Old.«15_2_a_a_old_90_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«90».Old.«15_2_a_a_old_90_3»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«90».Old.«15_2_a_a_old_90_6»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«90».Old.«30_eta_1p1_2p1_15p1_30p1_old_90_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«90».Old.«30_eta_1p1_2p1_15p1_30p1_old_90_3»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«90».New.«90_eta_1m2_2p1_3p7_6m3_9m2_15p1_18p1_30p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«90».New.«90_eta_1m2_2p3_3p2_5p1_6m1_15p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«90».New.«90_eta_1m1_2p1_3p1_5p1_6p1_9p1_18m1_90p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«90».New.«90_eta_1m1_2p2_9p1_15p3_30m1_45m1_90p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«90».New.«90_eta_1m1_2p2_6p1_9p1_18m1_30p1_90p1»
public import WeightTwoCusps.Basis.Constructor

/-!
# An eta-quotient basis at level 90

Entries follow `Basis_cuspidal_eta_S2` in
[the local level table](../TABLE.md#level-90), in its original order.

0: `cuspForm_15_2_a_a_old_90_1` is the dilation-1 lift
of `cuspForm_15_2_a_a`.

1: `cuspForm_15_2_a_a_old_90_2` is the dilation-2 lift
of `cuspForm_15_2_a_a`.

2: `cuspForm_15_2_a_a_old_90_3` is the dilation-3 lift
of `cuspForm_15_2_a_a`.

3: `cuspForm_15_2_a_a_old_90_6` is the dilation-6 lift
of `cuspForm_15_2_a_a`.

4: `cuspForm_30_eta_1p1_2p1_15p1_30p1_old_90_1` is the dilation-1 lift
of `cuspForm_30_eta_1p1_2p1_15p1_30p1`.

5: `cuspForm_30_eta_1p1_2p1_15p1_30p1_old_90_3` is the dilation-3 lift
of `cuspForm_30_eta_1p1_2p1_15p1_30p1`.

6: `cuspForm_90_eta_1m2_2p1_3p7_6m3_9m2_15p1_18p1_30p1` is a directly defined eta basis vector.

7: `cuspForm_90_eta_1m2_2p3_3p2_5p1_6m1_15p1` is a directly defined eta basis vector.

8: `cuspForm_90_eta_1m1_2p1_3p1_5p1_6p1_9p1_18m1_90p1` is a directly defined eta basis vector.

9: `cuspForm_90_eta_1m1_2p2_9p1_15p3_30m1_45m1_90p1` is a directly defined eta basis vector.

10: `cuspForm_90_eta_1m1_2p2_6p1_9p1_18m1_30p1_90p1` is a directly defined eta basis vector.

Direct eta entries are not asserted to be normalized Hecke newforms or
members of the canonical newspace. The constructor certifies the full basis.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The complete cuspidal eta basis of `S₂(Γ₀(90))`, in report order. -/
@[eta_simps] def level_90_etaBasis : Module.Basis (Fin 11) ℂ (gamma0CuspForms 90) :=
  cuspFormBasis ![
    cuspForm_15_2_a_a_old_90_1,
    cuspForm_15_2_a_a_old_90_2,
    cuspForm_15_2_a_a_old_90_3,
    cuspForm_15_2_a_a_old_90_6,
    cuspForm_30_eta_1p1_2p1_15p1_30p1_old_90_1,
    cuspForm_30_eta_1p1_2p1_15p1_30p1_old_90_3,
    cuspForm_90_eta_1m2_2p1_3p7_6m3_9m2_15p1_18p1_30p1,
    cuspForm_90_eta_1m2_2p3_3p2_5p1_6m1_15p1,
    cuspForm_90_eta_1m1_2p1_3p1_5p1_6p1_9p1_18m1_90p1,
    cuspForm_90_eta_1m1_2p2_9p1_15p3_30m1_45m1_90p1,
    cuspForm_90_eta_1m1_2p2_6p1_9p1_18m1_30p1_90p1]

end WeightTwoCusps
