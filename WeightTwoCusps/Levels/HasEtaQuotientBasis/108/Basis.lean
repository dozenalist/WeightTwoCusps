module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«108».Old.«27_2_a_a_old_108_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«108».Old.«27_2_a_a_old_108_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«108».Old.«27_2_a_a_old_108_4»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«108».Old.«36_2_a_a_old_108_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«108».Old.«36_2_a_a_old_108_3»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«108».Old.«54_eta_1m1_2p2_6p2_9p1_old_108_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«108».Old.«54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_108_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«108».Old.«54_eta_1m1_2p2_6p2_9p1_old_108_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«108».Old.«54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_108_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«108».New.«108_eta_2p3_18p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«108».New.«108_eta_1m6_2p15_3p2_4m6_6m4_12p2_18p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«108».New.«108_eta_1m4_2p8_3p4_4m3_6m3_12p1_18p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«108».New.«108_eta_1m4_2p10_3p1_4m4_6m2_9p1_12p1_36p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«108».New.«108_eta_1m3_2p3_3p7_6m3_9m2_18p2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«108».New.«108_eta_1m3_2p5_3p4_4m1_6m2_9m1_18p1_36p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«108».New.«108_eta_1m2_2p1_3p6_6m2_18p1»
public import WeightTwoCusps.Basis.Constructor

/-!
# An eta-quotient basis at level 108

Entries follow `Basis_cuspidal_eta_S2` in
[the local level table](../TABLE.md#level-108), in its original order.

0: `cuspForm_27_2_a_a_old_108_1` is the dilation-1 lift
of `cuspForm_27_2_a_a`.

1: `cuspForm_27_2_a_a_old_108_2` is the dilation-2 lift
of `cuspForm_27_2_a_a`.

2: `cuspForm_27_2_a_a_old_108_4` is the dilation-4 lift
of `cuspForm_27_2_a_a`.

3: `cuspForm_36_2_a_a_old_108_1` is the dilation-1 lift
of `cuspForm_36_2_a_a`.

4: `cuspForm_36_2_a_a_old_108_3` is the dilation-3 lift
of `cuspForm_36_2_a_a`.

5: `cuspForm_54_eta_1m1_2p2_6p2_9p1_old_108_1` is the dilation-1 lift
of `cuspForm_54_eta_1m1_2p2_6p2_9p1`.

6: `cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_108_1` is the dilation-1 lift
of `cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1`.

7: `cuspForm_54_eta_1m1_2p2_6p2_9p1_old_108_2` is the dilation-2 lift
of `cuspForm_54_eta_1m1_2p2_6p2_9p1`.

8: `cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_108_2` is the dilation-2 lift
of `cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1`.

9: `cuspForm_108_eta_2p3_18p1` is a directly defined eta basis vector.

Additional imported source forms for higher levels are not appended to
this table-ordered basis:
- `cuspForm_108_eta_1m6_2p15_3p2_4m6_6m4_12p2_18p1`
- `cuspForm_108_eta_1m4_2p8_3p4_4m3_6m3_12p1_18p1`
- `cuspForm_108_eta_1m4_2p10_3p1_4m4_6m2_9p1_12p1_36p1`
- `cuspForm_108_eta_1m3_2p3_3p7_6m3_9m2_18p2`
- `cuspForm_108_eta_1m3_2p5_3p4_4m1_6m2_9m1_18p1_36p1`
- `cuspForm_108_eta_1m2_2p1_3p6_6m2_18p1`

Direct eta entries are not asserted to be normalized Hecke newforms or
members of the canonical newspace. The constructor certifies the full basis.
The coefficient columns are `1, 2, 3, 4, 5, 7, 8, 10, 13, 19`.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The complete cuspidal eta basis of `S₂(Γ₀(108))`, in report order. -/
@[eta_simps] def level_108_etaBasis : Module.Basis (Fin 10) ℂ (gamma0CuspForms 108) :=
  cuspFormBasis ![
    cuspForm_27_2_a_a_old_108_1,
    cuspForm_27_2_a_a_old_108_2,
    cuspForm_27_2_a_a_old_108_4,
    cuspForm_36_2_a_a_old_108_1,
    cuspForm_36_2_a_a_old_108_3,
    cuspForm_54_eta_1m1_2p2_6p2_9p1_old_108_1,
    cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_108_1,
    cuspForm_54_eta_1m1_2p2_6p2_9p1_old_108_2,
    cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_108_2,
    cuspForm_108_eta_2p3_18p1] (c := ![1, 2, 3, 4, 5, 7, 8, 10, 13, 19])

end WeightTwoCusps
