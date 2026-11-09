module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«162».Old.«27_2_a_a_old_162_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«162».Old.«27_2_a_a_old_162_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«162».Old.«27_2_a_a_old_162_3»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«162».Old.«27_2_a_a_old_162_6»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«162».Old.«54_eta_1m1_2p2_6p2_9p1_old_162_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«162».Old.«54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_162_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«162».Old.«54_eta_1m1_2p2_6p2_9p1_old_162_3»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«162».Old.«54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_162_3»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«162».Old.«81_eta_3m1_9p6_27m1_old_162_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«162».Old.«81_eta_3p1_9p2_27p1_old_162_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«162».Old.«81_eta_3m1_9p6_27m1_old_162_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«162».Old.«81_eta_3p1_9p2_27p1_old_162_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«162».New.«162_eta_1m1_2p2_3m1_6p2_9p1_27p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«162».New.«162_eta_1m1_2p2_6m1_9p1_18p4_54m1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«162».New.«162_eta_1m1_2p2_6m1_9p2_18p2_27m1_81p2_162m1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«162».New.«162_eta_1m1_2p2_3p1_6m1_18p1_27p2»
public import WeightTwoCusps.Basis.Constructor

/-!
# An eta-quotient basis at level 162

Entries follow `Basis_cuspidal_eta_S2` in
[the local level table](../TABLE.md#level-162), in its original order.

0: `cuspForm_27_2_a_a_old_162_1` is the dilation-1 lift
of `cuspForm_27_2_a_a`.

1: `cuspForm_27_2_a_a_old_162_2` is the dilation-2 lift
of `cuspForm_27_2_a_a`.

2: `cuspForm_27_2_a_a_old_162_3` is the dilation-3 lift
of `cuspForm_27_2_a_a`.

3: `cuspForm_27_2_a_a_old_162_6` is the dilation-6 lift
of `cuspForm_27_2_a_a`.

4: `cuspForm_54_eta_1m1_2p2_6p2_9p1_old_162_1` is the dilation-1 lift
of `cuspForm_54_eta_1m1_2p2_6p2_9p1`.

5: `cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_162_1` is the dilation-1 lift
of `cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1`.

6: `cuspForm_54_eta_1m1_2p2_6p2_9p1_old_162_3` is the dilation-3 lift
of `cuspForm_54_eta_1m1_2p2_6p2_9p1`.

7: `cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_162_3` is the dilation-3 lift
of `cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1`.

8: `cuspForm_81_eta_3m1_9p6_27m1_old_162_1` is the dilation-1 lift
of `cuspForm_81_eta_3m1_9p6_27m1`.

9: `cuspForm_81_eta_3p1_9p2_27p1_old_162_1` is the dilation-1 lift
of `cuspForm_81_eta_3p1_9p2_27p1`.

10: `cuspForm_81_eta_3m1_9p6_27m1_old_162_2` is the dilation-2 lift
of `cuspForm_81_eta_3m1_9p6_27m1`.

11: `cuspForm_81_eta_3p1_9p2_27p1_old_162_2` is the dilation-2 lift
of `cuspForm_81_eta_3p1_9p2_27p1`.

12: `cuspForm_162_eta_1m1_2p2_3m1_6p2_9p1_27p1` is a directly defined eta basis vector.

13: `cuspForm_162_eta_1m1_2p2_6m1_9p1_18p4_54m1` is a directly defined eta basis vector.

14: `cuspForm_162_eta_1m1_2p2_6m1_9p2_18p2_27m1_81p2_162m1` is a directly defined eta basis vector.

15: `cuspForm_162_eta_1m1_2p2_3p1_6m1_18p1_27p2` is a directly defined eta basis vector.

Direct eta entries are not asserted to be normalized Hecke newforms or
members of the canonical newspace. The constructor certifies the full basis.
The coefficient columns are `1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17`.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The complete cuspidal eta basis of `S₂(Γ₀(162))`, in report order. -/
@[eta_simps] def level_162_etaBasis : Module.Basis (Fin 16) ℂ (gamma0CuspForms 162) :=
  cuspFormBasis ![
    cuspForm_27_2_a_a_old_162_1,
    cuspForm_27_2_a_a_old_162_2,
    cuspForm_27_2_a_a_old_162_3,
    cuspForm_27_2_a_a_old_162_6,
    cuspForm_54_eta_1m1_2p2_6p2_9p1_old_162_1,
    cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_162_1,
    cuspForm_54_eta_1m1_2p2_6p2_9p1_old_162_3,
    cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_162_3,
    cuspForm_81_eta_3m1_9p6_27m1_old_162_1,
    cuspForm_81_eta_3p1_9p2_27p1_old_162_1,
    cuspForm_81_eta_3m1_9p6_27m1_old_162_2,
    cuspForm_81_eta_3p1_9p2_27p1_old_162_2,
    cuspForm_162_eta_1m1_2p2_3m1_6p2_9p1_27p1,
    cuspForm_162_eta_1m1_2p2_6m1_9p1_18p4_54m1,
    cuspForm_162_eta_1m1_2p2_6m1_9p2_18p2_27m1_81p2_162m1,
    cuspForm_162_eta_1m1_2p2_3p1_6m1_18p1_27p2] (c := ![1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17])

end WeightTwoCusps
