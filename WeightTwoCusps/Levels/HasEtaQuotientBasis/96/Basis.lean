module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«96».Old.«24_2_a_a_old_96_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«96».Old.«24_2_a_a_old_96_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«96».Old.«24_2_a_a_old_96_4»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«96».Old.«32_2_a_a_old_96_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«96».Old.«32_2_a_a_old_96_3»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«96».Old.«48_eta_1m2_2p4_3p2_6m2_12p2_old_96_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«96».Old.«48_eta_1m2_2p4_3p2_6m2_12p2_old_96_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«96».New.«96_eta_2p1_6p1_16p1_48p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«96».New.«96_eta_1m2_2p2_3p2_4p3_8m1_12m1_24p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«96».New.«96_eta_1m3_2p9_3p1_4m4_6m3_8p2_12p2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«96».New.«96_eta_1m2_2p3_3p2_4p1_6m1_8m1_16p2_24p1_32m1_48m1_96p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«96».New.«96_eta_1m3_2p7_3p1_4m2_6m1_24p2»
public import WeightTwoCusps.Basis.Constructor

/-!
# An eta-quotient basis at level 96

Entries follow `Basis_cuspidal_eta_S2` in
[the local level table](../TABLE.md#level-96), in its original order.

0: `cuspForm_24_2_a_a_old_96_1` is the dilation-1 lift
of `cuspForm_24_2_a_a`.

1: `cuspForm_24_2_a_a_old_96_2` is the dilation-2 lift
of `cuspForm_24_2_a_a`.

2: `cuspForm_24_2_a_a_old_96_4` is the dilation-4 lift
of `cuspForm_24_2_a_a`.

3: `cuspForm_32_2_a_a_old_96_1` is the dilation-1 lift
of `cuspForm_32_2_a_a`.

4: `cuspForm_32_2_a_a_old_96_3` is the dilation-3 lift
of `cuspForm_32_2_a_a`.

5: `cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2_old_96_1` is the dilation-1 lift
of `cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2`.

6: `cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2_old_96_2` is the dilation-2 lift
of `cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2`.

7: `cuspForm_96_eta_2p1_6p1_16p1_48p1` is a directly defined eta basis vector.

8: `cuspForm_96_eta_1m2_2p2_3p2_4p3_8m1_12m1_24p1` is a directly defined eta basis vector.

Additional imported source forms for higher levels are not appended to
this table-ordered basis:
- `cuspForm_96_eta_1m3_2p9_3p1_4m4_6m3_8p2_12p2`
- `cuspForm_96_eta_1m2_2p3_3p2_4p1_6m1_8m1_16p2_24p1_32m1_48m1_96p1`
- `cuspForm_96_eta_1m3_2p7_3p1_4m2_6m1_24p2`

Direct eta entries are not asserted to be normalized Hecke newforms or
members of the canonical newspace. The constructor certifies the full basis.
The coefficient columns are `1, 2, 3, 4, 5, 6, 7, 9, 11`.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The complete cuspidal eta basis of `S₂(Γ₀(96))`, in report order. -/
@[eta_simps] def level_96_etaBasis : Module.Basis (Fin 9) ℂ (gamma0CuspForms 96) :=
  cuspFormBasis ![
    cuspForm_24_2_a_a_old_96_1,
    cuspForm_24_2_a_a_old_96_2,
    cuspForm_24_2_a_a_old_96_4,
    cuspForm_32_2_a_a_old_96_1,
    cuspForm_32_2_a_a_old_96_3,
    cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2_old_96_1,
    cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2_old_96_2,
    cuspForm_96_eta_2p1_6p1_16p1_48p1,
    cuspForm_96_eta_1m2_2p2_3p2_4p3_8m1_12m1_24p1] (c := ![1, 2, 3, 4, 5, 6, 7, 9, 11])

end WeightTwoCusps
