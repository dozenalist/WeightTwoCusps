module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«112».Old.«14_2_a_a_old_112_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«112».Old.«14_2_a_a_old_112_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«112».Old.«14_2_a_a_old_112_4»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«112».Old.«14_2_a_a_old_112_8»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«112».Old.«56_eta_1p1_7p1_8p1_56p1_old_112_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«112».Old.«56_eta_2m1_4p3_14p3_28m1_old_112_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«112».Old.«56_eta_1p1_7p1_8p1_56p1_old_112_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«112».Old.«56_eta_2m1_4p3_14p3_28m1_old_112_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«112».New.«112_eta_1m3_2p7_4m2_7p1_14p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«112».New.«112_eta_1m2_2p4_7p2_14m2_28p2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«112».New.«112_eta_1m2_2p5_4m2_8p2_16m1_56p1_112p1»
public import WeightTwoCusps.Basis.Constructor

/-!
# An eta-quotient basis at level 112

Entries follow `Basis_cuspidal_eta_S2` in
[the local level table](../TABLE.md#level-112), in its original order.

0: `cuspForm_14_2_a_a_old_112_1` is the dilation-1 lift
of `cuspForm_14_2_a_a`.

1: `cuspForm_14_2_a_a_old_112_2` is the dilation-2 lift
of `cuspForm_14_2_a_a`.

2: `cuspForm_14_2_a_a_old_112_4` is the dilation-4 lift
of `cuspForm_14_2_a_a`.

3: `cuspForm_14_2_a_a_old_112_8` is the dilation-8 lift
of `cuspForm_14_2_a_a`.

4: `cuspForm_56_eta_1p1_7p1_8p1_56p1_old_112_1` is the dilation-1 lift
of `cuspForm_56_eta_1p1_7p1_8p1_56p1`.

5: `cuspForm_56_eta_2m1_4p3_14p3_28m1_old_112_1` is the dilation-1 lift
of `cuspForm_56_eta_2m1_4p3_14p3_28m1`.

6: `cuspForm_56_eta_1p1_7p1_8p1_56p1_old_112_2` is the dilation-2 lift
of `cuspForm_56_eta_1p1_7p1_8p1_56p1`.

7: `cuspForm_56_eta_2m1_4p3_14p3_28m1_old_112_2` is the dilation-2 lift
of `cuspForm_56_eta_2m1_4p3_14p3_28m1`.

8: `cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1` is a directly defined eta basis vector.

9: `cuspForm_112_eta_1m2_2p4_7p2_14m2_28p2` is a directly defined eta basis vector.

10: `cuspForm_112_eta_1m2_2p5_4m2_8p2_16m1_56p1_112p1` is a directly defined eta basis vector.

Direct eta entries are not asserted to be normalized Hecke newforms or
members of the canonical newspace. The constructor certifies the full basis.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The complete cuspidal eta basis of `S₂(Γ₀(112))`, in report order. -/
@[eta_simps] def level_112_etaBasis : Module.Basis (Fin 11) ℂ (gamma0CuspForms 112) :=
  cuspFormBasis ![
    cuspForm_14_2_a_a_old_112_1,
    cuspForm_14_2_a_a_old_112_2,
    cuspForm_14_2_a_a_old_112_4,
    cuspForm_14_2_a_a_old_112_8,
    cuspForm_56_eta_1p1_7p1_8p1_56p1_old_112_1,
    cuspForm_56_eta_2m1_4p3_14p3_28m1_old_112_1,
    cuspForm_56_eta_1p1_7p1_8p1_56p1_old_112_2,
    cuspForm_56_eta_2m1_4p3_14p3_28m1_old_112_2,
    cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1,
    cuspForm_112_eta_1m2_2p4_7p2_14m2_28p2,
    cuspForm_112_eta_1m2_2p5_4m2_8p2_16m1_56p1_112p1]

end WeightTwoCusps
