module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«100».Old.«20_2_a_a_old_100_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«100».Old.«20_2_a_a_old_100_5»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«100».New.«100_eta_2p1_10p2_50p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«100».New.«100_eta_1m1_2p2_4m1_5p2_20p2_25m1_50p2_100m1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«100».New.«100_eta_1m1_2p2_10p2_25p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«100».New.«100_eta_1m1_2p3_4m1_10p2_25p1_50m1_100p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«100».New.«100_eta_2m1_4p1_10p6_20m2_50m1_100p1»
public import WeightTwoCusps.Basis.Constructor

/-!
# An eta-quotient basis at level 100

Entries follow `Basis_cuspidal_eta_S2` in
[the local level table](../TABLE.md#level-100), in its original order.

0: `cuspForm_20_2_a_a_old_100_1` is the dilation-1 lift
of `cuspForm_20_2_a_a`.

1: `cuspForm_20_2_a_a_old_100_5` is the dilation-5 lift
of `cuspForm_20_2_a_a`.

2: `cuspForm_100_eta_2p1_10p2_50p1` is a directly defined eta basis vector.

3: `cuspForm_100_eta_1m1_2p2_4m1_5p2_20p2_25m1_50p2_100m1` is a directly defined eta basis vector.

4: `cuspForm_100_eta_1m1_2p2_10p2_25p1` is a directly defined eta basis vector.

5: `cuspForm_100_eta_1m1_2p3_4m1_10p2_25p1_50m1_100p1` is a directly defined eta basis vector.

6: `cuspForm_100_eta_2m1_4p1_10p6_20m2_50m1_100p1` is a directly defined eta basis vector.

Direct eta entries are not asserted to be normalized Hecke newforms or
members of the canonical newspace. The constructor certifies the full basis.
The coefficient columns are `1, 2, 3, 4, 5, 7, 9`.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The complete cuspidal eta basis of `S₂(Γ₀(100))`, in report order. -/
@[eta_simps] def level_100_etaBasis : Module.Basis (Fin 7) ℂ (gamma0CuspForms 100) :=
  cuspFormBasis ![
    cuspForm_20_2_a_a_old_100_1,
    cuspForm_20_2_a_a_old_100_5,
    cuspForm_100_eta_2p1_10p2_50p1,
    cuspForm_100_eta_1m1_2p2_4m1_5p2_20p2_25m1_50p2_100m1,
    cuspForm_100_eta_1m1_2p2_10p2_25p1,
    cuspForm_100_eta_1m1_2p3_4m1_10p2_25p1_50m1_100p1,
    cuspForm_100_eta_2m1_4p1_10p6_20m2_50m1_100p1] (c := ![1, 2, 3, 4, 5, 7, 9])

end WeightTwoCusps
