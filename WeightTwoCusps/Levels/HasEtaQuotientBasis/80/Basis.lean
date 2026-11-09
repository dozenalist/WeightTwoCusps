module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«80».Old.«20_2_a_a_old_80_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«80».Old.«20_2_a_a_old_80_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«80».Old.«20_2_a_a_old_80_4»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«80».Old.«40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_80_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«80».Old.«40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_80_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«80».New.«80_eta_1m2_2p5_4m1_5m2_10p5_20m1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«80».New.«80_eta_1m1_2p1_4p2_5p1_10p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«80».New.«80_eta_1m2_2p5_4m1_20m1_40p5_80m2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«80».New.«80_eta_1m1_2p2_4m1_5p1_8p3_16m1_20p1_40m1_80p1»
public import WeightTwoCusps.Basis.Constructor

/-!
# An eta-quotient basis at level 80

Entries follow `Basis_cuspidal_eta_S2` in
[the local level table](../TABLE.md#level-80), in its original order.

0: `cuspForm_20_2_a_a_old_80_1` is the dilation-1 lift
of `cuspForm_20_2_a_a`.

1: `cuspForm_20_2_a_a_old_80_2` is the dilation-2 lift
of `cuspForm_20_2_a_a`.

2: `cuspForm_20_2_a_a_old_80_4` is the dilation-4 lift
of `cuspForm_20_2_a_a`.

3: `cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_80_1` is the dilation-1 lift
of `cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1`.

4: `cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_80_2` is the dilation-2 lift
of `cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1`.

5: `cuspForm_80_eta_1m2_2p5_4m1_5m2_10p5_20m1` is a directly defined eta basis vector.

6: `cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1` is a directly defined eta basis vector.

Additional imported source forms for higher levels are not appended to
this table-ordered basis:
- `cuspForm_80_eta_1m2_2p5_4m1_20m1_40p5_80m2`
- `cuspForm_80_eta_1m1_2p2_4m1_5p1_8p3_16m1_20p1_40m1_80p1`

Direct eta entries are not asserted to be normalized Hecke newforms or
members of the canonical newspace. The constructor certifies the full basis.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The complete cuspidal eta basis of `S₂(Γ₀(80))`, in report order. -/
@[eta_simps] def level_80_etaBasis : Module.Basis (Fin 7) ℂ (gamma0CuspForms 80) :=
  cuspFormBasis ![
    cuspForm_20_2_a_a_old_80_1,
    cuspForm_20_2_a_a_old_80_2,
    cuspForm_20_2_a_a_old_80_4,
    cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_80_1,
    cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_80_2,
    cuspForm_80_eta_1m2_2p5_4m1_5m2_10p5_20m1,
    cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1]

end WeightTwoCusps
