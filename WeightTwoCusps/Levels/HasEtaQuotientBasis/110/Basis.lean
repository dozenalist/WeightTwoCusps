module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«110».Old.«11_2_a_a_old_110_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«110».Old.«11_2_a_a_old_110_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«110».Old.«11_2_a_a_old_110_5»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«110».Old.«11_2_a_a_old_110_10»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«110».Old.«55_eta_1p1_5p1_11p1_55p1_old_110_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«110».Old.«55_eta_1p1_5p1_11p1_55p1_old_110_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«110».New.«110_eta_1p2_2m1_5m1_10p2_11m1_22p2_55p2_110m1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«110».New.«110_eta_1m1_2p2_10p1_11p1_55p2_110m1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«110».New.«110_eta_2p1_5m1_10p2_11p2_22m1_55p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«110».New.«110_eta_1m1_2p2_5p1_11m1_22p2_55p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«110».New.«110_eta_1p1_5m1_10p2_11p1_55m1_110p2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«110».New.«110_eta_1p1_2p1_55p1_110p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«110».New.«110_eta_5p1_10p1_11p1_22p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«110».New.«110_eta_1p1_2m1_5m1_10p3_11m1_22p3_55p1_110m1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«110».New.«110_eta_1p3_2m1_5m1_10p1_11m1_22p1_55p3_110m1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«110».New.«110_eta_1m1_2p1_5p3_10m1_11p3_22m1_55m1_110p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«110».New.«110_eta_1m1_2p2_5p2_10m1_11p2_22m1_55m1_110p2»
public import WeightTwoCusps.Basis.Constructor

/-!
# An eta-quotient basis at level 110

Entries follow `Basis_cuspidal_eta_S2` in
[the local level table](../TABLE.md#level-110), in its original order.

0: `cuspForm_11_2_a_a_old_110_1` is the dilation-1 lift
of `cuspForm_11_2_a_a`.

1: `cuspForm_11_2_a_a_old_110_2` is the dilation-2 lift
of `cuspForm_11_2_a_a`.

2: `cuspForm_11_2_a_a_old_110_5` is the dilation-5 lift
of `cuspForm_11_2_a_a`.

3: `cuspForm_11_2_a_a_old_110_10` is the dilation-10 lift
of `cuspForm_11_2_a_a`.

4: `cuspForm_55_eta_1p1_5p1_11p1_55p1_old_110_1` is the dilation-1 lift
of `cuspForm_55_eta_1p1_5p1_11p1_55p1`.

5: `cuspForm_55_eta_1p1_5p1_11p1_55p1_old_110_2` is the dilation-2 lift
of `cuspForm_55_eta_1p1_5p1_11p1_55p1`.

6: `cuspForm_110_eta_1p2_2m1_5m1_10p2_11m1_22p2_55p2_110m1` is a directly defined eta basis vector.

7: `cuspForm_110_eta_1m1_2p2_10p1_11p1_55p2_110m1` is a directly defined eta basis vector.

8: `cuspForm_110_eta_2p1_5m1_10p2_11p2_22m1_55p1` is a directly defined eta basis vector.

9: `cuspForm_110_eta_1m1_2p2_5p1_11m1_22p2_55p1` is a directly defined eta basis vector.

10: `cuspForm_110_eta_1p1_5m1_10p2_11p1_55m1_110p2` is a directly defined eta basis vector.

11: `cuspForm_110_eta_1p1_2p1_55p1_110p1` is a directly defined eta basis vector.

12: `cuspForm_110_eta_5p1_10p1_11p1_22p1` is a directly defined eta basis vector.

13: `cuspForm_110_eta_1p1_2m1_5m1_10p3_11m1_22p3_55p1_110m1` is a directly defined eta basis vector.

14: `cuspForm_110_eta_1p3_2m1_5m1_10p1_11m1_22p1_55p3_110m1` is a directly defined eta basis vector.

Additional imported source forms for higher levels are not appended to
this table-ordered basis:
- `cuspForm_110_eta_1m1_2p1_5p3_10m1_11p3_22m1_55m1_110p1`
- `cuspForm_110_eta_1m1_2p2_5p2_10m1_11p2_22m1_55m1_110p2`

Direct eta entries are not asserted to be normalized Hecke newforms or
members of the canonical newspace. The constructor certifies the full basis.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The complete cuspidal eta basis of `S₂(Γ₀(110))`, in report order. -/
@[eta_simps] def level_110_etaBasis : Module.Basis (Fin 15) ℂ (gamma0CuspForms 110) :=
  cuspFormBasis ![
    cuspForm_11_2_a_a_old_110_1,
    cuspForm_11_2_a_a_old_110_2,
    cuspForm_11_2_a_a_old_110_5,
    cuspForm_11_2_a_a_old_110_10,
    cuspForm_55_eta_1p1_5p1_11p1_55p1_old_110_1,
    cuspForm_55_eta_1p1_5p1_11p1_55p1_old_110_2,
    cuspForm_110_eta_1p2_2m1_5m1_10p2_11m1_22p2_55p2_110m1,
    cuspForm_110_eta_1m1_2p2_10p1_11p1_55p2_110m1,
    cuspForm_110_eta_2p1_5m1_10p2_11p2_22m1_55p1,
    cuspForm_110_eta_1m1_2p2_5p1_11m1_22p2_55p1,
    cuspForm_110_eta_1p1_5m1_10p2_11p1_55m1_110p2,
    cuspForm_110_eta_1p1_2p1_55p1_110p1,
    cuspForm_110_eta_5p1_10p1_11p1_22p1,
    cuspForm_110_eta_1p1_2m1_5m1_10p3_11m1_22p3_55p1_110m1,
    cuspForm_110_eta_1p3_2m1_5m1_10p1_11m1_22p1_55p3_110m1]

end WeightTwoCusps
