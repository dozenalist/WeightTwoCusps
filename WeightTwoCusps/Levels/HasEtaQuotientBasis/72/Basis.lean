module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«72».Old.«24_2_a_a_old_72_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«72».Old.«24_2_a_a_old_72_3»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«72».Old.«36_2_a_a_old_72_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«72».Old.«36_2_a_a_old_72_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«72».New.«72_eta_1m3_2p7_3p1_4m2_6m1_12p2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«72».New.«72_eta_1m1_3p3_4p1_12p1»
public import WeightTwoCusps.Basis.Constructor

/-!
# An eta-quotient basis at level 72

Entries follow `Basis_cuspidal_eta_S2` in
[the local level table](../TABLE.md#level-72), in its original order.

0: `cuspForm_24_2_a_a_old_72_1` is the dilation-1 lift
of `cuspForm_24_2_a_a`.

1: `cuspForm_24_2_a_a_old_72_3` is the dilation-3 lift
of `cuspForm_24_2_a_a`.

2: `cuspForm_36_2_a_a_old_72_1` is the dilation-1 lift
of `cuspForm_36_2_a_a`.

3: `cuspForm_36_2_a_a_old_72_2` is the dilation-2 lift
of `cuspForm_36_2_a_a`.

4: `cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2` is a directly defined eta basis vector.

Additional imported source forms for higher levels are not appended to
this table-ordered basis:
- `cuspForm_72_eta_1m1_3p3_4p1_12p1`

Direct eta entries are not asserted to be normalized Hecke newforms or
members of the canonical newspace. The constructor certifies the full basis.
The coefficient columns are `1, 2, 3, 5, 7`.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The complete cuspidal eta basis of `S₂(Γ₀(72))`, in report order. -/
@[eta_simps] def level_72_etaBasis : Module.Basis (Fin 5) ℂ (gamma0CuspForms 72) :=
  cuspFormBasis ![
    cuspForm_24_2_a_a_old_72_1,
    cuspForm_24_2_a_a_old_72_3,
    cuspForm_36_2_a_a_old_72_1,
    cuspForm_36_2_a_a_old_72_2,
    cuspForm_72_eta_1m3_2p7_3p1_4m2_6m1_12p2] (c := ![1, 2, 3, 5, 7])

end WeightTwoCusps
