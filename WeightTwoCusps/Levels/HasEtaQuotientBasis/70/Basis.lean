module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«70».Old.«14_2_a_a_old_70_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«70».Old.«14_2_a_a_old_70_5»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«70».Old.«35_eta_1p2_35p2_old_70_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«70».Old.«35_eta_1p1_5p1_7p1_35p1_old_70_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«70».Old.«35_eta_5p2_7p2_old_70_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«70».Old.«35_eta_1p2_35p2_old_70_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«70».Old.«35_eta_1p1_5p1_7p1_35p1_old_70_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«70».Old.«35_eta_5p2_7p2_old_70_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«70».New.«70_eta_1p1_5p2_10m1_14p1_35m1_70p2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«70».New.«70_eta_1m1_2p1_5p3_7p3_10m1_14m1_35m1_70p1»
public import WeightTwoCusps.Basis.Constructor

/-!
# An eta-quotient basis at level 70

Entries follow `Basis_cuspidal_eta_S2` in
[the local level table](../TABLE.md#level-70), in its original order.

0: `cuspForm_14_2_a_a_old_70_1` is the dilation-1 lift
of `cuspForm_14_2_a_a`.

1: `cuspForm_14_2_a_a_old_70_5` is the dilation-5 lift
of `cuspForm_14_2_a_a`.

2: `cuspForm_35_eta_1p2_35p2_old_70_1` is the dilation-1 lift
of `cuspForm_35_eta_1p2_35p2`.

3: `cuspForm_35_eta_1p1_5p1_7p1_35p1_old_70_1` is the dilation-1 lift
of `cuspForm_35_eta_1p1_5p1_7p1_35p1`.

4: `cuspForm_35_eta_5p2_7p2_old_70_1` is the dilation-1 lift
of `cuspForm_35_eta_5p2_7p2`.

5: `cuspForm_35_eta_1p2_35p2_old_70_2` is the dilation-2 lift
of `cuspForm_35_eta_1p2_35p2`.

6: `cuspForm_35_eta_1p1_5p1_7p1_35p1_old_70_2` is the dilation-2 lift
of `cuspForm_35_eta_1p1_5p1_7p1_35p1`.

7: `cuspForm_35_eta_5p2_7p2_old_70_2` is the dilation-2 lift
of `cuspForm_35_eta_5p2_7p2`.

8: `cuspForm_70_eta_1p1_5p2_10m1_14p1_35m1_70p2` is a directly defined eta basis vector.

Additional imported source forms for higher levels are not appended to
this table-ordered basis:
- `cuspForm_70_eta_1m1_2p1_5p3_7p3_10m1_14m1_35m1_70p1`

Direct eta entries are not asserted to be normalized Hecke newforms or
members of the canonical newspace. The constructor certifies the full basis.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The complete cuspidal eta basis of `S₂(Γ₀(70))`, in report order. -/
@[eta_simps] def level_70_etaBasis : Module.Basis (Fin 9) ℂ (gamma0CuspForms 70) :=
  cuspFormBasis ![
    cuspForm_14_2_a_a_old_70_1,
    cuspForm_14_2_a_a_old_70_5,
    cuspForm_35_eta_1p2_35p2_old_70_1,
    cuspForm_35_eta_1p1_5p1_7p1_35p1_old_70_1,
    cuspForm_35_eta_5p2_7p2_old_70_1,
    cuspForm_35_eta_1p2_35p2_old_70_2,
    cuspForm_35_eta_1p1_5p1_7p1_35p1_old_70_2,
    cuspForm_35_eta_5p2_7p2_old_70_2,
    cuspForm_70_eta_1p1_5p2_10m1_14p1_35m1_70p2]

end WeightTwoCusps
