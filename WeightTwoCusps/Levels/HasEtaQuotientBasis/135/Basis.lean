module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«135».Old.«15_2_a_a_old_135_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«135».Old.«15_2_a_a_old_135_3»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«135».Old.«15_2_a_a_old_135_9»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«135».Old.«27_2_a_a_old_135_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«135».Old.«27_2_a_a_old_135_5»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«135».New.«135_eta_1p1_5p1_27p1_135p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«135».New.«135_eta_3p2_45p2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«135».New.«135_eta_9p2_15p2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«135».New.«135_eta_1m1_3p2_5p2_9p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«135».New.«135_eta_1m1_3p3_5p2_15m1_45p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«135».New.«135_eta_3m1_9p3_15p3_45m1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«135».New.«135_eta_15p1_27p2_45p2_135m1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«135».New.«135_eta_9p3_15p1_27m1_45m1_135p2»
public import WeightTwoCusps.Basis.Constructor

/-!
# An eta-quotient basis at level 135

Entries follow `Basis_cuspidal_eta_S2` in
[the local level table](../TABLE.md#level-135), in its original order.

0: `cuspForm_15_2_a_a_old_135_1` is the dilation-1 lift
of `cuspForm_15_2_a_a`.

1: `cuspForm_15_2_a_a_old_135_3` is the dilation-3 lift
of `cuspForm_15_2_a_a`.

2: `cuspForm_15_2_a_a_old_135_9` is the dilation-9 lift
of `cuspForm_15_2_a_a`.

3: `cuspForm_27_2_a_a_old_135_1` is the dilation-1 lift
of `cuspForm_27_2_a_a`.

4: `cuspForm_27_2_a_a_old_135_5` is the dilation-5 lift
of `cuspForm_27_2_a_a`.

5: `cuspForm_135_eta_1p1_5p1_27p1_135p1` is a directly defined eta basis vector.

6: `cuspForm_135_eta_3p2_45p2` is a directly defined eta basis vector.

7: `cuspForm_135_eta_9p2_15p2` is a directly defined eta basis vector.

8: `cuspForm_135_eta_1m1_3p2_5p2_9p1` is a directly defined eta basis vector.

9: `cuspForm_135_eta_1m1_3p3_5p2_15m1_45p1` is a directly defined eta basis vector.

10: `cuspForm_135_eta_3m1_9p3_15p3_45m1` is a directly defined eta basis vector.

11: `cuspForm_135_eta_15p1_27p2_45p2_135m1` is a directly defined eta basis vector.

12: `cuspForm_135_eta_9p3_15p1_27m1_45m1_135p2` is a directly defined eta basis vector.

Direct eta entries are not asserted to be normalized Hecke newforms or
members of the canonical newspace. The constructor certifies the full basis.
The coefficient columns are `1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 17`.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The complete cuspidal eta basis of `S₂(Γ₀(135))`, in report order. -/
@[eta_simps] def level_135_etaBasis : Module.Basis (Fin 13) ℂ (gamma0CuspForms 135) :=
  cuspFormBasis ![
    cuspForm_15_2_a_a_old_135_1,
    cuspForm_15_2_a_a_old_135_3,
    cuspForm_15_2_a_a_old_135_9,
    cuspForm_27_2_a_a_old_135_1,
    cuspForm_27_2_a_a_old_135_5,
    cuspForm_135_eta_1p1_5p1_27p1_135p1,
    cuspForm_135_eta_3p2_45p2,
    cuspForm_135_eta_9p2_15p2,
    cuspForm_135_eta_1m1_3p2_5p2_9p1,
    cuspForm_135_eta_1m1_3p3_5p2_15m1_45p1,
    cuspForm_135_eta_3m1_9p3_15p3_45m1,
    cuspForm_135_eta_15p1_27p2_45p2_135m1,
    cuspForm_135_eta_9p3_15p1_27m1_45m1_135p2] (c := ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 17])

end WeightTwoCusps
