module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«46».Old.«23_eta_1p2_23p2_old_46_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«46».Old.«23_eta_1p2_23p2_old_46_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«46».New.«46_eta_1m1_2p3_23m1_46p3»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«46».New.«46_eta_1p1_2p1_23p1_46p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«46».New.«46_eta_1p3_2m1_23p3_46m1»
public import WeightTwoCusps.Basis.Constructor

/-!
# An eta-quotient basis at level 46

Entries follow `Basis_cuspidal_eta_S2` in
[the local level table](../TABLE.md#level-46), in its original order.

0: `cuspForm_23_eta_1p2_23p2_old_46_1` is the dilation-1 lift
of `cuspForm_23_eta_1p2_23p2`.

1: `cuspForm_23_eta_1p2_23p2_old_46_2` is the dilation-2 lift
of `cuspForm_23_eta_1p2_23p2`.

2: `cuspForm_46_eta_1m1_2p3_23m1_46p3` is a directly defined eta basis vector.

3: `cuspForm_46_eta_1p1_2p1_23p1_46p1` is a directly defined eta basis vector.

4: `cuspForm_46_eta_1p3_2m1_23p3_46m1` is a directly defined eta basis vector.

Direct eta entries are not asserted to be normalized Hecke newforms or
members of the canonical newspace. The constructor certifies the full basis.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The complete cuspidal eta basis of `S₂(Γ₀(46))`, in report order. -/
@[eta_simps] def level_46_etaBasis : Module.Basis (Fin 5) ℂ (gamma0CuspForms 46) :=
  cuspFormBasis ![
    cuspForm_23_eta_1p2_23p2_old_46_1,
    cuspForm_23_eta_1p2_23p2_old_46_2,
    cuspForm_46_eta_1m1_2p3_23m1_46p3,
    cuspForm_46_eta_1p1_2p1_23p1_46p1,
    cuspForm_46_eta_1p3_2m1_23p3_46m1]

end WeightTwoCusps
