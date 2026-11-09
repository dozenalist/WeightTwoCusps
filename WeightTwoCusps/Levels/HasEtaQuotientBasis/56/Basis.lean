module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«56».Old.«14_2_a_a_old_56_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«56».Old.«14_2_a_a_old_56_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«56».Old.«14_2_a_a_old_56_4»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«56».New.«56_eta_1p1_7p1_8p1_56p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«56».New.«56_eta_2m1_4p3_14p3_28m1»
public import WeightTwoCusps.Basis.Constructor

/-!
# An eta-quotient basis at level 56

Entries follow `Basis_cuspidal_eta_S2` in
[the local level table](../TABLE.md#level-56), in its original order.

0: `cuspForm_14_2_a_a_old_56_1` is the dilation-1 lift
of `cuspForm_14_2_a_a`.

1: `cuspForm_14_2_a_a_old_56_2` is the dilation-2 lift
of `cuspForm_14_2_a_a`.

2: `cuspForm_14_2_a_a_old_56_4` is the dilation-4 lift
of `cuspForm_14_2_a_a`.

3: `cuspForm_56_eta_1p1_7p1_8p1_56p1` is a directly defined eta basis vector.

4: `cuspForm_56_eta_2m1_4p3_14p3_28m1` is a directly defined eta basis vector.

Direct eta entries are not asserted to be normalized Hecke newforms or
members of the canonical newspace. The constructor certifies the full basis.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The complete cuspidal eta basis of `S₂(Γ₀(56))`, in report order. -/
@[eta_simps] def level_56_etaBasis : Module.Basis (Fin 5) ℂ (gamma0CuspForms 56) :=
  cuspFormBasis ![
    cuspForm_14_2_a_a_old_56_1,
    cuspForm_14_2_a_a_old_56_2,
    cuspForm_14_2_a_a_old_56_4,
    cuspForm_56_eta_1p1_7p1_8p1_56p1,
    cuspForm_56_eta_2m1_4p3_14p3_28m1]

end WeightTwoCusps
