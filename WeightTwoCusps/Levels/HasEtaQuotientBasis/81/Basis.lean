module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«81».Old.«27_2_a_a_old_81_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«81».Old.«27_2_a_a_old_81_3»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«81».New.«81_eta_3m1_9p6_27m1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«81».New.«81_eta_3p1_9p2_27p1»
public import WeightTwoCusps.Basis.Constructor

/-!
# An eta-quotient basis at level 81

Entries follow `Basis_cuspidal_eta_S2` in
[the local level table](../TABLE.md#level-81), in its original order.

0: `cuspForm_27_2_a_a_old_81_1` is the dilation-1 lift
of `cuspForm_27_2_a_a`.

1: `cuspForm_27_2_a_a_old_81_3` is the dilation-3 lift
of `cuspForm_27_2_a_a`.

2: `cuspForm_81_eta_3m1_9p6_27m1` is a directly defined eta basis vector.

3: `cuspForm_81_eta_3p1_9p2_27p1` is a directly defined eta basis vector.

Direct eta entries are not asserted to be normalized Hecke newforms or
members of the canonical newspace. The constructor certifies the full basis.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The complete cuspidal eta basis of `S₂(Γ₀(81))`, in report order. -/
@[eta_simps] def level_81_etaBasis : Module.Basis (Fin 4) ℂ (gamma0CuspForms 81) :=
  cuspFormBasis ![
    cuspForm_27_2_a_a_old_81_1,
    cuspForm_27_2_a_a_old_81_3,
    cuspForm_81_eta_3m1_9p6_27m1,
    cuspForm_81_eta_3p1_9p2_27p1]

end WeightTwoCusps
