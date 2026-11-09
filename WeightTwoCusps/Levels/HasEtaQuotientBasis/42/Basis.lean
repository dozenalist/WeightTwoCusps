module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«42».Old.«14_2_a_a_old_42_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«42».Old.«14_2_a_a_old_42_3»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«42».New.«42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«42».New.«42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«42».New.«42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«42».New.«42_eta_1m1_2p2_3p1_7p2_14m1_42p1»
public import WeightTwoCusps.Basis.Constructor

/-!
# An eta-quotient basis at level 42

Entries follow `Basis_cuspidal_eta_S2` in
[the local level table](../TABLE.md#level-42), in its original order.

0: `cuspForm_14_2_a_a_old_42_1` is the dilation-1 lift
of `cuspForm_14_2_a_a`.

1: `cuspForm_14_2_a_a_old_42_3` is the dilation-3 lift
of `cuspForm_14_2_a_a`.

2: `cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1` is a directly defined eta basis vector.

3: `cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4` is a directly defined eta basis vector.

4: `cuspForm_42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1` is a directly defined eta basis vector.

Additional imported source forms for higher levels are not appended to
this table-ordered basis:
- `cuspForm_42_eta_1m1_2p2_3p1_7p2_14m1_42p1`

Direct eta entries are not asserted to be normalized Hecke newforms or
members of the canonical newspace. The constructor certifies the full basis.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The complete cuspidal eta basis of `S₂(Γ₀(42))`, in report order. -/
@[eta_simps] def level_42_etaBasis : Module.Basis (Fin 5) ℂ (gamma0CuspForms 42) :=
  cuspFormBasis ![
    cuspForm_14_2_a_a_old_42_1,
    cuspForm_14_2_a_a_old_42_3,
    cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1,
    cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4,
    cuspForm_42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1]

end WeightTwoCusps
