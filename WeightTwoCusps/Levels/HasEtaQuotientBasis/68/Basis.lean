module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«68».New.«68_eta_1p2_2m1_4p1_17m2_34p5_68m1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«68».New.«68_eta_1p1_2m1_4p2_17m1_34p5_68m2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«68».New.«68_eta_1p1_2p2_4m1_17m1_34p2_68p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«68».New.«68_eta_2p2_34p2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«68».New.«68_eta_1m1_2p2_4p1_17p1_34p2_68m1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«68».New.«68_eta_1m1_2p5_4m2_17p1_34m1_68p2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«68».New.«68_eta_1m2_2p5_4m1_17p2_34m1_68p1»
public import WeightTwoCusps.Basis.Constructor

/-!
# An eta-quotient basis at level 68

Entries follow `Basis_cuspidal_eta_S2` in
[the local level table](../TABLE.md#level-68), in its original order.

0: `cuspForm_68_eta_1p2_2m1_4p1_17m2_34p5_68m1` is a directly defined eta basis vector.

1: `cuspForm_68_eta_1p1_2m1_4p2_17m1_34p5_68m2` is a directly defined eta basis vector.

2: `cuspForm_68_eta_1p1_2p2_4m1_17m1_34p2_68p1` is a directly defined eta basis vector.

3: `cuspForm_68_eta_2p2_34p2` is a directly defined eta basis vector.

4: `cuspForm_68_eta_1m1_2p2_4p1_17p1_34p2_68m1` is a directly defined eta basis vector.

5: `cuspForm_68_eta_1m1_2p5_4m2_17p1_34m1_68p2` is a directly defined eta basis vector.

6: `cuspForm_68_eta_1m2_2p5_4m1_17p2_34m1_68p1` is a directly defined eta basis vector.

Direct eta entries are not asserted to be normalized Hecke newforms or
members of the canonical newspace. The constructor certifies the full basis.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The complete cuspidal eta basis of `S₂(Γ₀(68))`, in report order. -/
@[eta_simps] def level_68_etaBasis : Module.Basis (Fin 7) ℂ (gamma0CuspForms 68) :=
  cuspFormBasis ![
    cuspForm_68_eta_1p2_2m1_4p1_17m2_34p5_68m1,
    cuspForm_68_eta_1p1_2m1_4p2_17m1_34p5_68m2,
    cuspForm_68_eta_1p1_2p2_4m1_17m1_34p2_68p1,
    cuspForm_68_eta_2p2_34p2,
    cuspForm_68_eta_1m1_2p2_4p1_17p1_34p2_68m1,
    cuspForm_68_eta_1m1_2p5_4m2_17p1_34m1_68p2,
    cuspForm_68_eta_1m2_2p5_4m1_17p2_34m1_68p1]

end WeightTwoCusps
