module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«104».New.«104_eta_1p1_4p2_8m1_13m1_26p2_104p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«104».New.«104_eta_1m1_2p1_4p3_8m1_13p1_26p1_52m1_104p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«104».New.«104_eta_1m1_2p2_8p1_13p1_52p2_104m1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«104».New.«104_eta_1m1_2p2_4p2_8m1_13p1_104p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«104».New.«104_eta_1m1_2p3_4m1_8p1_13p1_26m1_52p3_104m1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«104».New.«104_eta_1m1_2p3_4p1_8m1_13p1_26m1_52p1_104p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«104».New.«104_eta_1m1_2p4_4m2_8p1_13p1_26m2_52p4_104m1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«104».New.«104_eta_1p1_2m2_4p4_8m1_13m1_26p4_52m2_104p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«104».New.«104_eta_1p1_2m1_4p1_8p1_13m1_26p3_52p1_104m1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«104».New.«104_eta_1p1_2m1_4p3_8m1_13m1_26p3_52m1_104p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«104».New.«104_eta_1p1_8p1_13m1_26p2_52p2_104m1»
public import WeightTwoCusps.Basis.Constructor

/-!
# An eta-quotient basis at level 104

Entries follow `Basis_cuspidal_eta_S2` in
[the local level table](../TABLE.md#level-104), in its original order.

0: `cuspForm_104_eta_1p1_4p2_8m1_13m1_26p2_104p1` is a directly defined eta basis vector.

1: `cuspForm_104_eta_1m1_2p1_4p3_8m1_13p1_26p1_52m1_104p1` is a directly defined eta basis vector.

2: `cuspForm_104_eta_1m1_2p2_8p1_13p1_52p2_104m1` is a directly defined eta basis vector.

3: `cuspForm_104_eta_1m1_2p2_4p2_8m1_13p1_104p1` is a directly defined eta basis vector.

4: `cuspForm_104_eta_1m1_2p3_4m1_8p1_13p1_26m1_52p3_104m1` is a directly defined eta basis vector.

5: `cuspForm_104_eta_1m1_2p3_4p1_8m1_13p1_26m1_52p1_104p1` is a directly defined eta basis vector.

6: `cuspForm_104_eta_1m1_2p4_4m2_8p1_13p1_26m2_52p4_104m1` is a directly defined eta basis vector.

7: `cuspForm_104_eta_1p1_2m2_4p4_8m1_13m1_26p4_52m2_104p1` is a directly defined eta basis vector.

8: `cuspForm_104_eta_1p1_2m1_4p1_8p1_13m1_26p3_52p1_104m1` is a directly defined eta basis vector.

9: `cuspForm_104_eta_1p1_2m1_4p3_8m1_13m1_26p3_52m1_104p1` is a directly defined eta basis vector.

10: `cuspForm_104_eta_1p1_8p1_13m1_26p2_52p2_104m1` is a directly defined eta basis vector.

Direct eta entries are not asserted to be normalized Hecke newforms or
members of the canonical newspace. The constructor certifies the full basis.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The complete cuspidal eta basis of `S₂(Γ₀(104))`, in report order. -/
@[eta_simps] def level_104_etaBasis : Module.Basis (Fin 11) ℂ (gamma0CuspForms 104) :=
  cuspFormBasis ![
    cuspForm_104_eta_1p1_4p2_8m1_13m1_26p2_104p1,
    cuspForm_104_eta_1m1_2p1_4p3_8m1_13p1_26p1_52m1_104p1,
    cuspForm_104_eta_1m1_2p2_8p1_13p1_52p2_104m1,
    cuspForm_104_eta_1m1_2p2_4p2_8m1_13p1_104p1,
    cuspForm_104_eta_1m1_2p3_4m1_8p1_13p1_26m1_52p3_104m1,
    cuspForm_104_eta_1m1_2p3_4p1_8m1_13p1_26m1_52p1_104p1,
    cuspForm_104_eta_1m1_2p4_4m2_8p1_13p1_26m2_52p4_104m1,
    cuspForm_104_eta_1p1_2m2_4p4_8m1_13m1_26p4_52m2_104p1,
    cuspForm_104_eta_1p1_2m1_4p1_8p1_13m1_26p3_52p1_104m1,
    cuspForm_104_eta_1p1_2m1_4p3_8m1_13m1_26p3_52m1_104p1,
    cuspForm_104_eta_1p1_8p1_13m1_26p2_52p2_104m1]

end WeightTwoCusps
