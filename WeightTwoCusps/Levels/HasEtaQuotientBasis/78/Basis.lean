module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«78».New.«78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«78».New.«78_eta_1p3_2m2_3m2_6p3_13m2_26p3_39p3_78m2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«78».New.«78_eta_1p1_2p1_39p1_78p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«78».New.«78_eta_1p1_6p1_26p1_39p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«78».New.«78_eta_2p1_3p1_13p1_78p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«78».New.«78_eta_3p1_6p1_13p1_26p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«78».New.«78_eta_1m1_2p1_3p2_13p2_39m1_78p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«78».New.«78_eta_1m1_2p2_6p1_13p2_26m1_39p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«78».New.«78_eta_1m1_2p2_3p2_6m1_13p2_26m1_39m1_78p2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«78».New.«78_eta_2p1_3m1_6p2_13p1_39p2_78m1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«78».New.«78_eta_1p1_2m1_6p2_26p2_39p1_78m1»
public import WeightTwoCusps.Basis.Constructor

/-!
# An eta-quotient basis at level 78

Entries follow `Basis_cuspidal_eta_S2` in
[the local level table](../TABLE.md#level-78), in its original order.

0: `cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3` is a directly defined eta basis vector.

1: `cuspForm_78_eta_1p3_2m2_3m2_6p3_13m2_26p3_39p3_78m2` is a directly defined eta basis vector.

2: `cuspForm_78_eta_1p1_2p1_39p1_78p1` is a directly defined eta basis vector.

3: `cuspForm_78_eta_1p1_6p1_26p1_39p1` is a directly defined eta basis vector.

4: `cuspForm_78_eta_2p1_3p1_13p1_78p1` is a directly defined eta basis vector.

5: `cuspForm_78_eta_3p1_6p1_13p1_26p1` is a directly defined eta basis vector.

6: `cuspForm_78_eta_1m1_2p1_3p2_13p2_39m1_78p1` is a directly defined eta basis vector.

7: `cuspForm_78_eta_1m1_2p2_6p1_13p2_26m1_39p1` is a directly defined eta basis vector.

8: `cuspForm_78_eta_1m1_2p2_3p2_6m1_13p2_26m1_39m1_78p2` is a directly defined eta basis vector.

9: `cuspForm_78_eta_2p1_3m1_6p2_13p1_39p2_78m1` is a directly defined eta basis vector.

10: `cuspForm_78_eta_1p1_2m1_6p2_26p2_39p1_78m1` is a directly defined eta basis vector.

Direct eta entries are not asserted to be normalized Hecke newforms or
members of the canonical newspace. The constructor certifies the full basis.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The complete cuspidal eta basis of `S₂(Γ₀(78))`, in report order. -/
@[eta_simps] def level_78_etaBasis : Module.Basis (Fin 11) ℂ (gamma0CuspForms 78) :=
  cuspFormBasis ![
    cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3,
    cuspForm_78_eta_1p3_2m2_3m2_6p3_13m2_26p3_39p3_78m2,
    cuspForm_78_eta_1p1_2p1_39p1_78p1,
    cuspForm_78_eta_1p1_6p1_26p1_39p1,
    cuspForm_78_eta_2p1_3p1_13p1_78p1,
    cuspForm_78_eta_3p1_6p1_13p1_26p1,
    cuspForm_78_eta_1m1_2p1_3p2_13p2_39m1_78p1,
    cuspForm_78_eta_1m1_2p2_6p1_13p2_26m1_39p1,
    cuspForm_78_eta_1m1_2p2_3p2_6m1_13p2_26m1_39m1_78p2,
    cuspForm_78_eta_2p1_3m1_6p2_13p1_39p2_78m1,
    cuspForm_78_eta_1p1_2m1_6p2_26p2_39p1_78m1]

end WeightTwoCusps
