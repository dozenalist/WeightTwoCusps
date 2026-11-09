module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«88».Old.«11_2_a_a_old_88_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«88».Old.«11_2_a_a_old_88_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«88».Old.«11_2_a_a_old_88_4»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«88».Old.«11_2_a_a_old_88_8»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«88».New.«88_eta_1p1_4m1_8p2_11p1_22m2_44p5_88m2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«88».New.«88_eta_2p1_4p1_22p1_44p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«88».New.«88_eta_1m2_2p4_4p1_8m1_11p2_22m2_44p3_88m1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«88».New.«88_eta_1m2_2p5_4m2_8p1_11p2_22m1_88p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«88».New.«88_eta_1m2_2p5_4m1_11m2_22p5_44m1»
public import WeightTwoCusps.Basis.Constructor

/-!
# An eta-quotient basis at level 88

Entries follow `Basis_cuspidal_eta_S2` in
[the local level table](../TABLE.md#level-88), in its original order.

0: `cuspForm_11_2_a_a_old_88_1` is the dilation-1 lift
of `cuspForm_11_2_a_a`.

1: `cuspForm_11_2_a_a_old_88_2` is the dilation-2 lift
of `cuspForm_11_2_a_a`.

2: `cuspForm_11_2_a_a_old_88_4` is the dilation-4 lift
of `cuspForm_11_2_a_a`.

3: `cuspForm_11_2_a_a_old_88_8` is the dilation-8 lift
of `cuspForm_11_2_a_a`.

4: `cuspForm_88_eta_1p1_4m1_8p2_11p1_22m2_44p5_88m2` is a directly defined eta basis vector.

5: `cuspForm_88_eta_2p1_4p1_22p1_44p1` is a directly defined eta basis vector.

6: `cuspForm_88_eta_1m2_2p4_4p1_8m1_11p2_22m2_44p3_88m1` is a directly defined eta basis vector.

7: `cuspForm_88_eta_1m2_2p5_4m2_8p1_11p2_22m1_88p1` is a directly defined eta basis vector.

8: `cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1` is a directly defined eta basis vector.

Direct eta entries are not asserted to be normalized Hecke newforms or
members of the canonical newspace. The constructor certifies the full basis.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The complete cuspidal eta basis of `S₂(Γ₀(88))`, in report order. -/
@[eta_simps] def level_88_etaBasis : Module.Basis (Fin 9) ℂ (gamma0CuspForms 88) :=
  cuspFormBasis ![
    cuspForm_11_2_a_a_old_88_1,
    cuspForm_11_2_a_a_old_88_2,
    cuspForm_11_2_a_a_old_88_4,
    cuspForm_11_2_a_a_old_88_8,
    cuspForm_88_eta_1p1_4m1_8p2_11p1_22m2_44p5_88m2,
    cuspForm_88_eta_2p1_4p1_22p1_44p1,
    cuspForm_88_eta_1m2_2p4_4p1_8m1_11p2_22m2_44p3_88m1,
    cuspForm_88_eta_1m2_2p5_4m2_8p1_11p2_22m1_88p1,
    cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1]

end WeightTwoCusps
