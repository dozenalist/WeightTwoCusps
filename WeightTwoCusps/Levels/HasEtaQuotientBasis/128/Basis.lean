module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«128».Old.«32_2_a_a_old_128_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«128».Old.«32_2_a_a_old_128_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«128».Old.«32_2_a_a_old_128_4»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«128».Old.«64_eta_1m2_2p5_4m2_8p3_old_128_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«128».Old.«64_eta_1m2_2p5_4m2_8p3_old_128_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«128».New.«128_eta_2m2_4p5_8m1_16p1_32m1_64p2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«128».New.«128_eta_2p2_4p1_16p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«128».New.«128_eta_4p2_32p2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«128».New.«128_eta_8p1_32p1_64p2»
public import WeightTwoCusps.Basis.Constructor

/-!
# An eta-quotient basis at level 128

Entries follow `Basis_cuspidal_eta_S2` in
[the local level table](../TABLE.md#level-128), in its original order.

0: `cuspForm_32_2_a_a_old_128_1` is the dilation-1 lift
of `cuspForm_32_2_a_a`.

1: `cuspForm_32_2_a_a_old_128_2` is the dilation-2 lift
of `cuspForm_32_2_a_a`.

2: `cuspForm_32_2_a_a_old_128_4` is the dilation-4 lift
of `cuspForm_32_2_a_a`.

3: `cuspForm_64_eta_1m2_2p5_4m2_8p3_old_128_1` is the dilation-1 lift
of `cuspForm_64_eta_1m2_2p5_4m2_8p3`.

4: `cuspForm_64_eta_1m2_2p5_4m2_8p3_old_128_2` is the dilation-2 lift
of `cuspForm_64_eta_1m2_2p5_4m2_8p3`.

5: `cuspForm_128_eta_2m2_4p5_8m1_16p1_32m1_64p2` is a directly defined eta basis vector.

6: `cuspForm_128_eta_2p2_4p1_16p1` is a directly defined eta basis vector.

7: `cuspForm_128_eta_4p2_32p2` is a directly defined eta basis vector.

8: `cuspForm_128_eta_8p1_32p1_64p2` is a directly defined eta basis vector.

Direct eta entries are not asserted to be normalized Hecke newforms or
members of the canonical newspace. The constructor certifies the full basis.
The coefficient columns are `1, 2, 3, 4, 5, 7, 9, 10, 13`.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The complete cuspidal eta basis of `S₂(Γ₀(128))`, in report order. -/
@[eta_simps] def level_128_etaBasis : Module.Basis (Fin 9) ℂ (gamma0CuspForms 128) :=
  cuspFormBasis ![
    cuspForm_32_2_a_a_old_128_1,
    cuspForm_32_2_a_a_old_128_2,
    cuspForm_32_2_a_a_old_128_4,
    cuspForm_64_eta_1m2_2p5_4m2_8p3_old_128_1,
    cuspForm_64_eta_1m2_2p5_4m2_8p3_old_128_2,
    cuspForm_128_eta_2m2_4p5_8m1_16p1_32m1_64p2,
    cuspForm_128_eta_2p2_4p1_16p1,
    cuspForm_128_eta_4p2_32p2,
    cuspForm_128_eta_8p1_32p1_64p2] (c := ![1, 2, 3, 4, 5, 7, 9, 10, 13])

end WeightTwoCusps
