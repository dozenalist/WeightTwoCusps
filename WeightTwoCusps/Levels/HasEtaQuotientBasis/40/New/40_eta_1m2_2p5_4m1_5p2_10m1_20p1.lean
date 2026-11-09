module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A level-40 cuspidal eta basis vector

The eta product `η(2z)⁵η(5z)²η(20z) / (η(z)²η(4z)η(10z))` is from `Basis_cuspidal_eta_S2` in
`M2_Gamma0_Eta_Quotient_Bases_N_1_to_500`; see
[the local level table](../../TABLE.md#level-40).

Together with the two lifts of `20.2.a.a`, this is the report's
level-40 cuspidal basis, complementing the oldspace. The newspace has
dimension one. This eta quotient has coefficient 2 at degree two and
is not the normalized level-40 Hecke newform.

The new/old dimensions are also recorded at
https://www.lmfdb.org/ModularForm/GL2/Q/holomorphic/40/2/a/.
-/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)⁵η(5z)²η(20z) / (η(z)²η(4z)η(10z))` at level 40. -/
abbrev cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1 : gamma0CuspForms 40 :=
  etaQuotientCuspForm 40 sparse![40; 0 => -2, 1 => 5, 3 => -1, 4 => 2, 9 => -1, 19 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_first_coeffs : first_coeffs 100 cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1 =
    [0, 1, 2, 0, 0, 1, -4, -4, 0, -3, -2, 4, 0, -2, 4, 0, 0, 2, 2, 4,
     0, 0, 0, 4, 0, 1, 4, 0, 0, -2, 4, -8, 0, 0, -12, -4, 0, 6, -8, 0,
     0, -6, -8, -8, 0, -3, 12, 4, 0, 9, 2, 0, 0, 6, 8, 4, 0, 0, 12, -4,
     0, -2, -8, 12, 0, -2, 0, 8, 0, 0, -4, 0, 0, -6, 4, 0, 0, -16, -8, 0,
     0, 9, 12, -16, 0, 2, -20, 0, 0, -6, -2, 8, 0, 0, -12, 4, 0, -14, -6, -12] := by
  eta_coeff

end WeightTwoCusps

