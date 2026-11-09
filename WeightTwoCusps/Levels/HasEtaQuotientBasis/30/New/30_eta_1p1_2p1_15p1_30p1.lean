module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A level-30 cuspidal eta basis vector

The eta product `η(z)η(2z)η(15z)η(30z)` is from `Basis_cuspidal_eta_S2` in
`M2_Gamma0_Eta_Quotient_Bases_N_1_to_500`; see
[the local level table](../../TABLE.md#level-30).

This eta product starts at degree two. Together with the two lifts of
`15.2.a.a`, it gives the report's basis, complementing the oldspace.
It is not a normalized Hecke newform; the newspace has dimension one.

The new/old dimensions are also recorded at
https://www.lmfdb.org/ModularForm/GL2/Q/holomorphic/30/2/a/.
-/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta product `η(z)η(2z)η(15z)η(30z)` at level 30. -/
abbrev cuspForm_30_eta_1p1_2p1_15p1_30p1 : gamma0CuspForms 30 :=
  etaQuotientCuspForm 30 sparse![30; 0 => 1, 1 => 1, 14 => 1, 29 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_30_eta_1p1_2p1_15p1_30p1_first_coeffs : first_coeffs 100 cuspForm_30_eta_1p1_2p1_15p1_30p1 =
    [0, 0, 1, -1, -2, 1, 0, 2, 1, 0, 0, -2, 1, -2, -2, 0, 2, -2, 1, 4,
     -1, 2, -2, 0, 0, 0, 0, -1, 2, 2, -1, -4, -3, 2, 4, -2, -2, -6, 0, 0,
     0, 8, -2, 4, 6, 1, 0, 4, -3, -8, 1, -4, 2, -2, 0, -2, -2, 0, -4, -2,
     2, 4, 4, 2, -2, 0, 2, 8, -6, 0, 2, -4, 1, 4, -4, -1, -4, 0, 2, -4,
     3, 0, 2, 0, 2, 4, 0, 4, -2, -12, 0, 4, 0, -4, 4, 0, 4, 0, 1, -2] := by
  eta_coeff

end WeightTwoCusps

