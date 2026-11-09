module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A level-33 cuspidal eta basis vector

The eta product `η(z)η(3z)η(11z)η(33z)` is from `Basis_cuspidal_eta_S2` in
`M2_Gamma0_Eta_Quotient_Bases_N_1_to_500`; see
[the local level table](../../TABLE.md#level-33).

This eta product starts at degree two. Together with the two lifts of
`11.2.a.a`, it gives the report's basis, complementing the oldspace.
It is not a normalized Hecke newform; the newspace has dimension one.

The new/old dimensions are also recorded at
https://www.lmfdb.org/ModularForm/GL2/Q/holomorphic/33/2/a/.
-/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta product `η(z)η(3z)η(11z)η(33z)` at level 33. -/
abbrev cuspForm_33_eta_1p1_3p1_11p1_33p1 : gamma0CuspForms 33 :=
  etaQuotientCuspForm 33 sparse![33; 0 => 1, 2 => 1, 10 => 1, 32 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_33_eta_1p1_3p1_11p1_33p1_first_coeffs : first_coeffs 100 cuspForm_33_eta_1p1_3p1_11p1_33p1 =
    [0, 0, 1, -1, -1, -1, 1, 2, -1, 2, 0, 0, -1, -2, 0, 0, 1, 0, -3, 0,
     0, 0, 1, 3, 1, 1, 2, 0, 0, -2, 2, -5, -1, -1, -2, -2, 3, 1, 0, -2,
     2, 2, -4, 2, -1, 1, 2, 0, 3, 4, -3, 2, -2, 4, -1, -1, -4, 0, -2, -3,
     -2, -2, 2, -2, 5, 0, 1, 1, 2, -2, -4, 1, -1, -6, 4, 3, 0, 2, 6, 2,
     2, -5, -6, 6, 4, 2, -4, 2, -1, -7, -4, 0, -2, -2, 8, 0, -7, 3, 1, 2] := by
  eta_coeff

end WeightTwoCusps

