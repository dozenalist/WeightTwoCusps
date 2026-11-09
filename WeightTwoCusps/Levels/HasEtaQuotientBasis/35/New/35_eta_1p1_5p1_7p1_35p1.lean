module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A level-35 cuspidal eta basis vector

The eta product `η(z)η(5z)η(7z)η(35z)` is from `Basis_cuspidal_eta_S2` in
`M2_Gamma0_Eta_Quotient_Bases_N_1_to_500`; see
[the local level table](../../TABLE.md#level-35).

This is the second vector of the report's level-35 cuspidal basis and
starts at degree two. All three dimensions are new: every proper
divisor of 35 has zero-dimensional cusp space. This eta basis vector
is not a normalized Hecke newform.

The eta computation's companion source is
https://users.wfu.edu/rouseja/eta/.
-/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta product `η(z)η(5z)η(7z)η(35z)` at level 35. -/
abbrev cuspForm_35_eta_1p1_5p1_7p1_35p1 : gamma0CuspForms 35 :=
  etaQuotientCuspForm 35 sparse![35; 0 => 1, 4 => 1, 6 => 1, 34 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_35_eta_1p1_5p1_7p1_35p1_first_coeffs : first_coeffs 100 cuspForm_35_eta_1p1_5p1_7p1_35p1 =
    [0, 0, 1, -1, -1, 0, 0, 0, 1, 1, 1, 1, -2, 1, -1, -1, -3, -1, 1, 2,
     -1, 1, 0, -2, 4, 0, 2, 1, 1, -3, 0, 0, 1, -1, -2, 0, 1, 0, -4, -3,
     1, -2, 0, 2, 2, 1, 0, 3, 0, 0, 1, 3, 0, 2, -4, 1, -1, 2, 2, 0,
     -2, -6, 0, -1, 1, 1, -4, -4, 0, 2, -1, 0, -3, 4, 6, -1, 8, -1, -4, -1,
     -3, 0, 2, 0, 2, -1, 4, 1, -4, 2, 1, -1, -4, 0, -4, 2, 4, -5, 1, 2] := by
  eta_coeff

end WeightTwoCusps

