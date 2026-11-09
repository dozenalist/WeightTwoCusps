module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A level-35 cuspidal eta basis vector

The eta product `η(z)²η(35z)²` is from `Basis_cuspidal_eta_S2` in
`M2_Gamma0_Eta_Quotient_Bases_N_1_to_500`; see
[the local level table](../../TABLE.md#level-35).

This is the first vector of the report's level-35 cuspidal basis and
starts at degree three. All three dimensions are new: every proper
divisor of 35 has zero-dimensional cusp space. This eta basis vector
is not a normalized Hecke newform.

The eta computation's companion source is
https://users.wfu.edu/rouseja/eta/.
-/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta product `η(z)²η(35z)²` at level 35. -/
abbrev cuspForm_35_eta_1p2_35p2 : gamma0CuspForms 35 :=
  etaQuotientCuspForm 35 sparse![35; 0 => 2, 34 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_35_eta_1p2_35p2_first_coeffs : first_coeffs 100 cuspForm_35_eta_1p2_35p2 =
    [0, 0, 0, 1, -2, -1, 2, 1, 2, -2, 0, -2, -2, 1, 0, 0, 2, 3, -2, 2,
     0, 0, -2, -2, 0, 0, -2, -1, 0, 2, 2, -2, 2, 1, 2, 0, 2, -2, -4, 6,
     2, -6, -2, -8, 4, 0, 4, 5, -4, 0, 0, -2, -6, 6, -2, 1, -2, 4, 6, 2,
     0, 4, 0, 0, -6, -4, 2, -2, -2, -8, 0, -4, 2, 2, 0, 1, 4, -1, 6, 2,
     -2, 4, 4, 4, 0, 0, -4, -5, 0, -8, -2, 4, 4, -2, -6, 0, 0, 3, 0, 0] := by
  eta_coeff

end WeightTwoCusps

