module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A level-35 cuspidal eta basis vector

The eta product `η(5z)²η(7z)²` is from `Basis_cuspidal_eta_S2` in
`M2_Gamma0_Eta_Quotient_Bases_N_1_to_500`; see
[the local level table](../../TABLE.md#level-35).

This is the third vector of the report's level-35 cuspidal basis and
starts at degree one. All three dimensions are new: every proper
divisor of 35 has zero-dimensional cusp space. Its descriptive name
records the eta product without asserting a Hecke eigenform identification.

The eta computation's companion source is
https://users.wfu.edu/rouseja/eta/.
-/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta product `η(5z)²η(7z)²` at level 35. -/
abbrev cuspForm_35_eta_5p2_7p2 : gamma0CuspForms 35 :=
  etaQuotientCuspForm 35 sparse![35; 4 => 2, 6 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_35_eta_5p2_7p2_first_coeffs : first_coeffs 100 cuspForm_35_eta_5p2_7p2 =
    [0, 1, 0, 0, 0, 0, -2, 0, -2, 0, 0, -1, 0, 4, 0, -1, 2, 0, 2, 0,
     2, 1, 2, -4, 0, 1, 2, -4, -2, 1, -2, -2, -2, -4, -2, -1, 2, 4, 4, -1,
     -2, -6, 2, -2, 2, 2, -4, 4, 8, 1, 0, 5, -4, 6, 2, 2, 2, -2, -6, -2,
     2, 4, 0, -2, -2, -1, -2, -2, -4, 2, 0, 4, -2, 0, 0, 0, -8, -2, -6, -3,
     -2, -3, -4, 8, -2, -3, 4, 8, 0, -4, 2, 1, 8, -2, 6, -2, 0, -4, 0, 6] := by
  eta_coeff

end WeightTwoCusps

