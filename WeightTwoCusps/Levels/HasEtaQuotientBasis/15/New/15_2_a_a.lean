module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# The level-fifteen newform 15.2.a.a

The eta product `η(z)η(3z)η(5z)η(15z)` from the cuspidal basis in
`M2_Gamma0_Eta_Quotient_Bases_N_1_to_500`, with LMFDB label
https://www.lmfdb.org/ModularForm/GL2/Q/holomorphic/15/2/a/a/.
-/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The normalized weight-two cusp form with LMFDB label `15.2.a.a`. -/
abbrev cuspForm_15_2_a_a : gamma0CuspForms 15 :=
  etaQuotientCuspForm 15 sparse![15; 0 => 1, 2 => 1, 4 => 1, 14 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_15_2_a_a_first_coeffs : first_coeffs 100 cuspForm_15_2_a_a =
    [0, 1, -1, -1, -1, 1, 1, 0, 3, 1, -1, -4, 1, -2, 0, -1, -1, 2, -1, 4,
     -1, 0, 4, 0, -3, 1, 2, -1, 0, -2, 1, 0, -5, 4, -2, 0, -1, -10, -4, 2,
     3, 10, 0, 4, 4, 1, 0, 8, 1, -7, -1, -2, 2, -10, 1, -4, 0, -4, 2, -4,
     1, -2, 0, 0, 7, -2, -4, 12, -2, 0, 0, -8, 3, 10, 10, -1, -4, 0, -2, 0,
     -1, 1, -10, 12, 0, 2, -4, 2, -12, -6, -1, 0, 0, 0, -8, 4, 5, 2, 7, -4] := by
  eta_coeff

end WeightTwoCusps
