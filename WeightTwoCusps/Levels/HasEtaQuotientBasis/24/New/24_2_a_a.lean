module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# The level-twenty-four newform 24.2.a.a

The eta product `η(2z)η(4z)η(6z)η(12z)` from the cuspidal basis in
`M2_Gamma0_Eta_Quotient_Bases_N_1_to_500`, with LMFDB label
https://www.lmfdb.org/ModularForm/GL2/Q/holomorphic/24/2/a/a/.
-/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The normalized weight-two cusp form with LMFDB label `24.2.a.a`. -/
abbrev cuspForm_24_2_a_a : gamma0CuspForms 24 :=
  etaQuotientCuspForm 24 sparse![24; 1 => 1, 3 => 1, 5 => 1, 11 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_24_2_a_a_first_coeffs : first_coeffs 100 cuspForm_24_2_a_a =
    [0, 1, 0, -1, 0, -2, 0, 0, 0, 1, 0, 4, 0, -2, 0, 2, 0, 2, 0, -4,
     0, 0, 0, -8, 0, -1, 0, -1, 0, 6, 0, 8, 0, -4, 0, 0, 0, 6, 0, 2,
     0, -6, 0, 4, 0, -2, 0, 0, 0, -7, 0, -2, 0, -2, 0, -8, 0, 4, 0, 4,
     0, -2, 0, 0, 0, 4, 0, -4, 0, 8, 0, 8, 0, 10, 0, 1, 0, 0, 0, -8,
     0, 1, 0, -4, 0, -4, 0, -6, 0, -6, 0, 0, 0, -8, 0, 8, 0, 2, 0, 4] := by
  eta_coeff

end WeightTwoCusps
