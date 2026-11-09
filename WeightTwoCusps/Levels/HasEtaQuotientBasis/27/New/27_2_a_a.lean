module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# The level-twenty-seven newform 27.2.a.a

The eta product `η(3z)²η(9z)²` from the cuspidal basis in
`M2_Gamma0_Eta_Quotient_Bases_N_1_to_500`, with LMFDB label
https://www.lmfdb.org/ModularForm/GL2/Q/holomorphic/27/2/a/a/.
-/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The normalized weight-two cusp form with LMFDB label `27.2.a.a`. -/
abbrev cuspForm_27_2_a_a : gamma0CuspForms 27 :=
  etaQuotientCuspForm 27 sparse![27; 2 => 2, 8 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_27_2_a_a_first_coeffs : first_coeffs 100 cuspForm_27_2_a_a =
    [0, 1, 0, 0, -2, 0, 0, -1, 0, 0, 0, 0, 0, 5, 0, 0, 4, 0, 0, -7,
     0, 0, 0, 0, 0, -5, 0, 0, 2, 0, 0, -4, 0, 0, 0, 0, 0, 11, 0, 0,
     0, 0, 0, 8, 0, 0, 0, 0, 0, -6, 0, 0, -10, 0, 0, 0, 0, 0, 0, 0,
     0, -1, 0, 0, -8, 0, 0, 5, 0, 0, 0, 0, 0, -7, 0, 0, 14, 0, 0, 17,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -5, 0, 0, 0, 0, 0, -19, 0, 0] := by
  eta_coeff

end WeightTwoCusps
