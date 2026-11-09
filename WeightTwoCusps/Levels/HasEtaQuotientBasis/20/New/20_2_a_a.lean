module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# The level-twenty newform 20.2.a.a

The eta product `η(2z)²η(10z)²` from the cuspidal basis in
`M2_Gamma0_Eta_Quotient_Bases_N_1_to_500`, with LMFDB label
https://www.lmfdb.org/ModularForm/GL2/Q/holomorphic/20/2/a/a/.
-/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The normalized weight-two cusp form with LMFDB label `20.2.a.a`. -/
abbrev cuspForm_20_2_a_a : gamma0CuspForms 20 :=
  etaQuotientCuspForm 20 sparse![20; 1 => 2, 9 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_20_2_a_a_first_coeffs : first_coeffs 100 cuspForm_20_2_a_a =
    [0, 1, 0, -2, 0, -1, 0, 2, 0, 1, 0, 0, 0, 2, 0, 2, 0, -6, 0, -4,
     0, -4, 0, 6, 0, 1, 0, 4, 0, 6, 0, -4, 0, 0, 0, -2, 0, 2, 0, -4,
     0, 6, 0, -10, 0, -1, 0, -6, 0, -3, 0, 12, 0, -6, 0, 0, 0, 8, 0, 12,
     0, 2, 0, 2, 0, -2, 0, 2, 0, -12, 0, -12, 0, 2, 0, -2, 0, 0, 0, 8,
     0, -11, 0, 6, 0, 6, 0, -12, 0, -6, 0, 4, 0, 8, 0, 4, 0, 2, 0, 0] := by
  eta_coeff

end WeightTwoCusps
