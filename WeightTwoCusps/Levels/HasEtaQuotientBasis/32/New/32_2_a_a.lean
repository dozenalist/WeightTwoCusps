module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# The level-32 newform 32.2.a.a

The eta product `η(4z)²η(8z)²` from the cuspidal basis in
`M2_Gamma0_Eta_Quotient_Bases_N_1_to_500`, with LMFDB label
https://www.lmfdb.org/ModularForm/GL2/Q/holomorphic/32/2/a/a/.
The displayed LMFDB eta expression and q-expansion agree through the
weight-two Sturm bound (8), and through degree 49.
-/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The normalized weight-two cusp form with LMFDB label `32.2.a.a`. -/
abbrev cuspForm_32_2_a_a : gamma0CuspForms 32 :=
  etaQuotientCuspForm 32 sparse![32; 3 => 2, 7 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_32_2_a_a_first_coeffs : first_coeffs 100 cuspForm_32_2_a_a =
    [0, 1, 0, 0, 0, -2, 0, 0, 0, -3, 0, 0, 0, 6, 0, 0, 0, 2, 0, 0,
     0, 0, 0, 0, 0, -1, 0, 0, 0, -10, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0,
     0, 10, 0, 0, 0, 6, 0, 0, 0, -7, 0, 0, 0, 14, 0, 0, 0, 0, 0, 0,
     0, -10, 0, 0, 0, -12, 0, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0,
     0, 9, 0, 0, 0, -4, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0] := by
  eta_coeff

end WeightTwoCusps

