module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# The level-36 newform 36.2.a.a

The eta product `η(6z)⁴` from the cuspidal basis in
`M2_Gamma0_Eta_Quotient_Bases_N_1_to_500`, with LMFDB label
https://www.lmfdb.org/ModularForm/GL2/Q/holomorphic/36/2/a/a/.
The displayed LMFDB eta expression and q-expansion agree through the
weight-two Sturm bound (12), and through degree 49.
-/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The normalized weight-two cusp form with LMFDB label `36.2.a.a`. -/
abbrev cuspForm_36_2_a_a : gamma0CuspForms 36 :=
  etaQuotientCuspForm 36 sparse![36; 5 => 4]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_36_2_a_a_first_coeffs : first_coeffs 100 cuspForm_36_2_a_a =
    [0, 1, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 8,
     0, 0, 0, 0, 0, -5, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, -10, 0, 0,
     0, 0, 0, 8, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 14, 0, 0, 0, 0, 0, -16, 0, 0, 0, 0, 0, -10, 0, 0, 0, 0, 0, -4,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8, 0, 0, 0, 0, 0, 14, 0, 0] := by
  eta_coeff

end WeightTwoCusps

