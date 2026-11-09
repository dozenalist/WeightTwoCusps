module

public import Dimension.Gamma_0.Basic
public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# The level-eleven newform 11.2.a.a

The eta product `η(z)²η(11z)²` from
https://www.lmfdb.org/ModularForm/GL2/Q/holomorphic/11/2/a/a/.
-/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane


/-- The normalized weight-two cusp form with LMFDB label `11.2.a.a`. -/
abbrev cuspForm_11_2_a_a : gamma0CuspForms 11 :=
  etaQuotientCuspForm 11 sparse![11; 0 => 2, 10 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_11_2_a_a_first_coeffs : first_coeffs 100 cuspForm_11_2_a_a =
    [0, 1, -2, -1, 2, 1, 2, -2, 0, -2, -2, 1, -2, 4, 4, -1, -4, -2, 4, 0,
     2, 2, -2, -1, 0, -4, -8, 5, -4, 0, 2, 7, 8, -1, 4, -2, -4, 3, 0, -4,
     0, -8, -4, -6, 2, -2, 2, 8, 4, -3, 8, 2, 8, -6, -10, 1, 0, 0, 0, 5,
     -2, 12, -14, 4, -8, 4, 2, -7, -4, 1, 4, -3, 0, 4, -6, 4, 0, -2, 8, -10,
     -4, 1, 16, -6, 4, -2, 12, 0, 0, 15, 4, -8, -2, -7, -16, 0, -8, -7, 6, -2] := by
  eta_coeff

end WeightTwoCusps
