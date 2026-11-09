module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# The level-fourteen newform 14.2.a.a

The eta product `η(z)η(2z)η(7z)η(14z)` from
https://www.lmfdb.org/ModularForm/GL2/Q/holomorphic/14/2/a/a/.
-/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The normalized weight-two cusp form with LMFDB label `14.2.a.a`. -/
abbrev cuspForm_14_2_a_a : CuspForm (CongruenceSubgroup.Gamma0 14) 2 :=
  etaQuotientCuspForm 14 sparse![14; 0 => 1, 1 => 1, 6 => 1, 13 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_14_2_a_a_first_coeffs : first_coeffs 100 cuspForm_14_2_a_a =
    [0, 1, -1, -2, 1, 0, 2, 1, -1, 1, 0, 0, -2, -4, -1, 0, 1, 6, -1, 2,
     0, -2, 0, 0, 2, -5, 4, 4, 1, -6, 0, -4, -1, 0, -6, 0, 1, 2, -2, 8,
     0, 6, 2, 8, 0, 0, 0, -12, -2, 1, 5, -12, -4, 6, -4, 0, -1, -4, 6, -6,
     0, 8, 4, 1, 1, 0, 0, -4, 6, 0, 0, 0, -1, 2, -2, 10, 2, 0, -8, 8,
     0, -11, -6, -6, -2, 0, -8, 12, 0, -6, 0, -4, 0, 8, 12, 0, 2, -10, -1, 0] := by
  eta_coeff

end WeightTwoCusps
