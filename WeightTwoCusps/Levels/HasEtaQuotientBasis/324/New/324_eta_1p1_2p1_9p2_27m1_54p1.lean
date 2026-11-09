module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 324

The eta expression is `η(z) η(2z) η(9z)^2 η(27z)^(-1) η(54z)`; see
[the local level table](../../TABLE.md#level-324).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(2z) η(9z)^2 η(27z)^(-1) η(54z)` at level 324. -/
abbrev cuspForm_324_eta_1p1_2p1_9p2_27m1_54p1 : gamma0CuspForms 324 :=
  etaQuotientCuspForm 324 sparse![324; 0 => 1, 1 => 1, 8 => 2, 26 => -1, 53 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_324_eta_1p1_2p1_9p2_27m1_54p1_first_coeffs :
    first_coeffs 100 cuspForm_324_eta_1p1_2p1_9p2_27m1_54p1 =
    [0, 0, 1, -1, -2, 1, 0, 2, 1, 0, 0, -4, 3, 2, -4, 0, -2, -3, 0, 2,
     3, 1, 6, 4, 0, -6, -1, 0, -4, 5, -9, -6, 1, 0, 6, 8, 0, -4, -4, 4,
     0, -2, 0, 0, 0, 0, 12, -4, 3, 2, 4, 0, -4, -6, 0, -6, -4, -2, -12, -8,
     0, 14, -4, 0, -2, 11, 9, 8, 3, 0, 0, 0, 0, 14, -1, -4, 2, -8, 0, -10,
     3, 0, -18, -4, -3, -12, 8, 0, 6, -3, 0, 2, 0, -5, 12, 8, 0, -4, 9, 0] := by
  eta_coeff

end WeightTwoCusps
