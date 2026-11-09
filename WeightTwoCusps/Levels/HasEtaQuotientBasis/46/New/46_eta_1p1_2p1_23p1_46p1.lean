module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 46

The eta expression is `η(z) η(2z) η(23z) η(46z)`; see
[the local level table](../../TABLE.md#level-46).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(2z) η(23z) η(46z)` at level 46. -/
abbrev cuspForm_46_eta_1p1_2p1_23p1_46p1 : gamma0CuspForms 46 :=
  etaQuotientCuspForm 46 sparse![46; 0 => 1, 1 => 1, 22 => 1, 45 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_46_eta_1p1_2p1_23p1_46p1_first_coeffs :
    first_coeffs 100 cuspForm_46_eta_1p1_2p1_23p1_46p1 =
    [0, 0, 0, 1, -1, -2, 1, 0, 2, 1, 0, 0, -2, 1, -2, -2, 0, 2, -1, 0,
     2, 0, 2, 0, 1, 0, -1, -1, 2, -1, 0, -3, -3, -2, 0, 4, -1, 2, 0, 3,
     -2, 1, 2, -2, 0, 0, 0, 1, -1, -4, 4, 4, -2, -2, -1, 0, 0, -2, 1, -4,
     6, 6, -3, -4, 2, -2, -4, 0, -4, 1, -4, 1, 3, 3, 0, 3, 2, 4, 3, 6,
     0, -4, 3, -6, 2, -4, 2, -3, -4, 2, -4, -4, -1, -3, 1, 4, -2, -2, 0, 2] := by
  eta_coeff

end WeightTwoCusps
