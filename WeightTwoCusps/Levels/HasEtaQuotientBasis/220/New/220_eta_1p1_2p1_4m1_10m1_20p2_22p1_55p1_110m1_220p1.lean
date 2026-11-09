module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 220

The eta expression is `η(z) η(2z) η(4z)^(-1) η(10z)^(-1) η(20z)^2 η(22z) η(55z) η(110z)^(-1) η(220z)`; see
[the local level table](../../TABLE.md#level-220).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(2z) η(4z)^(-1) η(10z)^(-1) η(20z)^2 η(22z) η(55z) η(110z)^(-1) η(220z)` at level 220. -/
abbrev cuspForm_220_eta_1p1_2p1_4m1_10m1_20p2_22p1_55p1_110m1_220p1 : gamma0CuspForms 220 :=
  etaQuotientCuspForm 220 sparse![220; 0 => 1, 1 => 1, 3 => -1, 9 => -1, 19 => 2, 21 => 1, 54 => 1, 109 => -1, 219 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_220_eta_1p1_2p1_4m1_10m1_20p2_22p1_55p1_110m1_220p1_first_coeffs :
    first_coeffs 100 cuspForm_220_eta_1p1_2p1_4m1_10m1_20p2_22p1_55p1_110m1_220p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -2, 1, 1, 1, -1, 1, 2, -2, -1,
     -1, -1, 0, 0, 1, 2, 0, -1, 0, 1, 0, -2, 1, 4, -3, -2, 0, 0, 0, -2,
     3, 2, 0, -1, 0, 0, 1, -3, 0, 1, -1, -1, -1, 0, 0, 2, 1, 1, -2, 1,
     0, -1, 2, 1, 1, 5, 0, -2, -6, -4, 2, 0, -1, 1, 2, 1, 3, -4, 2, -2,
     -4, 4, -4, -1, -3, -2, 4, 1, 0, 5, 3, 4, -1, -2, 4, -3, -1, 0, 1, -2] := by
  eta_coeff

end WeightTwoCusps
