module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-3) η(18z)^(-1) η(28z) η(36z) η(42z)^(-1) η(84z)^2 η(126z) η(252z)^(-1)`; see
[the local level table](../../TABLE.md#level-252).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-3) η(18z)^(-1) η(28z) η(36z) η(42z)^(-1) η(84z)^2 η(126z) η(252z)^(-1)` at level 252. -/
abbrev cuspForm_252_eta_1m3_2p7_3p1_4m3_18m1_28p1_36p1_42m1_84p2_126p1_252m1 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -3, 1 => 7, 2 => 1, 3 => -3, 17 => -1, 27 => 1, 35 => 1, 41 => -1, 83 => 2, 125 => 1, 251 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m3_2p7_3p1_4m3_18m1_28p1_36p1_42m1_84p2_126p1_252m1_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m3_2p7_3p1_4m3_18m1_28p1_36p1_42m1_84p2_126p1_252m1 =
    [0, 0, 1, 3, 2, 0, 2, 3, 1, -3, -1, 6, 0, -3, 0, 0, 1, -6, 1, 6,
     -2, 0, 0, 3, -1, -6, 2, 6, 0, -3, -3, -3, -1, -9, -4, 0, -1, 0, -2, 3,
     -1, -6, -1, 9, -1, 0, 2, 0, 2, -12, 0, 3, -1, 3, -1, 0, 0, -9, 2, 6,
     -1, 9, -2, 0, -4, -3, 2, -6, 2, 3, 1, 0, -2, -6, -3, -3, 1, 0, -1, 0,
     0, 0, -4, 0, -1, 6, -1, 0, -3, -12, -1, 3, 2, 6, 6, -9, 3, 0, 1, -3] := by
  eta_coeff

end WeightTwoCusps
