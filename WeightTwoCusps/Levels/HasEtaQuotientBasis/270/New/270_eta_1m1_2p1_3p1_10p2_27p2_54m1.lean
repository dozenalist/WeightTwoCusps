module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-1) η(2z) η(3z) η(10z)^2 η(27z)^2 η(54z)^(-1)`; see
[the local level table](../../TABLE.md#level-270).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z) η(10z)^2 η(27z)^2 η(54z)^(-1)` at level 270. -/
abbrev cuspForm_270_eta_1m1_2p1_3p1_10p2_27p2_54m1 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -1, 1 => 1, 2 => 1, 9 => 2, 26 => 2, 53 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m1_2p1_3p1_10p2_27p2_54m1_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m1_2p1_3p1_10p2_27p2_54m1 =
    [0, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2,
     2, 0, 1, 2, 2, 1, -1, 1, -1, -2, -1, 0, -1, -4, 0, -4, -2, -5, -1, -2,
     -2, -1, -4, -2, -7, -1, -4, -5, -1, -3, -5, -4, -1, 3, -4, -3, 1, -2, -4, -1,
     -2, -4, 0, -6, -1, -4, 0, 0, -5, 0, -3, 0, -3, 0, 3, 1, 0, -1, 0, -4,
     -1, 2, -1, -5, 0, 0, -2, 4, -1, -3, 4, 2, 0, 0, 0, 5, -6, 6, 2, -2] := by
  eta_coeff

end WeightTwoCusps
