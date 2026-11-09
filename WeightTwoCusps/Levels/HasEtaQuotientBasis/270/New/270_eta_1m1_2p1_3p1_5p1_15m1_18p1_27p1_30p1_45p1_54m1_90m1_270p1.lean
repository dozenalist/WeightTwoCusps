module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-1) η(2z) η(3z) η(5z) η(15z)^(-1) η(18z) η(27z) η(30z) η(45z) η(54z)^(-1) η(90z)^(-1) η(270z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z) η(5z) η(15z)^(-1) η(18z) η(27z) η(30z) η(45z) η(54z)^(-1) η(90z)^(-1) η(270z)` at level 270. -/
abbrev cuspForm_270_eta_1m1_2p1_3p1_5p1_15m1_18p1_27p1_30p1_45p1_54m1_90m1_270p1 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -1, 1 => 1, 2 => 1, 4 => 1, 14 => -1, 17 => 1, 26 => 1, 29 => 1, 44 => 1, 53 => -1, 89 => -1, 269 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m1_2p1_3p1_5p1_15m1_18p1_27p1_30p1_45p1_54m1_90m1_270p1_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m1_2p1_3p1_5p1_15m1_18p1_27p1_30p1_45p1_54m1_90m1_270p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1,
     0, 1, 0, 0, 1, 1, 2, 1, 1, 0, -1, -1, 1, 0, 1, -1, 0, -2, -1, -1,
     1, 0, -2, 1, -3, -1, -4, 0, -2, 0, -3, -3, -2, -3, -2, -1, 1, -1, -1, -2,
     0, -4, 0, -2, -2, -3, 1, -3, -3, 0, -1, 2, -3, 1, -2, 0, -2, 2, 2, -2,
     0, 0, 1, -3, 1, 1, 0, 0, 2, 2, 2, 2, 2, -2, 1, 1, -2, 1, -2, 2] := by
  eta_coeff

end WeightTwoCusps
