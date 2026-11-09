module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-2) η(2z) η(3z)^4 η(5z)^4 η(6z)^(-1) η(10z)^(-2) η(15z)^(-2) η(30z) η(90z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^4 η(5z)^4 η(6z)^(-1) η(10z)^(-2) η(15z)^(-2) η(30z) η(90z)` at level 270. -/
abbrev cuspForm_270_eta_1m2_2p1_3p4_5p4_6m1_10m2_15m2_30p1_90p1 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -2, 1 => 1, 2 => 4, 4 => 4, 5 => -1, 9 => -2, 14 => -2, 29 => 1, 89 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m2_2p1_3p4_5p4_6m1_10m2_15m2_30p1_90p1_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m2_2p1_3p4_5p4_6m1_10m2_15m2_30p1_90p1 =
    [0, 0, 0, 0, 1, 2, 4, 4, 6, 4, 3, -2, 0, -2, -2, -4, -1, -2, -8, -4,
     0, 4, -4, 4, 0, -4, -14, 0, 0, -2, -4, 2, -10, -16, -7, 0, 4, 0, 14, -4,
     -2, -6, 8, -2, 4, 0, -5, -2, -8, 10, 8, 20, 6, 6, 4, 2, -12, 8, 12, 0,
     -4, 6, 2, -8, 6, 10, 12, -12, 22, 0, 4, -2, 8, 0, -6, 0, 1, -2, -16, 0,
     8, 4, 2, 6, 4, -4, -8, 16, -4, 0, -4, 4, -14, -8, 8, -10, 4, 2, 10, -8] := by
  eta_coeff

end WeightTwoCusps
