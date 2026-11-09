module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-3) η(2z)^4 η(3z)^4 η(5z) η(6z)^(-2) η(9z) η(10z)^(-1) η(15z)^(-1) η(30z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^4 η(3z)^4 η(5z) η(6z)^(-2) η(9z) η(10z)^(-1) η(15z)^(-1) η(30z)` at level 270. -/
abbrev cuspForm_270_eta_1m3_2p4_3p4_5p1_6m2_9p1_10m1_15m1_30p1 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -3, 1 => 4, 2 => 4, 4 => 1, 5 => -2, 8 => 1, 9 => -1, 14 => -1, 29 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m3_2p4_3p4_5p1_6m2_9p1_10m1_15m1_30p1_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m3_2p4_3p4_5p1_6m2_9p1_10m1_15m1_30p1 =
    [0, 1, 3, 5, 6, 5, 5, 4, 4, 5, 2, 0, -5, -4, -3, -5, 1, 0, 0, -3,
     -5, -5, -12, -5, 0, -6, -10, -10, -6, -10, 0, 5, -8, -15, -15, -5, -15, 2, 9, -5,
     -8, -5, 5, -10, 5, 10, 1, 0, 5, 9, 5, 15, 26, 5, 5, 1, -4, 10, 14, 20,
     0, 13, -2, 10, 1, 15, 5, -6, 20, 0, 13, 5, 20, -2, 3, 5, 12, -5, -15, 3,
     15, 5, 16, 15, -5, -5, -1, 30, -22, 0, -5, 4, -20, 10, 24, -20, 15, 4, 2, -30] := by
  eta_coeff

end WeightTwoCusps
