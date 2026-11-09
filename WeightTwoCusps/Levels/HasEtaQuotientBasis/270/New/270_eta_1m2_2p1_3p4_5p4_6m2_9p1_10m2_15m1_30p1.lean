module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-2) η(2z) η(3z)^4 η(5z)^4 η(6z)^(-2) η(9z) η(10z)^(-2) η(15z)^(-1) η(30z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^4 η(5z)^4 η(6z)^(-2) η(9z) η(10z)^(-2) η(15z)^(-1) η(30z)` at level 270. -/
abbrev cuspForm_270_eta_1m2_2p1_3p4_5p4_6m2_9p1_10m2_15m1_30p1 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -2, 1 => 1, 2 => 4, 4 => 4, 5 => -2, 8 => 1, 9 => -2, 14 => -1, 29 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m2_2p1_3p4_5p4_6m2_9p1_10m2_15m1_30p1_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m2_2p1_3p4_5p4_6m2_9p1_10m2_15m1_30p1 =
    [0, 1, 2, 4, 4, 6, 4, 4, 0, 4, 1, 2, -4, 0, -6, -4, -3, 8, 0, -3,
     -8, -4, -12, -6, 0, 1, -10, -8, -2, -2, 0, 1, -8, -12, -15, -8, -12, 2, 2, -4,
     -7, 10, 4, -6, 4, 8, -3, -4, 4, 13, 2, 12, 18, 2, 4, -2, 0, 8, 18, 8,
     0, 9, 0, 8, 3, 20, 4, -14, 16, 0, 14, -2, 16, 6, 10, 4, 6, -6, -12, -5,
     16, 4, 12, -6, -4, -5, 8, 24, -10, 12, -4, -4, -12, 8, 24, -34, 12, 8, 4, -24] := by
  eta_coeff

end WeightTwoCusps
