module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-2) η(2z)^4 η(3z) η(5z) η(6z)^(-2) η(9z) η(10z)^(-2) η(15z)^(-1) η(30z)^4`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z) η(5z) η(6z)^(-2) η(9z) η(10z)^(-2) η(15z)^(-1) η(30z)^4` at level 270. -/
abbrev cuspForm_270_eta_1m2_2p4_3p1_5p1_6m2_9p1_10m2_15m1_30p4 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -2, 1 => 4, 2 => 1, 4 => 1, 5 => -2, 8 => 1, 9 => -2, 14 => -1, 29 => 4]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m2_2p4_3p1_5p1_6m2_9p1_10m2_15m1_30p4_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m2_2p4_3p1_5p1_6m2_9p1_10m2_15m1_30p4 =
    [0, 0, 0, 0, 1, 2, 1, 1, 0, -2, 0, 1, 0, -2, -2, -1, -1, 4, 4, -1,
     -3, -2, -1, -2, 3, 2, -5, 0, 3, 1, 2, 2, -4, -10, -4, -3, -2, 0, 2, 2,
     -2, 6, 2, -2, 1, 0, -2, -2, 4, 1, 2, 8, 0, 0, -2, -4, 0, -4, 6, 0,
     -1, 3, 2, 4, 3, 7, -6, 0, 4, 0, 4, -2, -4, -3, 0, 0, -2, -2, -4, 3,
     5, -2, 2, -6, -2, -1, 1, 10, -1, 6, 2, 4, -2, 4, 2, -13, 1, -1, 4, 4] := by
  eta_coeff

end WeightTwoCusps
