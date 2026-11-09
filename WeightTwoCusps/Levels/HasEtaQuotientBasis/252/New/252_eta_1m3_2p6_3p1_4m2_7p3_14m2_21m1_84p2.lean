module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-3) η(2z)^6 η(3z) η(4z)^(-2) η(7z)^3 η(14z)^(-2) η(21z)^(-1) η(84z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z) η(4z)^(-2) η(7z)^3 η(14z)^(-2) η(21z)^(-1) η(84z)^2` at level 252. -/
abbrev cuspForm_252_eta_1m3_2p6_3p1_4m2_7p3_14m2_21m1_84p2 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -3, 1 => 6, 2 => 1, 3 => -2, 6 => 3, 13 => -2, 20 => -1, 83 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m3_2p6_3p1_4m2_7p3_14m2_21m1_84p2_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m3_2p6_3p1_4m2_7p3_14m2_21m1_84p2 =
    [0, 0, 0, 0, 0, 0, 1, 3, 3, 3, 5, 6, 7, 3, -1, 3, 2, 0, -3, -6,
     4, 3, -3, 0, -5, 3, 6, -6, -2, -6, -3, 3, -8, -6, -4, 0, 6, 0, -4, -3,
     -1, 0, -2, -6, -13, 0, 2, -12, -3, -9, 2, 6, -5, 6, 7, 0, -4, -3, -1, 0,
     -13, -9, 2, 3, -3, 6, -4, 6, 20, -12, 4, -6, -9, 6, -8, -6, 9, 0, 9, 3,
     -6, 6, -10, 0, -6, -6, -6, 6, 0, -12, 2, 6, 5, 6, -12, -6, 17, -6, 0, -12] := by
  eta_coeff

end WeightTwoCusps
