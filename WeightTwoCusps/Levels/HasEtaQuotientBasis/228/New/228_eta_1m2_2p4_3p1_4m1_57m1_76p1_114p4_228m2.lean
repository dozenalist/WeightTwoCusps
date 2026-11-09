module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 228

The eta expression is `η(z)^(-2) η(2z)^4 η(3z) η(4z)^(-1) η(57z)^(-1) η(76z) η(114z)^4 η(228z)^(-2)`; see
[the local level table](../../TABLE.md#level-228).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z) η(4z)^(-1) η(57z)^(-1) η(76z) η(114z)^4 η(228z)^(-2)` at level 228. -/
abbrev cuspForm_228_eta_1m2_2p4_3p1_4m1_57m1_76p1_114p4_228m2 : gamma0CuspForms 228 :=
  etaQuotientCuspForm 228 sparse![228; 0 => -2, 1 => 4, 2 => 1, 3 => -1, 56 => -1, 75 => 1, 113 => 4, 227 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_228_eta_1m2_2p4_3p1_4m1_57m1_76p1_114p4_228m2_first_coeffs :
    first_coeffs 100 cuspForm_228_eta_1m2_2p4_3p1_4m1_57m1_76p1_114p4_228m2 =
    [0, 1, 2, 1, 1, 1, 1, 1, -1, 1, 0, 0, 2, -2, -1, -1, 1, 1, -2, 0,
     -1, -1, -1, 0, -1, -1, 0, 0, -1, -2, -1, 0, 1, -2, -1, -2, -1, 2, 0, -1,
     -1, -1, 0, -2, 0, 1, -1, 1, -2, 0, -1, 2, -1, -1, 2, -2, 0, 0, 3, 1,
     1, 2, 1, -1, 1, -1, 2, 2, -1, 3, -1, 1, 1, -1, -1, -2, -1, 0, -3, -1,
     1, -2, 0, 0, 0, -2, -1, 0, -2, 5, -2, -1, -2, -1, 6, 0, 1, 1, -1, -2] := by
  eta_coeff

end WeightTwoCusps
