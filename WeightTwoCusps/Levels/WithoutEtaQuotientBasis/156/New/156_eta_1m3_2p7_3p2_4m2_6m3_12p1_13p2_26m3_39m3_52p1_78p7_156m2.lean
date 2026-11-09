module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 156

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-3) η(2z)^7 η(3z)^2 η(4z)^(-2) η(6z)^(-3) η(12z) η(13z)^2 η(26z)^(-3) η(39z)^(-3) η(52z) η(78z)^7 η(156z)^(-2)`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-156).
The table has full eta basis = NO at this level: these supporting forms
do not span the whole cusp-form space.

It is needed by table vector 8 (zero-based) at level 468; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-468).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z)^2 η(4z)^(-2) η(6z)^(-3) η(12z) η(13z)^2 η(26z)^(-3) η(39z)^(-3) η(52z) η(78z)^7 η(156z)^(-2)` at level 156. -/
abbrev cuspForm_156_eta_1m3_2p7_3p2_4m2_6m3_12p1_13p2_26m3_39m3_52p1_78p7_156m2 : gamma0CuspForms 156 :=
  etaQuotientCuspForm 156 sparse![156; 0 => -3, 1 => 7, 2 => 2, 3 => -2, 5 => -3, 11 => 1, 12 => 2, 25 => -3, 38 => -3, 51 => 1, 77 => 7, 155 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_156_eta_1m3_2p7_3p2_4m2_6m3_12p1_13p2_26m3_39m3_52p1_78p7_156m2_first_coeffs :
    first_coeffs 100 cuspForm_156_eta_1m3_2p7_3p2_4m2_6m3_12p1_13p2_26m3_39m3_52p1_78p7_156m2 =
    [0, 0, 0, 0, 0, 1, 3, 2, -1, -2, -2, 1, 2, 0, -2, -7, -2, 2, -2, -4,
     -7, 0, 2, 4, 4, -4, -1, 2, 14, 6, -2, 6, 2, 7, 0, 2, -2, -8, 4, 2,
     -2, -11, 2, 0, -11, -1, -2, 3, -6, 0, 4, -8, -2, 2, 3, -12, 0, 10, 0, -1,
     -3, 8, -2, 4, 8, 1, 0, 2, 14, -8, -8, -5, -3, 2, -2, 6, -12, -6, 0, 4,
     13, -2, 10, 5, 0, 12, 2, -2, -2, -1, 0, 2, -4, -12, -10, -14, -3, 2, -6, 5] := by
  eta_coeff

end WeightTwoCusps
