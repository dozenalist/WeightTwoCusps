module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 200

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(2z)^(-2) η(4z)^4 η(8z)^(-1) η(10z)^3 η(20z)^(-1) η(50z)^(-1) η(100z) η(200z)`; see
[the local level table](../../TABLE.md#level-200).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 37 (zero-based) at level 400; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-400).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-2) η(4z)^4 η(8z)^(-1) η(10z)^3 η(20z)^(-1) η(50z)^(-1) η(100z) η(200z)` at level 200. -/
abbrev cuspForm_200_eta_2m2_4p4_8m1_10p3_20m1_50m1_100p1_200p1 : gamma0CuspForms 200 :=
  etaQuotientCuspForm 200 sparse![200; 1 => -2, 3 => 4, 7 => -1, 9 => 3, 19 => -1, 49 => -1, 99 => 1, 199 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_200_eta_2m2_4p4_8m1_10p3_20m1_50m1_100p1_200p1_first_coeffs :
    first_coeffs 100 cuspForm_200_eta_2m2_4p4_8m1_10p3_20m1_50m1_100p1_200p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 1, 0, 2, 0, 3,
     0, -1, 0, -2, 0, 1, 0, -2, 0, -3, 0, 2, 0, -2, 0, -3, 0, 0, 0, -4,
     0, -3, 0, 0, 0, -2, 0, -2, 0, 1, 0, -5, 0, 0, 0, 2, 0, -4, 0, 2,
     0, 4, 0, 4, 0, -2, 0, 6, 0, 5, 0, 0, 0, 0, 0, -1, 0, -2, 0, -6,
     0, 7, 0, -2, 0, 4, 0, 6, 0, 0, 0, -2, 0, -6, 0, 4, 0, 0, 0, 2] := by
  eta_coeff

end WeightTwoCusps
