module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 200

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(2z)^(-2) η(4z)^5 η(8z)^(-2) η(10z) η(20z)^(-1) η(40z)^2 η(50z)`; see
[the local level table](../../TABLE.md#level-200).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 38 (zero-based) at level 400; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-400).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-2) η(4z)^5 η(8z)^(-2) η(10z) η(20z)^(-1) η(40z)^2 η(50z)` at level 200. -/
abbrev cuspForm_200_eta_2m2_4p5_8m2_10p1_20m1_40p2_50p1 : gamma0CuspForms 200 :=
  etaQuotientCuspForm 200 sparse![200; 1 => -2, 3 => 5, 7 => -2, 9 => 1, 19 => -1, 39 => 2, 49 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_200_eta_2m2_4p5_8m2_10p1_20m1_40p2_50p1_first_coeffs :
    first_coeffs 100 cuspForm_200_eta_2m2_4p5_8m2_10p1_20m1_40p2_50p1 =
    [0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 2, 0, -1, 0, -2, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, -1, 0, 0, 0, 0,
     0, 0, 0, -2, 0, -1, 0, -4, 0, 0, 0, 0, 0, -4, 0, 2, 0, 0, 0, 0,
     0, 0, 0, -2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 4, 0, 1, 0, 2, 0, 0,
     0, 0, 0, 6, 0, -2, 0, -2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 8, 0, 0] := by
  eta_coeff

end WeightTwoCusps
