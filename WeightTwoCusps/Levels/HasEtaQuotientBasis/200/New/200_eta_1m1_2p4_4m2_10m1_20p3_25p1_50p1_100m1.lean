module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 200

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-1) η(2z)^4 η(4z)^(-2) η(10z)^(-1) η(20z)^3 η(25z) η(50z) η(100z)^(-1)`; see
[the local level table](../../TABLE.md#level-200).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 35 (zero-based) at level 400; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-400).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^4 η(4z)^(-2) η(10z)^(-1) η(20z)^3 η(25z) η(50z) η(100z)^(-1)` at level 200. -/
abbrev cuspForm_200_eta_1m1_2p4_4m2_10m1_20p3_25p1_50p1_100m1 : gamma0CuspForms 200 :=
  etaQuotientCuspForm 200 sparse![200; 0 => -1, 1 => 4, 3 => -2, 9 => -1, 19 => 3, 24 => 1, 49 => 1, 99 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_200_eta_1m1_2p4_4m2_10m1_20p3_25p1_50p1_100m1_first_coeffs :
    first_coeffs 100 cuspForm_200_eta_1m1_2p4_4m2_10m1_20p3_25p1_50p1_100m1 =
    [0, 1, 1, -2, -1, 1, -1, -1, -1, 2, 2, -1, 1, -1, 0, 0, -1, 2, 0, -1,
     0, 0, -1, 1, 1, 1, 2, -1, 2, -2, -4, 2, -1, 3, -1, -4, 2, -3, -1, 0,
     0, -1, -2, 3, 3, -3, 0, 5, 1, -1, -2, -5, -4, 5, 3, 4, 2, 3, 4, -4,
     0, -2, -2, 5, -1, -2, 1, -6, -3, 0, 4, 0, 2, -4, 0, 0, -5, 2, -4, 10,
     0, -1, 3, -8, -2, 2, -2, 6, 3, -1, 2, 8, 6, -10, -6, 4, 1, -15, -3, -2] := by
  eta_coeff

end WeightTwoCusps
