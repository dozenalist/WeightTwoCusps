module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 200

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(5z)^2 η(10z)^(-1) η(20z) η(100z)`; see
[the local level table](../../TABLE.md#level-200).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 39 (zero-based) at level 400; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-400).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(5z)^2 η(10z)^(-1) η(20z) η(100z)` at level 200. -/
abbrev cuspForm_200_eta_1m2_2p5_4m2_5p2_10m1_20p1_100p1 : gamma0CuspForms 200 :=
  etaQuotientCuspForm 200 sparse![200; 0 => -2, 1 => 5, 3 => -2, 4 => 2, 9 => -1, 19 => 1, 99 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_200_eta_1m2_2p5_4m2_5p2_10m1_20p1_100p1_first_coeffs :
    first_coeffs 100 cuspForm_200_eta_1m2_2p5_4m2_5p2_10m1_20p1_100p1 =
    [0, 0, 0, 0, 0, 1, 2, 0, 0, 2, -2, -4, 0, 0, -2, 0, 0, 0, 0, -4,
     0, 2, 0, 0, 0, 1, -2, 0, 0, 2, 4, 4, 0, 0, 6, -4, 0, 0, 0, 4,
     0, 4, 0, 0, 0, -3, -6, 0, 0, -6, 2, 0, 0, 0, -4, 4, 0, 0, 0, -4,
     0, -4, 0, 0, 0, -2, 0, 0, 0, -2, -4, 4, 0, 0, -2, 0, 0, 0, 0, 8,
     0, -10, 0, 0, 0, 2, 10, 0, 0, 6, -2, 0, 0, 0, 6, 4, 0, 0, 0, 4] := by
  eta_coeff

end WeightTwoCusps
