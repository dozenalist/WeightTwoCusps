module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 70

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-1) η(2z) η(5z)^3 η(7z)^3 η(10z)^(-1) η(14z)^(-1) η(35z)^(-1) η(70z)`; see
[the local level table](../../TABLE.md#level-70).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 31 (zero-based) at level 210; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-210).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(5z)^3 η(7z)^3 η(10z)^(-1) η(14z)^(-1) η(35z)^(-1) η(70z)` at level 70. -/
abbrev cuspForm_70_eta_1m1_2p1_5p3_7p3_10m1_14m1_35m1_70p1 : gamma0CuspForms 70 :=
  etaQuotientCuspForm 70 sparse![70; 0 => -1, 1 => 1, 4 => 3, 6 => 3, 9 => -1, 13 => -1, 34 => -1, 69 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_70_eta_1m1_2p1_5p3_7p3_10m1_14m1_35m1_70p1_first_coeffs :
    first_coeffs 100 cuspForm_70_eta_1m1_2p1_5p3_7p3_10m1_14m1_35m1_70p1 =
    [0, 0, 1, 1, 1, 2, 2, 0, 1, -1, -3, -1, -4, -5, 1, -1, -5, 3, -3, -4,
     1, -3, -4, 6, -2, -2, 8, 1, 1, 3, 2, 0, 9, 3, 2, 2, 3, 0, 2, 7,
     5, 10, 2, 2, 2, -1, -8, -13, -10, 0, 3, -11, 6, -6, -8, -3, -7, -6, 6, -2,
     -8, 12, -4, 3, -9, -7, -4, 8, 0, -2, -3, 0, 9, -8, 2, 5, 10, 3, 4, 5,
     -1, -4, -18, -6, 4, 13, -16, 1, 8, -2, 1, -1, -12, 4, 16, 0, 22, 7, 1, -6] := by
  eta_coeff

end WeightTwoCusps
