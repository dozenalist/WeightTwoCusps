module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 42

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-1) η(2z)^2 η(3z) η(7z)^2 η(14z)^(-1) η(42z)`; see
[the local level table](../../TABLE.md#level-42).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 59 (zero-based) at level 462; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-462).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(3z) η(7z)^2 η(14z)^(-1) η(42z)` at level 42. -/
abbrev cuspForm_42_eta_1m1_2p2_3p1_7p2_14m1_42p1 : gamma0CuspForms 42 :=
  etaQuotientCuspForm 42 sparse![42; 0 => -1, 1 => 2, 2 => 1, 6 => 2, 13 => -1, 41 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_42_eta_1m1_2p2_3p1_7p2_14m1_42p1_first_coeffs :
    first_coeffs 100 cuspForm_42_eta_1m1_2p2_3p1_7p2_14m1_42p1 =
    [0, 0, 1, 1, 0, 0, -1, 0, -1, -3, -2, -2, 1, 2, -1, 1, 2, 2, 4, -2,
     0, 2, 2, 2, -3, 0, 0, 1, 0, 0, -1, 0, 1, 0, -4, 0, -3, -4, 2, -7,
     2, -2, -2, 0, -2, 0, 2, 0, 3, 0, -1, 10, 2, 0, -1, 4, 1, 3, -2, -2,
     1, 2, 0, -3, -4, -4, 4, 0, 2, -2, 2, 2, 2, 4, 2, -7, -2, 2, 3, 4,
     -4, 6, 0, 2, 2, -4, -4, -8, -6, 2, -2, -2, 2, -6, 0, 4, -1, -8, 1, -2] := by
  eta_coeff

end WeightTwoCusps
