module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 80

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-1) η(2z)^2 η(4z)^(-1) η(5z) η(8z)^3 η(16z)^(-1) η(20z) η(40z)^(-1) η(80z)`; see
[the local level table](../../TABLE.md#level-80).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 27 (zero-based) at level 400; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-400).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(4z)^(-1) η(5z) η(8z)^3 η(16z)^(-1) η(20z) η(40z)^(-1) η(80z)` at level 80. -/
abbrev cuspForm_80_eta_1m1_2p2_4m1_5p1_8p3_16m1_20p1_40m1_80p1 : gamma0CuspForms 80 :=
  etaQuotientCuspForm 80 sparse![80; 0 => -1, 1 => 2, 3 => -1, 4 => 1, 7 => 3, 15 => -1, 19 => 1, 39 => -1, 79 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_80_eta_1m1_2p2_4m1_5p1_8p3_16m1_20p1_40m1_80p1_first_coeffs :
    first_coeffs 100 cuspForm_80_eta_1m1_2p2_4m1_5p1_8p3_16m1_20p1_40m1_80p1 =
    [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, -2, -2, 0, -3, -1, 0, 0, -2, 0,
     -1, 0, 2, -5, 0, 0, -2, -2, 2, 0, -1, 6, 0, 0, 4, 3, 1, 0, 4, 2,
     0, 0, 2, 9, 0, 0, -1, 1, 0, 0, 0, -6, 2, 0, -2, -2, 0, 0, -4, -4,
     2, 0, -2, -7, 0, 0, 0, -5, -6, 0, -1, 6, 0, 0, 2, 1, -4, 0, 2, -4,
     0, 0, -6, 5, -4, 0, 1, 6, 0, 0, -1, -6, 6, 0, 5, -4, 0, 0, 6, 6] := by
  eta_coeff

end WeightTwoCusps
