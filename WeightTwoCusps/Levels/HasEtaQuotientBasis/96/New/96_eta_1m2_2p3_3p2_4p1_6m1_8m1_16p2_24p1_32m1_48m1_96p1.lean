module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 96

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-2) η(2z)^3 η(3z)^2 η(4z) η(6z)^(-1) η(8z)^(-1) η(16z)^2 η(24z) η(32z)^(-1) η(48z)^(-1) η(96z)`; see
[the local level table](../../TABLE.md#level-96).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 9 (zero-based) at level 192; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-192).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^2 η(4z) η(6z)^(-1) η(8z)^(-1) η(16z)^2 η(24z) η(32z)^(-1) η(48z)^(-1) η(96z)` at level 96. -/
abbrev cuspForm_96_eta_1m2_2p3_3p2_4p1_6m1_8m1_16p2_24p1_32m1_48m1_96p1 : gamma0CuspForms 96 :=
  etaQuotientCuspForm 96 sparse![96; 0 => -2, 1 => 3, 2 => 2, 3 => 1, 5 => -1, 7 => -1, 15 => 2, 23 => 1, 31 => -1, 47 => -1, 95 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_96_eta_1m2_2p3_3p2_4p1_6m1_8m1_16p2_24p1_32m1_48m1_96p1_first_coeffs :
    first_coeffs 100 cuspForm_96_eta_1m2_2p3_3p2_4p1_6m1_8m1_16p2_24p1_32m1_48m1_96p1 =
    [0, 0, 0, 1, 2, 2, 2, 0, 0, 0, 0, 2, -2, 0, 0, -2, 0, -4, 0, -2,
     -4, -2, -8, -4, 0, 0, 0, -5, 0, -2, -4, 4, 0, 4, 0, 0, 2, -4, 8, 10,
     0, 4, 0, 2, 8, 2, 16, 0, 0, 8, 0, 2, -4, 6, 2, -4, 0, -4, 0, 2,
     4, 4, -16, 0, 0, -4, 0, -2, 4, -4, 0, 4, 0, -8, 0, -1, -8, -8, -4, -4,
     0, 0, 0, -2, 0, -4, -8, -18, 0, 8, 0, 0, -16, 6, 0, 4, 0, -8, 0, 2] := by
  eta_coeff

end WeightTwoCusps
