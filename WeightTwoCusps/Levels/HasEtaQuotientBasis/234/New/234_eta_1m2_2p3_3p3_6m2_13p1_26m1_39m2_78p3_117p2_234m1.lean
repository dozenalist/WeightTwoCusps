module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 234

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-2) η(2z)^3 η(3z)^3 η(6z)^(-2) η(13z) η(26z)^(-1) η(39z)^(-2) η(78z)^3 η(117z)^2 η(234z)^(-1)`; see
[the local level table](../../TABLE.md#level-234).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 25 (zero-based) at level 468; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-468).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^3 η(6z)^(-2) η(13z) η(26z)^(-1) η(39z)^(-2) η(78z)^3 η(117z)^2 η(234z)^(-1)` at level 234. -/
abbrev cuspForm_234_eta_1m2_2p3_3p3_6m2_13p1_26m1_39m2_78p3_117p2_234m1 : gamma0CuspForms 234 :=
  etaQuotientCuspForm 234 sparse![234; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 12 => 1, 25 => -1, 38 => -2, 77 => 3, 116 => 2, 233 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_234_eta_1m2_2p3_3p3_6m2_13p1_26m1_39m2_78p3_117p2_234m1_first_coeffs :
    first_coeffs 100 cuspForm_234_eta_1m2_2p3_3p3_6m2_13p1_26m1_39m2_78p3_117p2_234m1 =
    [0, 0, 0, 0, 0, 0, 1, 2, 2, 1, -1, 0, 0, 1, 1, -3, -2, -3, 1, 0,
     -4, -1, -4, 0, -1, -1, -1, -4, 4, 2, 1, 0, 0, 4, -2, 3, 1, -2, 2, 0,
     3, -2, 3, 5, 0, -1, 2, 6, 0, 1, 0, -1, 1, 2, 0, -6, -5, 4, 2, -6,
     -3, -4, -2, 3, 2, -1, -6, 2, 5, 0, -4, -2, -1, -6, 3, 1, -2, 2, -1, 2,
     0, 4, 10, 0, -1, 4, 6, 0, 2, -2, -2, 1, 0, 2, -9, -4, 1, 0, -4, -2] := by
  eta_coeff

end WeightTwoCusps
