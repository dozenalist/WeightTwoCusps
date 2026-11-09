module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 234

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-2) η(2z)^4 η(3z) η(6z)^(-1) η(39z) η(78z)`; see
[the local level table](../../TABLE.md#level-234).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 41 (zero-based) at level 468; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-468).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z) η(6z)^(-1) η(39z) η(78z)` at level 234. -/
abbrev cuspForm_234_eta_1m2_2p4_3p1_6m1_39p1_78p1 : gamma0CuspForms 234 :=
  etaQuotientCuspForm 234 sparse![234; 0 => -2, 1 => 4, 2 => 1, 5 => -1, 38 => 1, 77 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_234_eta_1m2_2p4_3p1_6m1_39p1_78p1_first_coeffs :
    first_coeffs 100 cuspForm_234_eta_1m2_2p4_3p1_6m1_39p1_78p1 =
    [0, 0, 0, 0, 0, 1, 2, 1, 1, 0, -1, 1, 0, 0, -2, -2, 1, -2, 0, -1,
     -1, 0, -1, 0, -4, 0, 1, 0, 0, -2, 0, 0, 0, 2, 1, -2, 0, -1, 0, 0,
     1, 3, 0, 0, 1, -2, -1, 1, 0, 0, -2, 4, 0, 2, 2, 0, 4, 0, 2, -1,
     2, 2, 2, 4, 0, -1, 0, 0, 2, 0, -1, 1, -2, -1, 2, 0, 0, 2, 0, -2,
     -5, 0, 1, -3, -4, -1, -4, -4, 3, -3, -4, 0, 0, 4, -3, 2, 2, 1, 4, -2] := by
  eta_coeff

end WeightTwoCusps
