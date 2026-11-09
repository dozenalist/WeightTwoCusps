module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 76

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-3) η(2z)^8 η(4z)^(-3) η(19z) η(76z)`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-76).
The table has full eta basis = NO at this level: these supporting forms
do not span the whole cusp-form space.

It is needed by table vector 6 (zero-based) at level 456; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-456).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^8 η(4z)^(-3) η(19z) η(76z)` at level 76. -/
abbrev cuspForm_76_eta_1m3_2p8_4m3_19p1_76p1 : gamma0CuspForms 76 :=
  etaQuotientCuspForm 76 sparse![76; 0 => -3, 1 => 8, 3 => -3, 18 => 1, 75 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_76_eta_1m3_2p8_4m3_19p1_76p1_first_coeffs :
    first_coeffs 100 cuspForm_76_eta_1m3_2p8_4m3_19p1_76p1 =
    [0, 0, 0, 0, 1, 3, 1, -2, 2, 1, -4, -1, -2, 0, 2, -4, -1, -2, -2, 1,
     0, 2, -2, 1, -3, -5, 3, -2, 1, 6, 6, 2, -2, -2, 4, 5, 0, 2, -1, 3,
     2, 2, -3, -1, 4, -3, 0, -5, 2, -4, 2, 4, -4, 4, -1, 7, 0, -1, -5, -8,
     -2, -3, -2, 3, 3, -6, 2, -2, -1, 0, -4, 0, 0, -8, -2, 2, 0, -3, -4, 6,
     -6, -4, 0, 6, 0, 3, 4, -5, 4, 2, 2, 2, -1, -2, 6, -1, 5, 2, 4, 5] := by
  eta_coeff

end WeightTwoCusps
