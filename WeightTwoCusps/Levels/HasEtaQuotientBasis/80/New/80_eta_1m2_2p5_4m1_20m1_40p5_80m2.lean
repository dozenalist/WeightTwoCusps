module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 80

This additional source is not in the report's chosen span list at its own
level. Its eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-1) η(20z)^(-1) η(40z)^5 η(80z)^(-2)`; see
[the local level table](../../TABLE.md#level-80).
This is an additional source for higher levels, not an entry of the
table-ordered basis at this level.

It is needed by table vector 9 (zero-based) at level 400; see
[the target table block](../../../HasEtaQuotientBasis/TABLE.md#level-400).

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-1) η(20z)^(-1) η(40z)^5 η(80z)^(-2)` at level 80. -/
abbrev cuspForm_80_eta_1m2_2p5_4m1_20m1_40p5_80m2 : gamma0CuspForms 80 :=
  etaQuotientCuspForm 80 sparse![80; 0 => -2, 1 => 5, 3 => -1, 19 => -1, 39 => 5, 79 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_80_eta_1m2_2p5_4m1_20m1_40p5_80m2_first_coeffs :
    first_coeffs 100 cuspForm_80_eta_1m2_2p5_4m1_20m1_40p5_80m2 =
    [0, 1, 2, 0, 0, 1, -2, 0, 0, -3, 0, 0, 0, -2, -2, 0, 0, 2, -2, 0,
     0, 0, 4, 0, 0, 1, 0, 0, 0, -2, 2, 0, 0, 0, -4, 0, 0, 6, 0, 0,
     0, -6, -4, 0, 0, -3, 10, 0, 0, 9, 2, 0, 0, 6, 4, 0, 0, 0, 4, 0,
     0, -2, -12, 0, 0, -2, 0, 0, 0, 0, -6, 0, 0, -6, 8, 0, 0, -16, -4, 0,
     0, 9, 0, 0, 0, 2, -18, 0, 0, -6, -4, 0, 0, 0, -2, 0, 0, -14, 6, 0] := by
  eta_coeff

end WeightTwoCusps
