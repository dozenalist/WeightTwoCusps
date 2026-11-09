module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 308

The eta expression is `η(z)^(-2) η(2z)^4 η(7z) η(14z)^(-1) η(77z)^(-1) η(154z)^3`; see
[the local level table](../../TABLE.md#level-308).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(7z) η(14z)^(-1) η(77z)^(-1) η(154z)^3` at level 308. -/
abbrev cuspForm_308_eta_1m2_2p4_7p1_14m1_77m1_154p3 : gamma0CuspForms 308 :=
  etaQuotientCuspForm 308 sparse![308; 0 => -2, 1 => 4, 6 => 1, 13 => -1, 76 => -1, 153 => 3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_308_eta_1m2_2p4_7p1_14m1_77m1_154p3_first_coeffs :
    first_coeffs 100 cuspForm_308_eta_1m2_2p4_7p1_14m1_77m1_154p3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 2,
     2, 0, 3, 1, -2, 1, 0, 0, 1, -1, -2, 2, 2, -2, 0, -1, -1, 3, -2, -5,
     0, -2, 0, -2, -3, 2, 0, 2, -2, -1, 1, -1, -2, -2, -2, 0, 1, -4, -2, 0,
     1, -2, 2, -1, 2, 2, -6, 0, -4, -4, 1, 0, -1, 4, 1, 2, 2, 1, 1, -2,
     -4, -1, 2, -2, 0, -3, -1, 4, 2, 0, 2, -2, 4, 3, -2, -3, 0, 4, 0, 1] := by
  eta_coeff

end WeightTwoCusps
