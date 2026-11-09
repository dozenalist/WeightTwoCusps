module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 308

The eta expression is `η(z)^(-1) η(2z)^3 η(11z) η(22z)^(-1) η(77z)^(-2) η(154z)^4`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^3 η(11z) η(22z)^(-1) η(77z)^(-2) η(154z)^4` at level 308. -/
abbrev cuspForm_308_eta_1m1_2p3_11p1_22m1_77m2_154p4 : gamma0CuspForms 308 :=
  etaQuotientCuspForm 308 sparse![308; 0 => -1, 1 => 3, 10 => 1, 21 => -1, 76 => -2, 153 => 4]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_308_eta_1m1_2p3_11p1_22m1_77m2_154p4_first_coeffs :
    first_coeffs 100 cuspForm_308_eta_1m1_2p3_11p1_22m1_77m2_154p4 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
     1, -1, 0, -1, -2, 1, -1, -1, 0, 1, 0, -2, 2, 0, 3, 3, -1, 1, 0, 2,
     0, -1, 0, -1, -1, -2, -2, 1, 1, -2, -2, -2, -2, -1, 2, 1, 1, 3, -3, -2,
     4, 1, 0, 2, 3, -2, 0, -3, -4, 4, 0, 0, -2, 1, 2, -1, 0, 1, 4, 4,
     -4, 2, 3, 1, 2, -2, 3, -3, -1, -6, -4, 4, 1, -3, -4, -3, 0, 0, 0, 1] := by
  eta_coeff

end WeightTwoCusps
