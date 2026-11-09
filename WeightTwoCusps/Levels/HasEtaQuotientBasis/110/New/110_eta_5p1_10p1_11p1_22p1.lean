module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 110

The eta expression is `η(5z) η(10z) η(11z) η(22z)`; see
[the local level table](../../TABLE.md#level-110).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(5z) η(10z) η(11z) η(22z)` at level 110. -/
abbrev cuspForm_110_eta_5p1_10p1_11p1_22p1 : gamma0CuspForms 110 :=
  etaQuotientCuspForm 110 sparse![110; 4 => 1, 9 => 1, 10 => 1, 21 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_110_eta_5p1_10p1_11p1_22p1_first_coeffs :
    first_coeffs 100 cuspForm_110_eta_5p1_10p1_11p1_22p1 =
    [0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -2, -1, 0, 0, 0, 1, 1, 0,
     0, 0, 0, 2, -2, 0, 0, 2, -1, 2, 0, 0, 1, 0, 4, 1, 0, 0, -2, -2,
     -1, 0, 0, -1, 0, -2, 0, -2, 0, -4, 1, 0, 1, 0, -2, 0, 0, 0, 2, 0,
     2, 0, -4, -1, 0, 1, 0, -4, 3, 4, 0, 0, 4, 1, -2, 0, 0, -1, -2, 4,
     -2, 0, 4, -1, 4, 1, 0, 4, 1, 0, -2, 0, 0, 2, -4, -2, 0, 2, -1, 2] := by
  eta_coeff

end WeightTwoCusps
