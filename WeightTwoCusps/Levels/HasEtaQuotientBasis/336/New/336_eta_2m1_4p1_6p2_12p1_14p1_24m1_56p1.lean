module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 336

The eta expression is `η(2z)^(-1) η(4z) η(6z)^2 η(12z) η(14z) η(24z)^(-1) η(56z)`; see
[the local level table](../../TABLE.md#level-336).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-1) η(4z) η(6z)^2 η(12z) η(14z) η(24z)^(-1) η(56z)` at level 336. -/
abbrev cuspForm_336_eta_2m1_4p1_6p2_12p1_14p1_24m1_56p1 : gamma0CuspForms 336 :=
  etaQuotientCuspForm 336 sparse![336; 1 => -1, 3 => 1, 5 => 2, 11 => 1, 13 => 1, 23 => -1, 55 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_336_eta_2m1_4p1_6p2_12p1_14p1_24m1_56p1_first_coeffs :
    first_coeffs 100 cuspForm_336_eta_2m1_4p1_6p2_12p1_14p1_24m1_56p1 =
    [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, -2, 0, -2, 0, -3,
     0, -1, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 2, 0, -1, 0, 0, 0, 0,
     0, -2, 0, 4, 0, -1, 0, 2, 0, 0, 0, 2, 0, 6, 0, 2, 0, 2, 0, -1,
     0, -1, 0, -1, 0, 0, 0, -2, 0, -4, 0, 2, 0, 8, 0, 3, 0, 2, 0, -4,
     0, 4, 0, -1, 0, -4, 0, 0, 0, -8, 0, 1, 0, -2, 0, -2, 0, 2, 0, -4] := by
  eta_coeff

end WeightTwoCusps
