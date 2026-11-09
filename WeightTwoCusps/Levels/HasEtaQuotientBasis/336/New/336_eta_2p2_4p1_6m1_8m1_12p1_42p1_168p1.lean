module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 336

The eta expression is `η(2z)^2 η(4z) η(6z)^(-1) η(8z)^(-1) η(12z) η(42z) η(168z)`; see
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

/-- The cuspidal eta quotient `η(2z)^2 η(4z) η(6z)^(-1) η(8z)^(-1) η(12z) η(42z) η(168z)` at level 336. -/
abbrev cuspForm_336_eta_2p2_4p1_6m1_8m1_12p1_42p1_168p1 : gamma0CuspForms 336 :=
  etaQuotientCuspForm 336 sparse![336; 1 => 2, 3 => 1, 5 => -1, 7 => -1, 11 => 1, 41 => 1, 167 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_336_eta_2p2_4p1_6m1_8m1_12p1_42p1_168p1_first_coeffs :
    first_coeffs 100 cuspForm_336_eta_2p2_4p1_6m1_8m1_12p1_42p1_168p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -2, 0, -2, 0, 5, 0, 0, 0, -2,
     0, 1, 0, 0, 0, 0, 0, -4, 0, -2, 0, 2, 0, 4, 0, 0, 0, 2, 0, 1,
     0, 0, 0, -2, 0, -6, 0, 4, 0, 0, 0, -2, 0, 2, 0, 2, 0, -7, 0, 0,
     0, 2, 0, -1, 0, 2, 0, 2, 0, 8, 0, 2, 0, 0, 0, -10, 0, 0, 0, 0,
     0, -4, 0, 0, 0, 2, 0, 4, 0, -4, 0, 0, 0, -4, 0, 2, 0, 4, 0, -2] := by
  eta_coeff

end WeightTwoCusps
