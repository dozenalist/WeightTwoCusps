module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 336

The eta expression is `η(z)^2 η(2z)^(-1) η(8z) η(56z) η(112z)^(-1) η(168z) η(336z)`; see
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

/-- The cuspidal eta quotient `η(z)^2 η(2z)^(-1) η(8z) η(56z) η(112z)^(-1) η(168z) η(336z)` at level 336. -/
abbrev cuspForm_336_eta_1p2_2m1_8p1_56p1_112m1_168p1_336p1 : gamma0CuspForms 336 :=
  etaQuotientCuspForm 336 sparse![336; 0 => 2, 1 => -1, 7 => 1, 55 => 1, 111 => -1, 167 => 1, 335 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_336_eta_1p2_2m1_8p1_56p1_112m1_168p1_336p1_first_coeffs :
    first_coeffs 100 cuspForm_336_eta_1p2_2m1_8p1_56p1_112m1_168p1_336p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
     -2, 0, 0, 2, 0, 0, 0, -1, 0, 0, 0, -2, 0, 0, 0, 1, 4, 0, 0, -2,
     0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0, 2, 0, 0, 0, 1,
     0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, -2, 0, 0, 0, 2, 2, 0, 0, 0,
     0, 0, 0, 3, -2, 0, 0, 2, 0, 0, 0, -1, -4, 0, 0, 4, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
