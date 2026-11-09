module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 234

The eta expression is `η(z)^(-1) η(2z)^2 η(3z)^(-1) η(6z)^2 η(9z) η(13z)^(-1) η(18z)^(-1) η(26z)^2 η(39z)^3 η(78z)^(-2) η(117z)^(-1) η(234z)`; see
[the local level table](../../TABLE.md#level-234).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(3z)^(-1) η(6z)^2 η(9z) η(13z)^(-1) η(18z)^(-1) η(26z)^2 η(39z)^3 η(78z)^(-2) η(117z)^(-1) η(234z)` at level 234. -/
abbrev cuspForm_234_eta_1m1_2p2_3m1_6p2_9p1_13m1_18m1_26p2_39p3_78m2_117m1_234p1 : gamma0CuspForms 234 :=
  etaQuotientCuspForm 234 sparse![234; 0 => -1, 1 => 2, 2 => -1, 5 => 2, 8 => 1, 12 => -1, 17 => -1, 25 => 2, 38 => 3, 77 => -2, 116 => -1, 233 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_234_eta_1m1_2p2_3m1_6p2_9p1_13m1_18m1_26p2_39p3_78m2_117m1_234p1_first_coeffs :
    first_coeffs 100 cuspForm_234_eta_1m1_2p2_3m1_6p2_9p1_13m1_18m1_26p2_39p3_78m2_117m1_234p1 =
    [0, 0, 0, 0, 0, 1, 1, 0, 2, 1, 0, 2, 0, 0, 1, 1, 0, -1, 1, 1,
     0, 2, 1, 0, 2, 0, 1, 0, 1, 1, -1, 0, -3, -1, 0, -2, 1, 0, -3, 1,
     -1, 1, -1, 0, -1, -6, -1, -6, -4, 1, -3, -3, 0, -5, -2, -2, 1, -2, -4, -1,
     -9, -3, -1, -5, 0, -2, -4, -4, -5, 2, 0, 7, 0, -1, 4, -3, 0, 4, -3, 3,
     -1, -2, 0, -1, 12, 2, 6, 4, -3, -3, 8, 0, 6, 0, 6, 2, 1, 5, -1, 15] := by
  eta_coeff

end WeightTwoCusps
