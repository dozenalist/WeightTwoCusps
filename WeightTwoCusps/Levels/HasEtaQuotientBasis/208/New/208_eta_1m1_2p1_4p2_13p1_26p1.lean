module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 208

The eta expression is `η(z)^(-1) η(2z) η(4z)^2 η(13z) η(26z)`; see
[the local level table](../../TABLE.md#level-208).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(4z)^2 η(13z) η(26z)` at level 208. -/
abbrev cuspForm_208_eta_1m1_2p1_4p2_13p1_26p1 : gamma0CuspForms 208 :=
  etaQuotientCuspForm 208 sparse![208; 0 => -1, 1 => 1, 3 => 2, 12 => 1, 25 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_208_eta_1m1_2p1_4p2_13p1_26p1_first_coeffs :
    first_coeffs 100 cuspForm_208_eta_1m1_2p1_4p2_13p1_26p1 =
    [0, 0, 1, 1, 1, 2, 0, 1, 2, 1, 1, 1, 1, 0, 3, 0, -1, 1, -1, 1,
     0, -2, 0, 2, 0, 1, 0, -3, -2, 0, -3, -5, 2, -2, -4, -1, -4, -2, -2, 0,
     -5, -2, 1, -3, 2, -4, -2, 5, -3, -5, 1, -5, 0, 4, 0, -6, -1, 0, -4, 3,
     -2, -2, 0, -3, -1, 1, -4, 3, 3, 2, 0, -1, 0, -2, 5, 2, -4, 6, -1, 4,
     4, 0, 6, 3, 0, -6, 4, 0, 8, 6, 0, -2, 6, 0, -1, 4, 0, 8, 7, -1] := by
  eta_coeff

end WeightTwoCusps
