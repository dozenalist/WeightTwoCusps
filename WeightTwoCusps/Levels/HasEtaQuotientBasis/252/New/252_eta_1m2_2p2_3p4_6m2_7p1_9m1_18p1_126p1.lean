module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^4 η(6z)^(-2) η(7z) η(9z)^(-1) η(18z) η(126z)`; see
[the local level table](../../TABLE.md#level-252).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^4 η(6z)^(-2) η(7z) η(9z)^(-1) η(18z) η(126z)` at level 252. -/
abbrev cuspForm_252_eta_1m2_2p2_3p4_6m2_7p1_9m1_18p1_126p1 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -2, 1 => 2, 2 => 4, 5 => -2, 6 => 1, 8 => -1, 17 => 1, 125 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m2_2p2_3p4_6m2_7p1_9m1_18p1_126p1_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m2_2p2_3p4_6m2_7p1_9m1_18p1_126p1 =
    [0, 0, 0, 0, 0, 0, 1, 2, 3, 2, 1, 2, 2, 3, 0, 0, 1, 2, 4, 1,
     0, 0, 0, 1, -1, -3, 0, -3, 1, -2, -2, 0, -3, 2, -2, -1, -4, -3, 0, -2,
     -3, -2, -1, 1, -3, -1, -1, -4, 0, -8, -3, -2, -1, 0, -8, -2, 0, 2, 2, -4,
     -4, -1, 0, 1, -1, -1, -2, 0, 6, -2, 0, -4, 2, 0, -3, 0, -1, 3, 4, -3,
     -6, 2, -2, 6, -2, 2, 3, 0, 5, -2, 1, 2, 0, 0, 2, 3, 5, 2, 0, 0] := by
  eta_coeff

end WeightTwoCusps
