module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-2) η(2z) η(3z)^5 η(6z)^(-2) η(7z)^2 η(14z)^(-1) η(21z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^5 η(6z)^(-2) η(7z)^2 η(14z)^(-1) η(21z)` at level 252. -/
abbrev cuspForm_252_eta_1m2_2p1_3p5_6m2_7p2_14m1_21p1 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -2, 1 => 1, 2 => 5, 5 => -2, 6 => 2, 13 => -1, 20 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m2_2p1_3p5_6m2_7p2_14m1_21p1_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m2_2p1_3p5_6m2_7p2_14m1_21p1 =
    [0, 1, 2, 4, 3, 4, 4, 7, 6, 4, 2, 4, 4, 6, 2, 4, 3, 4, 8, 4,
     4, 0, 0, 4, -4, -5, -4, -4, 1, -8, -4, 0, -6, 0, -10, -4, -4, -6, 0, -12,
     -6, -4, 0, 0, -12, -8, 0, -8, -4, -31, -10, -8, -6, 0, -20, -8, -2, -4, 6, -16,
     -12, -2, -8, 4, -9, -16, 0, -4, 4, -8, 2, 4, 0, -6, -4, 4, 4, 4, -4, -12,
     -4, 8, -10, 8, -8, 4, 16, 0, 4, -4, 0, 14, 4, 8, 8, -8, 20, 18, 2, -8] := by
  eta_coeff

end WeightTwoCusps
