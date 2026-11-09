module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 68

The eta expression is `η(z)^(-1) η(2z)^2 η(4z) η(17z) η(34z)^2 η(68z)^(-1)`; see
[the local level table](../../TABLE.md#level-68).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(4z) η(17z) η(34z)^2 η(68z)^(-1)` at level 68. -/
abbrev cuspForm_68_eta_1m1_2p2_4p1_17p1_34p2_68m1 : gamma0CuspForms 68 :=
  etaQuotientCuspForm 68 sparse![68; 0 => -1, 1 => 2, 3 => 1, 16 => 1, 33 => 2, 67 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_68_eta_1m1_2p2_4p1_17p1_34p2_68m1_first_coeffs :
    first_coeffs 100 cuspForm_68_eta_1m1_2p2_4p1_17p1_34p2_68m1 =
    [0, 1, 1, 0, 1, -1, -1, 1, -1, -1, -1, 0, -1, 0, 0, -2, 1, 0, -1, -2,
     -1, 0, 3, 1, -1, 1, 0, 2, 0, 3, 0, 1, 3, -2, 0, -2, -1, 1, -4, 2,
     3, -4, 4, 4, 3, -1, 2, 0, -1, 5, -3, 0, 0, 4, 2, -2, -8, 0, 3, -4,
     0, -7, 0, -9, -3, -2, -6, 6, 0, 0, -4, -3, 5, -2, -3, 4, -4, -4, -2, 5,
     -1, 3, 0, -4, 4, -1, 6, 2, 3, 6, 3, -8, 2, 4, 0, 8, -1, 4, 9, 2] := by
  eta_coeff

end WeightTwoCusps
