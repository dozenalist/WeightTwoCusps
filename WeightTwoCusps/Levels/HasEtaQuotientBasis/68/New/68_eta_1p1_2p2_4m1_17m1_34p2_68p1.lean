module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 68

The eta expression is `η(z) η(2z)^2 η(4z)^(-1) η(17z)^(-1) η(34z)^2 η(68z)`; see
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

/-- The cuspidal eta quotient `η(z) η(2z)^2 η(4z)^(-1) η(17z)^(-1) η(34z)^2 η(68z)` at level 68. -/
abbrev cuspForm_68_eta_1p1_2p2_4m1_17m1_34p2_68p1 : gamma0CuspForms 68 :=
  etaQuotientCuspForm 68 sparse![68; 0 => 1, 1 => 2, 3 => -1, 16 => -1, 33 => 2, 67 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_68_eta_1p1_2p2_4m1_17m1_34p2_68p1_first_coeffs :
    first_coeffs 100 cuspForm_68_eta_1p1_2p2_4m1_17m1_34p2_68p1 =
    [0, 0, 0, 0, 0, 1, -1, -3, 2, 2, 1, 0, -1, 2, -4, -2, 0, -1, 2, 2,
     1, 0, 3, -3, -1, 2, 2, 2, -4, -3, 0, -3, -2, -2, -1, 6, 2, 3, 0, 2,
     -3, 2, 4, 0, 3, -7, -2, 0, -1, -4, -2, 0, 2, -2, 2, -2, 4, 0, -3, 8,
     0, 3, -4, 3, 4, -6, -6, 2, -1, 0, 4, 1, -4, 4, -1, 4, 0, -4, -2, -7,
     1, -6, 6, 0, 4, 1, 2, 2, 3, -4, -3, 0, -2, 4, 0, 0, -1, 2, 0, 2] := by
  eta_coeff

end WeightTwoCusps
