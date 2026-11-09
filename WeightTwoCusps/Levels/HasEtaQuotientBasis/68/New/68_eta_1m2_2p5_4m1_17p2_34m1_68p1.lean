module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 68

The eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-1) η(17z)^2 η(34z)^(-1) η(68z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-1) η(17z)^2 η(34z)^(-1) η(68z)` at level 68. -/
abbrev cuspForm_68_eta_1m2_2p5_4m1_17p2_34m1_68p1 : gamma0CuspForms 68 :=
  etaQuotientCuspForm 68 sparse![68; 0 => -2, 1 => 5, 3 => -1, 16 => 2, 33 => -1, 67 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_68_eta_1m2_2p5_4m1_17p2_34m1_68p1_first_coeffs :
    first_coeffs 100 cuspForm_68_eta_1m2_2p5_4m1_17p2_34m1_68p1 =
    [0, 0, 0, 1, 2, 0, 0, 1, -2, 0, 0, -3, 0, 0, 0, -2, -2, 0, 0, 2,
     -4, -4, 0, -1, 0, 4, 0, 0, 8, 0, 0, 1, 6, 4, 0, 2, -6, 4, 0, 4,
     4, -4, 0, -2, 0, -4, 0, 0, 0, -4, 0, -1, -4, 4, 0, -2, -8, -4, 0, 2,
     0, 0, 0, -1, -2, -4, 0, 0, 2, 0, 0, -1, 6, 0, 0, -1, -8, 8, 0, -5,
     4, 4, 0, -2, 0, 0, 0, 2, 0, 4, 0, 0, 8, 0, 0, 4, 0, -4, 0, -1] := by
  eta_coeff

end WeightTwoCusps
