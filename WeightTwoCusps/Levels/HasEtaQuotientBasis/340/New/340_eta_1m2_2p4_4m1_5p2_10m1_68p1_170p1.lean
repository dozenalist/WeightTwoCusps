module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 340

The eta expression is `η(z)^(-2) η(2z)^4 η(4z)^(-1) η(5z)^2 η(10z)^(-1) η(68z) η(170z)`; see
[the local level table](../../TABLE.md#level-340).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(4z)^(-1) η(5z)^2 η(10z)^(-1) η(68z) η(170z)` at level 340. -/
abbrev cuspForm_340_eta_1m2_2p4_4m1_5p2_10m1_68p1_170p1 : gamma0CuspForms 340 :=
  etaQuotientCuspForm 340 sparse![340; 0 => -2, 1 => 4, 3 => -1, 4 => 2, 9 => -1, 67 => 1, 169 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_340_eta_1m2_2p4_4m1_5p2_10m1_68p1_170p1_first_coeffs :
    first_coeffs 100 cuspForm_340_eta_1m2_2p4_4m1_5p2_10m1_68p1_170p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 2, 3, 0, 0, 2, 0, 0,
     3, 0, 0, 2, -1, 0, 0, 0, 0, 0, -2, 0, 2, -2, 1, 0, 0, -2, 0, 0,
     -1, 2, -4, -2, -2, 0, 0, 0, 0, 0, 0, -4, 0, 0, -1, 0, 0, -2, 0, 0,
     -2, -2, 1, -2, -4, 0, 0, 2, 0, 0, -4, -2, 0, -2, 2, 0, 0, 0, -1, -2,
     0, -4, -5, 2, -4, -2, 0, -2, -3, 0, 1, -2, -1, -2, 2, 0, 0, 0, 2, 0] := by
  eta_coeff

end WeightTwoCusps
