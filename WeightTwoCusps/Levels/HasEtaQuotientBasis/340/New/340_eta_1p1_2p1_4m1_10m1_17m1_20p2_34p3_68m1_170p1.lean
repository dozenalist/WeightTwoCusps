module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 340

The eta expression is `η(z) η(2z) η(4z)^(-1) η(10z)^(-1) η(17z)^(-1) η(20z)^2 η(34z)^3 η(68z)^(-1) η(170z)`; see
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

/-- The cuspidal eta quotient `η(z) η(2z) η(4z)^(-1) η(10z)^(-1) η(17z)^(-1) η(20z)^2 η(34z)^3 η(68z)^(-1) η(170z)` at level 340. -/
abbrev cuspForm_340_eta_1p1_2p1_4m1_10m1_17m1_20p2_34p3_68m1_170p1 : gamma0CuspForms 340 :=
  etaQuotientCuspForm 340 sparse![340; 0 => 1, 1 => 1, 3 => -1, 9 => -1, 16 => -1, 19 => 2, 33 => 3, 67 => -1, 169 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_340_eta_1p1_2p1_4m1_10m1_17m1_20p2_34p3_68m1_170p1_first_coeffs :
    first_coeffs 100 cuspForm_340_eta_1p1_2p1_4m1_10m1_17m1_20p2_34p3_68m1_170p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -2, 1, 1, 1, -1, 1, 2, -2, -1,
     -1, -1, 0, 0, 1, 2, 1, -2, -2, 2, 1, 0, -1, 3, 0, -3, 0, -2, 0, 0,
     1, 2, 1, -3, 0, 2, 2, -2, -2, 1, 0, -4, 0, 2, -1, 4, 0, 2, 0, -4,
     0, 2, 1, 2, -1, 2, -2, -4, 0, -2, 0, 0, 1, 0, 0, -2, 1, 4, 1, 0,
     -2, 3, -1, -2, 0, -2, 0, 2, 3, -1, 1, 0, -1, 0, -2, 0, 0, -4, 1, -4] := by
  eta_coeff

end WeightTwoCusps
