module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 340

The eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(5z)^2 η(10z)^(-2) η(20z) η(34z) η(340z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(5z)^2 η(10z)^(-2) η(20z) η(34z) η(340z)` at level 340. -/
abbrev cuspForm_340_eta_1m2_2p5_4m2_5p2_10m2_20p1_34p1_340p1 : gamma0CuspForms 340 :=
  etaQuotientCuspForm 340 sparse![340; 0 => -2, 1 => 5, 3 => -2, 4 => 2, 9 => -2, 19 => 1, 33 => 1, 339 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_340_eta_1m2_2p5_4m2_5p2_10m2_20p1_34p1_340p1_first_coeffs :
    first_coeffs 100 cuspForm_340_eta_1m2_2p5_4m2_5p2_10m2_20p1_34p1_340p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0,
     2, -2, -4, 0, 0, -2, 1, 2, 0, 0, -2, -2, -2, 0, 0, -2, 3, 2, 0, 0,
     2, 0, -2, 0, 0, 2, 0, 4, 0, 0, 3, -4, 0, 0, -2, 2, 4, 0, 0, 2,
     -1, -2, -2, 0, 2, 0, 5, 2, 0, 2, -5, -2, -2, 0, -2, 0, 2, 0, 0, -2,
     -2, -6, 2, 0, -5, -2, -1, -2, -2, 2, 4, 0, -4, 2, -1, -4, 2, 2, 2, 4] := by
  eta_coeff

end WeightTwoCusps
