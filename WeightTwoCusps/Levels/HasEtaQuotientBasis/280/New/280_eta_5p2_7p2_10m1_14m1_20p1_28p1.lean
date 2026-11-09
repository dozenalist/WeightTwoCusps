module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 280

The eta expression is `η(5z)^2 η(7z)^2 η(10z)^(-1) η(14z)^(-1) η(20z) η(28z)`; see
[the local level table](../../TABLE.md#level-280).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(5z)^2 η(7z)^2 η(10z)^(-1) η(14z)^(-1) η(20z) η(28z)` at level 280. -/
abbrev cuspForm_280_eta_5p2_7p2_10m1_14m1_20p1_28p1 : gamma0CuspForms 280 :=
  etaQuotientCuspForm 280 sparse![280; 4 => 2, 6 => 2, 9 => -1, 13 => -1, 19 => 1, 27 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_280_eta_5p2_7p2_10m1_14m1_20p1_28p1_first_coeffs :
    first_coeffs 100 cuspForm_280_eta_5p2_7p2_10m1_14m1_20p1_28p1 =
    [0, 0, 1, 0, 0, 0, 0, -2, 0, -2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0,
     0, 0, 1, 0, 0, 0, 0, 2, 0, -2, 1, 0, 0, 0, -4, -2, 0, 2, 0, 0,
     0, 0, -7, 0, 0, 0, 0, 0, 0, 6, 1, 0, 0, 0, 0, 2, 0, 2, -3, 0,
     0, 0, 2, 6, 0, 0, 0, 2, 0, 4, -3, 0, 0, 0, -4, 0, 0, -6, -3, 0,
     0, 0, 2, -6, 0, 0, -2, 2, 0, -4, -2, 4, 0, 2, -4, 2, 0, -4, 5, 0] := by
  eta_coeff

end WeightTwoCusps
