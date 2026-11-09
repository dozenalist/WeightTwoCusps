module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 150

The eta expression is `η(z)^(-1) η(2z) η(3z) η(5z) η(10z) η(25z) η(50z)^(-1) η(150z)`; see
[the local level table](../../TABLE.md#level-150).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z) η(5z) η(10z) η(25z) η(50z)^(-1) η(150z)` at level 150. -/
abbrev cuspForm_150_eta_1m1_2p1_3p1_5p1_10p1_25p1_50m1_150p1 : gamma0CuspForms 150 :=
  etaQuotientCuspForm 150 sparse![150; 0 => -1, 1 => 1, 2 => 1, 4 => 1, 9 => 1, 24 => 1, 49 => -1, 149 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_150_eta_1m1_2p1_3p1_5p1_10p1_25p1_50m1_150p1_first_coeffs :
    first_coeffs 100 cuspForm_150_eta_1m1_2p1_3p1_5p1_10p1_25p1_50m1_150p1 =
    [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, -1, 0, -1, -1,
     0, -1, 1, -1, 0, -1, -2, -2, 0, -1, -2, -2, -2, -2, -3, -2, 1, -2, -3, -1,
     -3, 2, -1, 1, -1, 0, 1, -1, 1, 0, 2, 0, 2, 0, 0, 2, 1, 4, 2, 3,
     1, -1, 3, 3, 4, 2, -1, 2, 0, 1, 2, 0, 0, -1, 4, 0, 2, 1, 4, 3,
     4, -1, -7, 0, -2, 2, -2, 1, -3, -6, 1, 5, 1, 2, 1, -4, -1, -1, 5, -2] := by
  eta_coeff

end WeightTwoCusps
