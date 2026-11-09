module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 440

The eta expression is `η(4z) η(10z)^(-1) η(20z)^2 η(44z) η(110z)^(-1) η(220z)^2`; see
[the local level table](../../TABLE.md#level-440).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z) η(10z)^(-1) η(20z)^2 η(44z) η(110z)^(-1) η(220z)^2` at level 440. -/
abbrev cuspForm_440_eta_4p1_10m1_20p2_44p1_110m1_220p2 : gamma0CuspForms 440 :=
  etaQuotientCuspForm 440 sparse![440; 3 => 1, 9 => -1, 19 => 2, 43 => 1, 109 => -1, 219 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_440_eta_4p1_10m1_20p2_44p1_110m1_220p2_first_coeffs :
    first_coeffs 100 cuspForm_440_eta_4p1_10m1_20p2_44p1_110m1_220p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
     0, -1, 0, 0, 0, -1, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 1, 0, 0,
     0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0,
     0, -1, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, 0, 0, 1, 0, 0, 0, 1,
     0, -2, 0, 0, 0, -1, 0, -1, 0, -1, 0, -2, 0, 0, 0, 0, 0, 1, 0, 0] := by
  eta_coeff

end WeightTwoCusps
