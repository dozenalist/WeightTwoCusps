module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(z) η(5z)^(-1) η(7z)^(-1) η(10z)^2 η(14z)^2 η(20z)^(-1) η(28z)^(-1) η(35z) η(60z) η(84z)`; see
[the local level table](../../TABLE.md#level-420).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(5z)^(-1) η(7z)^(-1) η(10z)^2 η(14z)^2 η(20z)^(-1) η(28z)^(-1) η(35z) η(60z) η(84z)` at level 420. -/
abbrev cuspForm_420_eta_1p1_5m1_7m1_10p2_14p2_20m1_28m1_35p1_60p1_84p1 : gamma0CuspForms 420 :=
  etaQuotientCuspForm 420 sparse![420; 0 => 1, 4 => -1, 6 => -1, 9 => 2, 13 => 2, 19 => -1, 27 => -1, 34 => 1, 59 => 1, 83 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_420_eta_1p1_5m1_7m1_10p2_14p2_20m1_28m1_35p1_60p1_84p1_first_coeffs :
    first_coeffs 100 cuspForm_420_eta_1p1_5m1_7m1_10p2_14p2_20m1_28m1_35p1_60p1_84p1 =
    [0, 0, 0, 0, 0, 0, 0, 1, -1, -1, 0, 0, 2, -1, 1, -1, -1, 1, 0, 2,
     -1, 0, 0, -1, -1, 0, 0, 1, 0, 0, -2, -2, 2, 2, 0, 0, 0, 0, 1, 1,
     2, -1, 0, -1, 0, -1, -1, 0, 0, -2, 0, -1, 0, 1, 0, 0, -1, 2, 0, 1,
     0, 2, -1, 1, 0, 0, 0, -1, 1, -1, 0, -2, -2, 2, -1, 1, 0, -2, 3, -1,
     1, 1, 0, 1, -1, 3, 0, -2, 0, -3, 2, 0, -1, -1, 2, 0, -1, -1, -2, 0] := by
  eta_coeff

end WeightTwoCusps
