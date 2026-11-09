module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 392

The eta expression is `η(z)^(-1) η(2z)^2 η(14z)^(-1) η(28z)^3 η(49z) η(98z) η(196z)^(-1)`; see
[the local level table](../../TABLE.md#level-392).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(14z)^(-1) η(28z)^3 η(49z) η(98z) η(196z)^(-1)` at level 392. -/
abbrev cuspForm_392_eta_1m1_2p2_14m1_28p3_49p1_98p1_196m1 : gamma0CuspForms 392 :=
  etaQuotientCuspForm 392 sparse![392; 0 => -1, 1 => 2, 13 => -1, 27 => 3, 48 => 1, 97 => 1, 195 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_392_eta_1m1_2p2_14m1_28p3_49p1_98p1_196m1_first_coeffs :
    first_coeffs 100 cuspForm_392_eta_1m1_2p2_14m1_28p3_49p1_98p1_196m1 =
    [0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 2, 0, 1, 0,
     0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 1, 1, 0, -1,
     0, 0, 0, 1, -1, 0, 1, 0, 0, 0, -2, 0, 0, -1, 0, 0, 0, -2, -1, 0,
     -1, 0, 0, -1, -1, -3, 0, -1, 0, 0, 0, -3, -3, 0, -4, 0, 0, -2, -1, 1,
     0, 0, 0, 0, 0, -1, -2, 0, 2, 0, 0, 1, -2, 1, 0, -1, 0, 0, 0, -4] := by
  eta_coeff

end WeightTwoCusps
