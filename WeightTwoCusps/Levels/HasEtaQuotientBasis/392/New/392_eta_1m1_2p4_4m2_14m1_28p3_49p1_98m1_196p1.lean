module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 392

The eta expression is `η(z)^(-1) η(2z)^4 η(4z)^(-2) η(14z)^(-1) η(28z)^3 η(49z) η(98z)^(-1) η(196z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^4 η(4z)^(-2) η(14z)^(-1) η(28z)^3 η(49z) η(98z)^(-1) η(196z)` at level 392. -/
abbrev cuspForm_392_eta_1m1_2p4_4m2_14m1_28p3_49p1_98m1_196p1 : gamma0CuspForms 392 :=
  etaQuotientCuspForm 392 sparse![392; 0 => -1, 1 => 4, 3 => -2, 13 => -1, 27 => 3, 48 => 1, 97 => -1, 195 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_392_eta_1m1_2p4_4m2_14m1_28p3_49p1_98m1_196p1_first_coeffs :
    first_coeffs 100 cuspForm_392_eta_1m1_2p4_4m2_14m1_28p3_49p1_98m1_196p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, -2, -1, 1, -1, -1, -1, 2, 2, -2,
     0, 1, 1, 0, 1, 1, 0, -2, -3, 2, -1, 0, 1, 1, 2, -3, -1, 0, 0, 1,
     0, 1, 2, -2, 0, 1, -2, 0, -1, 1, 0, -3, -2, 0, -1, 2, 3, 0, 3, -4,
     -1, 2, -3, 2, 2, 3, -1, -1, 3, -1, 0, 3, 2, -4, -3, 0, 1, 2, -5, 1,
     0, 0, 3, -4, 6, -2, -1, 2, -3, 0, -2, -1, 0, -2, -5, 3, 1, 1, -1, -1] := by
  eta_coeff

end WeightTwoCusps
