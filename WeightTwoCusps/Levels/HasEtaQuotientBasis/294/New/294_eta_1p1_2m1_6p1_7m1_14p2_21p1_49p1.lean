module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 294

The eta expression is `η(z) η(2z)^(-1) η(6z) η(7z)^(-1) η(14z)^2 η(21z) η(49z)`; see
[the local level table](../../TABLE.md#level-294).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(2z)^(-1) η(6z) η(7z)^(-1) η(14z)^2 η(21z) η(49z)` at level 294. -/
abbrev cuspForm_294_eta_1p1_2m1_6p1_7m1_14p2_21p1_49p1 : gamma0CuspForms 294 :=
  etaQuotientCuspForm 294 sparse![294; 0 => 1, 1 => -1, 5 => 1, 6 => -1, 13 => 2, 20 => 1, 48 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_294_eta_1p1_2m1_6p1_7m1_14p2_21p1_49p1_first_coeffs :
    first_coeffs 100 cuspForm_294_eta_1p1_2m1_6p1_7m1_14p2_21p1_49p1 =
    [0, 0, 0, 0, 1, -1, 0, -1, 1, -1, 0, 1, 1, -1, 0, 0, 0, -1, 1, 1,
     1, -1, 0, -1, 1, -1, 0, 0, 1, -2, 0, 0, 0, -1, 1, 1, 0, -1, 1, -1,
     0, 0, 0, 1, 1, -1, -1, 1, 0, 0, 0, 3, 1, -3, 0, 1, 0, -1, 1, 2,
     -2, -3, -1, 2, -1, 1, -1, 0, 0, -2, 1, 1, 2, -2, -1, 1, -1, -2, 2, 2,
     -2, 1, 1, -1, 1, -1, 1, 0, 0, 2, 0, 3, -1, -3, -1, 2, -3, 1, 1, 1] := by
  eta_coeff

end WeightTwoCusps
