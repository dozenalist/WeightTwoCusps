module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 392

The eta expression is `η(4z)^2 η(7z)^(-1) η(8z)^(-1) η(14z)^2 η(28z)^2 η(49z)^(-1) η(56z)^(-1) η(98z)^2`; see
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

/-- The cuspidal eta quotient `η(4z)^2 η(7z)^(-1) η(8z)^(-1) η(14z)^2 η(28z)^2 η(49z)^(-1) η(56z)^(-1) η(98z)^2` at level 392. -/
abbrev cuspForm_392_eta_4p2_7m1_8m1_14p2_28p2_49m1_56m1_98p2 : gamma0CuspForms 392 :=
  etaQuotientCuspForm 392 sparse![392; 3 => 2, 6 => -1, 7 => -1, 13 => 2, 27 => 2, 48 => -1, 55 => -1, 97 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_392_eta_4p2_7m1_8m1_14p2_28p2_49m1_56m1_98p2_first_coeffs :
    first_coeffs 100 cuspForm_392_eta_4p2_7m1_8m1_14p2_28p2_49m1_56m1_98p2 =
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, -2, 0,
     0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 2, 0, -2, 0, 0, -2, 0, 0, 0, 4,
     0, 0, -2, -2, 2, 0, 4, 0, 0, 1, -2, -4, 0, -2, 0, 0, -1, 0, -4, 0,
     2, 0, 0, 1, -2, 2, 0, -2, 0, 0, 0, 6, -2, 0, 0, 0, 0, 0, 6, 2,
     0, 0, 0, 0, -2, -2, 0, 0, 4, 0, 0, -2, 4, 0, 0, 4, 0, 0, 1, -6] := by
  eta_coeff

end WeightTwoCusps
