module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 336

The eta expression is `η(6z) η(14z)^2 η(24z) η(28z) η(42z)^(-1) η(56z)^(-1) η(84z)`; see
[the local level table](../../TABLE.md#level-336).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(6z) η(14z)^2 η(24z) η(28z) η(42z)^(-1) η(56z)^(-1) η(84z)` at level 336. -/
abbrev cuspForm_336_eta_6p1_14p2_24p1_28p1_42m1_56m1_84p1 : gamma0CuspForms 336 :=
  etaQuotientCuspForm 336 sparse![336; 5 => 1, 13 => 2, 23 => 1, 27 => 1, 41 => -1, 55 => -1, 83 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_336_eta_6p1_14p2_24p1_28p1_42m1_56m1_84p1_first_coeffs :
    first_coeffs 100 cuspForm_336_eta_6p1_14p2_24p1_28p1_42m1_56m1_84p1 =
    [0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, -2, 0, 0,
     0, 0, 0, 2, 0, 0, 0, -1, 0, 2, 0, -2, 0, 2, 0, 0, 0, 2, 0, 1,
     0, 2, 0, 2, 0, 6, 0, -4, 0, 0, 0, -6, 0, -2, 0, 2, 0, -5, 0, -2,
     0, -4, 0, 1, 0, 2, 0, -2, 0, -6, 0, 0, 0, -4, 0, 9, 0, -2, 0, 4,
     0, 4, 0, 2, 0, 2, 0, 6, 0, 2, 0, -2, 0, -8, 0, 2, 0, 4, 0, 0] := by
  eta_coeff

end WeightTwoCusps
