module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 294

The eta expression is `η(z)^(-1) η(2z)^2 η(3z) η(6z)^(-1) η(7z)^4 η(14z)^(-2) η(21z)^(-1) η(42z) η(49z)^(-1) η(98z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(3z) η(6z)^(-1) η(7z)^4 η(14z)^(-2) η(21z)^(-1) η(42z) η(49z)^(-1) η(98z)^2` at level 294. -/
abbrev cuspForm_294_eta_1m1_2p2_3p1_6m1_7p4_14m2_21m1_42p1_49m1_98p2 : gamma0CuspForms 294 :=
  etaQuotientCuspForm 294 sparse![294; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 6 => 4, 13 => -2, 20 => -1, 41 => 1, 48 => -1, 97 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_294_eta_1m1_2p2_3p1_6m1_7p4_14m2_21m1_42p1_49m1_98p2_first_coeffs :
    first_coeffs 100 cuspForm_294_eta_1m1_2p2_3p1_6m1_7p4_14m2_21m1_42p1_49m1_98p2 =
    [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, 0, -4, -4, -2, 0, 4, 0,
     0, 4, 4, 7, 0, -4, 0, 0, 1, 1, -4, 0, 0, 0, 0, 0, 0, -6, 0, -4,
     0, 0, -4, -2, -1, 0, 8, 0, 0, 1, -7, 8, 0, 0, 0, 0, 2, 9, 2, 0,
     -1, 0, 0, -8, -2, -3, 0, 0, 0, 0, 6, 1, 7, 0, -1, 0, 0, 6, 1, 0,
     0, -4, 0, 0, 4, 2, -12, 0, -10, 0, 0, -10, -5, -13, 0, 16, 0, 0, 2, -7] := by
  eta_coeff

end WeightTwoCusps
