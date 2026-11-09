module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 42

The eta expression is `η(z)^(-2) η(2z)^4 η(3z) η(6z)^(-1) η(7z)^4 η(14z)^(-2) η(21z)^(-1) η(42z)`; see
[the local level table](../../TABLE.md#level-42).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z) η(6z)^(-1) η(7z)^4 η(14z)^(-2) η(21z)^(-1) η(42z)` at level 42. -/
abbrev cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1 : gamma0CuspForms 42 :=
  etaQuotientCuspForm 42 sparse![42; 0 => -2, 1 => 4, 2 => 1, 5 => -1, 6 => 4, 13 => -2, 20 => -1, 41 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_first_coeffs :
    first_coeffs 100 cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1 =
    [0, 1, 2, 1, 1, 0, -1, 1, -4, -8, -6, -6, 1, 2, -4, 3, 7, 12, 11, -4,
     0, 4, 6, 6, -7, -5, 4, 7, 1, -6, -3, -4, 2, 0, -18, 0, -8, -10, 4, -13,
     6, 0, -4, 8, -6, 0, 6, -12, 7, 1, 2, 18, 2, 6, -7, 12, 2, 5, 0, -12,
     3, 14, 4, -8, -11, -12, 12, -4, 12, -6, 6, 6, 5, 14, 4, -11, -4, 6, 1, 20,
     -12, 7, -6, 0, 4, -12, -20, -12, -18, 0, -6, -10, 6, -10, 12, 12, -1, -34, 2, -6] := by
  eta_coeff

end WeightTwoCusps
