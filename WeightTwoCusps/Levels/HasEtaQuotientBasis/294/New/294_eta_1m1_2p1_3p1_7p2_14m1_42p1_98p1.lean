module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 294

The eta expression is `η(z)^(-1) η(2z) η(3z) η(7z)^2 η(14z)^(-1) η(42z) η(98z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z) η(7z)^2 η(14z)^(-1) η(42z) η(98z)` at level 294. -/
abbrev cuspForm_294_eta_1m1_2p1_3p1_7p2_14m1_42p1_98p1 : gamma0CuspForms 294 :=
  etaQuotientCuspForm 294 sparse![294; 0 => -1, 1 => 1, 2 => 1, 6 => 2, 13 => -1, 41 => 1, 97 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_294_eta_1m1_2p1_3p1_7p2_14m1_42p1_98p1_first_coeffs :
    first_coeffs 100 cuspForm_294_eta_1m1_2p1_3p1_7p2_14m1_42p1_98p1 =
    [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 1, 0, 0, 0, 1, 1, -1, 1,
     0, 1, 1, -1, 0, 0, 1, 0, -1, -1, 0, -1, 0, -1, 0, -1, 1, 0, -1, 1,
     -2, 1, 0, -2, 0, 0, -1, -1, -3, 0, -1, -2, -1, -4, -2, 0, 0, -2, -2, -1,
     0, 0, -1, -2, 0, 1, 0, 1, -2, -1, -1, 1, 0, -1, -1, 1, 1, 2, -1, -2,
     -1, -1, 2, -2, -1, 1, 1, 1, 1, 1, 1, -3, -1, -1, 0, 0, 1, -1, -1, 2] := by
  eta_coeff

end WeightTwoCusps
