module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(z)^(-1) η(2z) η(3z) η(7z) η(15z) η(70z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z) η(7z) η(15z) η(70z)` at level 420. -/
abbrev cuspForm_420_eta_1m1_2p1_3p1_7p1_15p1_70p1 : gamma0CuspForms 420 :=
  etaQuotientCuspForm 420 sparse![420; 0 => -1, 1 => 1, 2 => 1, 6 => 1, 14 => 1, 69 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_420_eta_1m1_2p1_3p1_7p1_15p1_70p1_first_coeffs :
    first_coeffs 100 cuspForm_420_eta_1m1_2p1_3p1_7p1_15p1_70p1 =
    [0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1,
     1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, -1,
     0, 0, 0, 0, 0, -2, -1, 0, 1, -1, -1, 0, -2, 1, -2, -1, -1, 0, -1, -1,
     -1, -1, -2, 1, -1, -2, 0, -2, -1, -2, -1, -2, -2, -2, -2, -2, -3, -3, -4, -4,
     -2, -1, 1, -1, -4, -3, -1, -5, -1, -4, -3, -2, 0, -1, -2, -2, -3, -1, -5, -2] := by
  eta_coeff

end WeightTwoCusps
