module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 392

The eta expression is `η(7z) η(8z) η(49z) η(56z)`; see
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

/-- The cuspidal eta quotient `η(7z) η(8z) η(49z) η(56z)` at level 392. -/
abbrev cuspForm_392_eta_7p1_8p1_49p1_56p1 : gamma0CuspForms 392 :=
  etaQuotientCuspForm 392 sparse![392; 6 => 1, 7 => 1, 48 => 1, 55 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_392_eta_7p1_8p1_49p1_56p1_first_coeffs :
    first_coeffs 100 cuspForm_392_eta_7p1_8p1_49p1_56p1 =
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, -1,
     1, -1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, -1,
     0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0,
     1, 0, 0, -1, -2, 0, 0, 0, 0, -2, 0, -1, 0, 0, 0, 0, 0, 2, 0, 0] := by
  eta_coeff

end WeightTwoCusps
