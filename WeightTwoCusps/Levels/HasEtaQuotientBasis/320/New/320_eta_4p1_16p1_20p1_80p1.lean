module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 320

The eta expression is `η(4z) η(16z) η(20z) η(80z)`; see
[the local level table](../../TABLE.md#level-320).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z) η(16z) η(20z) η(80z)` at level 320. -/
abbrev cuspForm_320_eta_4p1_16p1_20p1_80p1 : gamma0CuspForms 320 :=
  etaQuotientCuspForm 320 sparse![320; 3 => 1, 15 => 1, 19 => 1, 79 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_320_eta_4p1_16p1_20p1_80p1_first_coeffs :
    first_coeffs 100 cuspForm_320_eta_4p1_16p1_20p1_80p1 =
    [0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0,
     0, -1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, -1, 0, 0,
     0, 1, 0, 0, 0, -2, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0,
     0, 1, 0, 0, 0, -5, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0,
     0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0] := by
  eta_coeff

end WeightTwoCusps
