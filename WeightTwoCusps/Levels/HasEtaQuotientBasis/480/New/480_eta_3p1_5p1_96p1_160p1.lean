module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(3z) η(5z) η(96z) η(160z)`; see
[the local level table](../../TABLE.md#level-480).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z) η(5z) η(96z) η(160z)` at level 480. -/
abbrev cuspForm_480_eta_3p1_5p1_96p1_160p1 : gamma0CuspForms 480 :=
  etaQuotientCuspForm 480 sparse![480; 2 => 1, 4 => 1, 95 => 1, 159 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_480_eta_3p1_5p1_96p1_160p1_first_coeffs :
    first_coeffs 100 cuspForm_480_eta_3p1_5p1_96p1_160p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, -1, -1, 0, 1,
     0, -1, 1, 0, 1, 0, 1, 1, 0, 0, 0, -1, 1, 0, 0, 0, 0, -1, 0, -1,
     0, 0, -2, 0, 0, 0, 1, -1, 0, -1, 0, 1, 0, 0, 0, 0, -1, 2, 0, 0,
     0, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, -1, -1, 0, 1, 0, 0, 2, 0, 0,
     0, -1, -2, 0, 0, 0, -2, -1, 0, 2, 0, -1, 0, 0, -1, 0, 0, 0, 0, -1] := by
  eta_coeff

end WeightTwoCusps
