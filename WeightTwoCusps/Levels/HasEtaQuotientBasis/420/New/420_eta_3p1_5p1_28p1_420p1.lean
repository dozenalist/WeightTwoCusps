module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(3z) η(5z) η(28z) η(420z)`; see
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

/-- The cuspidal eta quotient `η(3z) η(5z) η(28z) η(420z)` at level 420. -/
abbrev cuspForm_420_eta_3p1_5p1_28p1_420p1 : gamma0CuspForms 420 :=
  etaQuotientCuspForm 420 sparse![420; 2 => 1, 4 => 1, 27 => 1, 419 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_420_eta_3p1_5p1_28p1_420p1_first_coeffs :
    first_coeffs 100 cuspForm_420_eta_3p1_5p1_28p1_420p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
     0, 0, -1, 0, -1, -1, 0, 1, 0, -1, 1, 0, 1, 0, 1, 1, 0, 0, 0, -1,
     1, 0, 0, 0, 0, -1, 0, -2, 0, 0, -1, 0, 1, 1, 1, -2, 0, 0, -1, 1,
     -1, 0, -1, -1, -1, 2, 0, 1, -1, 2, 0, 0, 0, 1, 1, 1, 0, 0, 3, -1,
     0, 1, 0, 0, 0, 4, -1, -1, -1, -1, -3, -1, 1, -2, -2, 0, -1, 0, 0, -1] := by
  eta_coeff

end WeightTwoCusps
