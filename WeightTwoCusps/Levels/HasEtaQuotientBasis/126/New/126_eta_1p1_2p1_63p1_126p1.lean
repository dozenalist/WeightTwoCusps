module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 126

The eta expression is `η(z) η(2z) η(63z) η(126z)`; see
[the local level table](../../TABLE.md#level-126).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(2z) η(63z) η(126z)` at level 126. -/
abbrev cuspForm_126_eta_1p1_2p1_63p1_126p1 : gamma0CuspForms 126 :=
  etaQuotientCuspForm 126 sparse![126; 0 => 1, 1 => 1, 62 => 1, 125 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_126_eta_1p1_2p1_63p1_126p1_first_coeffs :
    first_coeffs 100 cuspForm_126_eta_1p1_2p1_63p1_126p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -2, 1, 0, 2, 1, 0, 0, -2, 1, -2,
     -2, 0, 2, -1, 0, 2, 0, 2, 0, 1, 0, 0, -2, 0, 0, 0, -1, -2, -2, 0,
     2, 0, 0, -2, 3, 0, 0, 2, 0, 0, 2, 0, 2, -1, -2, 0, 0, 0, -2, 2,
     0, -2, -2, -1, -2, 2, 0, 0, 0, 0, 0, -1, 1, 4, 0, 0, -2, -1, 0, 2,
     4, -1, 4, 0, 0, -4, 2, 0, -4, 0, 0, 0, -3, 0, 0, -2, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
