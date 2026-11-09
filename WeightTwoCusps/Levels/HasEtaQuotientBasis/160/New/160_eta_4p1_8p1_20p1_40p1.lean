module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 160

The eta expression is `η(4z) η(8z) η(20z) η(40z)`; see
[the local level table](../../TABLE.md#level-160).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z) η(8z) η(20z) η(40z)` at level 160. -/
abbrev cuspForm_160_eta_4p1_8p1_20p1_40p1 : gamma0CuspForms 160 :=
  etaQuotientCuspForm 160 sparse![160; 3 => 1, 7 => 1, 19 => 1, 39 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_160_eta_4p1_8p1_20p1_40p1_first_coeffs :
    first_coeffs 100 cuspForm_160_eta_4p1_8p1_20p1_40p1 =
    [0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -2, 0, 0, 0, 1, 0, 0, 0, 0,
     0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, -1, 0, 0, 0, -2,
     0, 0, 0, -3, 0, 0, 0, -1, 0, 0, 0, 2, 0, 0, 0, -2, 0, 0, 0, 4,
     0, 0, 0, -5, 0, 0, 0, -1, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 4,
     0, 0, 0, 1, 0, 0, 0, 6, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, -10] := by
  eta_coeff

end WeightTwoCusps
