module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 312

The eta expression is `η(z) η(24z) η(39z) η(104z)`; see
[the local level table](../../TABLE.md#level-312).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(24z) η(39z) η(104z)` at level 312. -/
abbrev cuspForm_312_eta_1p1_24p1_39p1_104p1 : gamma0CuspForms 312 :=
  etaQuotientCuspForm 312 sparse![312; 0 => 1, 23 => 1, 38 => 1, 103 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_312_eta_1p1_24p1_39p1_104p1_first_coeffs :
    first_coeffs 100 cuspForm_312_eta_1p1_24p1_39p1_104p1 =
    [0, 0, 0, 0, 0, 0, 0, 1, -1, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, -1,
     0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, -1, 1, 2, 0, 0, -1, 0, -1, 0,
     0, 0, -1, 1, 0, 0, 0, 0, 1, 0, 0, -1, 0, -2, 0, -1, 1, 0, 2, 0,
     -1, 1, -1, 0, 1, 0, 1, 1, -1, 0, 2, 0, -2, 0, 0, 1, 0, -1, 0, 0,
     0, 0, -2, 0, -1, -2, 2, 1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2] := by
  eta_coeff

end WeightTwoCusps
