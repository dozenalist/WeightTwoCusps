module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 352

The eta expression is `η(2z) η(16z) η(22z) η(176z)`; see
[the local level table](../../TABLE.md#level-352).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(16z) η(22z) η(176z)` at level 352. -/
abbrev cuspForm_352_eta_2p1_16p1_22p1_176p1 : gamma0CuspForms 352 :=
  etaQuotientCuspForm 352 sparse![352; 1 => 1, 15 => 1, 21 => 1, 175 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_352_eta_2p1_16p1_22p1_176p1_first_coeffs :
    first_coeffs 100 cuspForm_352_eta_2p1_16p1_22p1_176p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1,
     0, 0, 0, 1, 0, -1, 0, 1, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, -2,
     0, -2, 0, 1, 0, 0, 0, 1, 0, 0, 0, -2, 0, 0, 0, 2, 0, 2, 0, 0,
     0, 3, 0, 0, 0, 0, 0, -2, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0,
     0, 0, 0, 1, 0, 0, 0, -2, 0, -1, 0, 0, 0, -4, 0, 2, 0, -1, 0, 2] := by
  eta_coeff

end WeightTwoCusps
