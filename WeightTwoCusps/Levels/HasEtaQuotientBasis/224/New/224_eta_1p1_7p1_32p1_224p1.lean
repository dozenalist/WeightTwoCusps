module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 224

The eta expression is `η(z) η(7z) η(32z) η(224z)`; see
[the local level table](../../TABLE.md#level-224).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(7z) η(32z) η(224z)` at level 224. -/
abbrev cuspForm_224_eta_1p1_7p1_32p1_224p1 : gamma0CuspForms 224 :=
  etaQuotientCuspForm 224 sparse![224; 0 => 1, 6 => 1, 31 => 1, 223 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_224_eta_1p1_7p1_32p1_224p1_first_coeffs :
    first_coeffs 100 cuspForm_224_eta_1p1_7p1_32p1_224p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, 0, 0, 1, 0, 0, 1,
     1, 0, 0, -2, 0, -2, 0, 1, 0, 0, 0, 0, -1, 2, 0, 0, 0, 2, 0, 0,
     0, 0, 0, -1, 0, 1, 0, -2, -2, 0, 0, -2, -1, 2, 0, 2, 0, 2, 0, -1,
     2, -2, 0, 0, 1, 0, 0, 1, 2, -3, 0, 0, 0, 0, 0, -3, 1, 1, 0, 2,
     0, -2, 0, 0, -1, -2, 0, 2, 0, 2, 0, -1, -2, 2, 0, 0, 2, -2, 0, -1] := by
  eta_coeff

end WeightTwoCusps
