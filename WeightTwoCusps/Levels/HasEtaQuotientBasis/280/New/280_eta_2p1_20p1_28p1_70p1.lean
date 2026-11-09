module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 280

The eta expression is `η(2z) η(20z) η(28z) η(70z)`; see
[the local level table](../../TABLE.md#level-280).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(20z) η(28z) η(70z)` at level 280. -/
abbrev cuspForm_280_eta_2p1_20p1_28p1_70p1 : gamma0CuspForms 280 :=
  etaQuotientCuspForm 280 sparse![280; 1 => 1, 19 => 1, 27 => 1, 69 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_280_eta_2p1_20p1_28p1_70p1_first_coeffs :
    first_coeffs 100 cuspForm_280_eta_2p1_20p1_28p1_70p1 =
    [0, 0, 0, 0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1,
     0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0, 0, -1, 0, -1, 0, 1, 0, -1,
     0, 0, 0, -1, 0, -1, 0, 0, 0, 3, 0, 0, 0, 1, 0, -1, 0, 1, 0, -1,
     0, -1, 0, 3, 0, 1, 0, 1, 0, 0, 0, -1, 0, 1, 0, -3, 0, -3, 0, 1,
     0, 1, 0, -1, 0, -3, 0, 1, 0, -2, 0, 2, 0, 0, 0, 3, 0, -2, 0, 0] := by
  eta_coeff

end WeightTwoCusps
