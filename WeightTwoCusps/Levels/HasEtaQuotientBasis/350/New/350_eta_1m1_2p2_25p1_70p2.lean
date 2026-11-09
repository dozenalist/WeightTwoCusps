module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 350

The eta expression is `η(z)^(-1) η(2z)^2 η(25z) η(70z)^2`; see
[the local level table](../../TABLE.md#level-350).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(25z) η(70z)^2` at level 350. -/
abbrev cuspForm_350_eta_1m1_2p2_25p1_70p2 : gamma0CuspForms 350 :=
  etaQuotientCuspForm 350 sparse![350; 0 => -1, 1 => 2, 24 => 1, 69 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_350_eta_1m1_2p2_25p1_70p2_first_coeffs :
    first_coeffs 100 cuspForm_350_eta_1m1_2p2_25p1_70p2 =
    [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0,
     0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, -1, 0, 0, 0, 0, -1, 0,
     0, 0, -1, 1, 0, 0, 0, -1, 0, 0, 0, 0, 1, -1, 0, 0, 0, -1, -1, 0,
     -2, 0, 1, -1, 0, 0, 0, -1, -1, 0, 0, 0, -1, 1, 0, 0, 0, -3, -3, 0,
     -2, 0, 0, -2, 0, 0, 0, -3, 0, 0, 0, 0, -2, -1, 0, 0, 0, 0, -2, 0] := by
  eta_coeff

end WeightTwoCusps
