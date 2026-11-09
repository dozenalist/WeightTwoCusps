module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 100

The eta expression is `η(2z) η(10z)^2 η(50z)`; see
[the local level table](../../TABLE.md#level-100).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(10z)^2 η(50z)` at level 100. -/
abbrev cuspForm_100_eta_2p1_10p2_50p1 : gamma0CuspForms 100 :=
  etaQuotientCuspForm 100 sparse![100; 1 => 1, 9 => 2, 49 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_100_eta_2p1_10p2_50p1_first_coeffs :
    first_coeffs 100 cuspForm_100_eta_2p1_10p2_50p1 =
    [0, 0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, -1, 0, 2, 0, 3, 0, 0,
     0, 0, 0, -3, 0, 1, 0, -2, 0, 0, 0, 0, 0, 0, 0, -2, 0, -1, 0, 0,
     0, 0, 0, 5, 0, -1, 0, 3, 0, 0, 0, 0, 0, 3, 0, 0, 0, -4, 0, 0,
     0, 0, 0, -1, 0, -2, 0, -1, 0, 0, 0, 0, 0, -1, 0, -2, 0, 0, 0, 0,
     0, 0, 0, -3, 0, 6, 0, 6, 0, 0, 0, 0, 0, -4, 0, 4, 0, -1, 0, 0] := by
  eta_coeff

end WeightTwoCusps
