module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 110

The eta expression is `η(2z) η(5z)^(-1) η(10z)^2 η(11z)^2 η(22z)^(-1) η(55z)`; see
[the local level table](../../TABLE.md#level-110).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(5z)^(-1) η(10z)^2 η(11z)^2 η(22z)^(-1) η(55z)` at level 110. -/
abbrev cuspForm_110_eta_2p1_5m1_10p2_11p2_22m1_55p1 : gamma0CuspForms 110 :=
  etaQuotientCuspForm 110 sparse![110; 1 => 1, 4 => -1, 9 => 2, 10 => 2, 21 => -1, 54 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_110_eta_2p1_5m1_10p2_11p2_22m1_55p1_first_coeffs :
    first_coeffs 100 cuspForm_110_eta_2p1_5m1_10p2_11p2_22m1_55p1 =
    [0, 0, 0, 1, 0, -1, 0, -1, 1, 0, -1, 0, -1, 1, -2, 0, 2, 1, 4, -2,
     -1, 2, 0, 2, -2, 0, 0, -1, -1, -4, 0, 2, 0, 0, 0, -1, 0, -1, 1, -2,
     0, 0, -1, 1, 0, 0, 2, 4, 1, 0, 0, -2, 3, 3, -4, 0, -2, 0, -5, 2,
     2, 2, 6, -3, -4, 1, 0, 2, 3, 2, 1, -6, 1, -7, 2, 1, -2, 0, -4, 0,
     -1, -4, -2, -1, 6, 1, -4, 2, -1, 0, 1, 6, 0, 1, 6, 0, 0, 4, -2, 2] := by
  eta_coeff

end WeightTwoCusps
