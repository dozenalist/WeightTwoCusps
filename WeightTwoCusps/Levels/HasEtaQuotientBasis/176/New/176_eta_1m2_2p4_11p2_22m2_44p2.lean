module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 176

The eta expression is `η(z)^(-2) η(2z)^4 η(11z)^2 η(22z)^(-2) η(44z)^2`; see
[the local level table](../../TABLE.md#level-176).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(11z)^2 η(22z)^(-2) η(44z)^2` at level 176. -/
abbrev cuspForm_176_eta_1m2_2p4_11p2_22m2_44p2 : gamma0CuspForms 176 :=
  etaQuotientCuspForm 176 sparse![176; 0 => -2, 1 => 4, 10 => 2, 21 => -2, 43 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_176_eta_1m2_2p4_11p2_22m2_44p2_first_coeffs :
    first_coeffs 100 cuspForm_176_eta_1m2_2p4_11p2_22m2_44p2 =
    [0, 0, 0, 1, 2, 1, 2, 2, 0, 3, 2, 0, 2, 2, 0, -3, 0, -4, -2, 4,
     -6, -2, 0, -3, 0, -1, 0, -1, 4, -2, -6, 5, 0, 1, 4, -6, -4, -1, -4, -4,
     0, 2, -8, -6, -2, -8, 2, 0, 0, 4, -2, -2, -8, 4, 6, 1, 0, -8, 4, 3,
     -6, 2, 2, 4, 0, -8, -2, -1, 12, 3, 0, 7, 0, 6, -2, 8, 16, 2, 4, 2,
     0, 0, 0, 2, 4, 14, -4, -8, 0, 7, 8, 0, -6, 3, 8, -8, 0, 5, 8, 3] := by
  eta_coeff

end WeightTwoCusps
