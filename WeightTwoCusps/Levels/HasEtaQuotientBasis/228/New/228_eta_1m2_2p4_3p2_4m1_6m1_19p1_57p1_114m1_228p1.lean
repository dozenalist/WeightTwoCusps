module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 228

The eta expression is `η(z)^(-2) η(2z)^4 η(3z)^2 η(4z)^(-1) η(6z)^(-1) η(19z) η(57z) η(114z)^(-1) η(228z)`; see
[the local level table](../../TABLE.md#level-228).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z)^2 η(4z)^(-1) η(6z)^(-1) η(19z) η(57z) η(114z)^(-1) η(228z)` at level 228. -/
abbrev cuspForm_228_eta_1m2_2p4_3p2_4m1_6m1_19p1_57p1_114m1_228p1 : gamma0CuspForms 228 :=
  etaQuotientCuspForm 228 sparse![228; 0 => -2, 1 => 4, 2 => 2, 3 => -1, 5 => -1, 18 => 1, 56 => 1, 113 => -1, 227 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_228_eta_1m2_2p4_3p2_4m1_6m1_19p1_57p1_114m1_228p1_first_coeffs :
    first_coeffs 100 cuspForm_228_eta_1m2_2p4_3p2_4m1_6m1_19p1_57p1_114m1_228p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, -1, 0, 0, -2, 0, -2, -1, 0,
     -2, 0, -3, 2, 2, -2, 0, -3, -2, -1, 2, 3, -1, 0, 4, 2, 2, 1, 1, 2,
     0, 3, -2, 0, 4, 2, 1, -2, -1, 0, -3, 1, 1, -2, -2, 0, 3, -1, 4, 0,
     2, -4, -4, 0, -4, 3, -4, -3, -4, 3, -1, -3, 0, -2, 4, -1, -1, -2, 1, 4,
     -2, -4, 0, -2, 1, 4, 5, -4, -4, 3, -1, 0, -2, 0, -3, -1, -2, -1, -2, 4] := by
  eta_coeff

end WeightTwoCusps
