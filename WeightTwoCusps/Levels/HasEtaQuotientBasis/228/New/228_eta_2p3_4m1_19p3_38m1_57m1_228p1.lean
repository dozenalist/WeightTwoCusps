module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 228

The eta expression is `η(2z)^3 η(4z)^(-1) η(19z)^3 η(38z)^(-1) η(57z)^(-1) η(228z)`; see
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

/-- The cuspidal eta quotient `η(2z)^3 η(4z)^(-1) η(19z)^3 η(38z)^(-1) η(57z)^(-1) η(228z)` at level 228. -/
abbrev cuspForm_228_eta_2p3_4m1_19p3_38m1_57m1_228p1 : gamma0CuspForms 228 :=
  etaQuotientCuspForm 228 sparse![228; 1 => 3, 3 => -1, 18 => 3, 37 => -1, 56 => -1, 227 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_228_eta_2p3_4m1_19p3_38m1_57m1_228p1_first_coeffs :
    first_coeffs 100 cuspForm_228_eta_2p3_4m1_19p3_38m1_57m1_228p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -3, 0, 1, 0, 2, 0, 2, 0, -1, 0,
     -4, 0, 1, 0, -2, 0, 0, -3, 2, 9, 4, -3, -1, -6, 2, -6, -2, 3, -1, 12,
     0, -3, -2, 6, -2, 0, -1, -6, -3, -12, 5, 3, 3, -6, 2, 6, 1, 3, -6, 0,
     6, 6, -2, 6, -2, 9, 2, -9, 4, -9, -5, 3, 0, 6, -2, -9, -1, -6, -3, -12,
     2, -6, -2, 6, -3, 6, 1, 12, 4, 9, 3, 12, 0, -6, 5, -3, 2, 9, 4, -18] := by
  eta_coeff

end WeightTwoCusps
