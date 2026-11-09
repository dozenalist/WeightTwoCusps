module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 228

The eta expression is `η(6z)^3 η(12z)^(-1) η(19z)^(-1) η(57z)^3 η(76z) η(114z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(6z)^3 η(12z)^(-1) η(19z)^(-1) η(57z)^3 η(76z) η(114z)^(-1)` at level 228. -/
abbrev cuspForm_228_eta_6p3_12m1_19m1_57p3_76p1_114m1 : gamma0CuspForms 228 :=
  etaQuotientCuspForm 228 sparse![228; 5 => 3, 11 => -1, 18 => -1, 56 => 3, 75 => 1, 113 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_228_eta_6p3_12m1_19m1_57p3_76p1_114m1_first_coeffs :
    first_coeffs 100 cuspForm_228_eta_6p3_12m1_19m1_57p3_76p1_114m1 =
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 1, 0, 0,
     0, 0, 0, 2, 1, 0, 0, 0, 0, 2, -3, 0, 0, 0, 0, -1, 1, 0, 0, 0,
     0, -4, 2, 2, 0, 0, 0, 1, 2, -6, 0, 0, 0, -2, -1, 2, 0, 0, 0, 0,
     -4, 4, 0, 0, 0, 2, 1, 4, 0, 0, 0, 4, -2, -2, 0, 0, 0, -1, 0, -8,
     0, 1, 0, 2, 2, 2, 0, -3, 0, -2, 4, -4, 0, 1, 0, -1, -1, 0, 0, 2] := by
  eta_coeff

end WeightTwoCusps
