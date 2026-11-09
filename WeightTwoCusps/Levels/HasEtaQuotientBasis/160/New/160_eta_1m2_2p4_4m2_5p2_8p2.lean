module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 160

The eta expression is `η(z)^(-2) η(2z)^4 η(4z)^(-2) η(5z)^2 η(8z)^2`; see
[the local level table](../../TABLE.md#level-160).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(4z)^(-2) η(5z)^2 η(8z)^2` at level 160. -/
abbrev cuspForm_160_eta_1m2_2p4_4m2_5p2_8p2 : gamma0CuspForms 160 :=
  etaQuotientCuspForm 160 sparse![160; 0 => -2, 1 => 4, 3 => -2, 4 => 2, 7 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_160_eta_1m2_2p4_4m2_5p2_8p2_first_coeffs :
    first_coeffs 100 cuspForm_160_eta_1m2_2p4_4m2_5p2_8p2 =
    [0, 1, 2, 1, 2, 4, 2, 1, 4, 3, 0, 2, 0, 0, 2, -1, 0, 2, -2, -4,
     2, -6, -4, 3, -8, -7, 0, -2, -8, 2, -2, -2, 0, -12, -4, -1, -6, -8, 0, -6,
     -4, 4, -4, 1, 8, -6, -10, 1, 0, -1, 2, 2, -4, 8, -4, -2, 8, 0, 4, 0,
     0, -4, 12, 1, 0, 18, 0, 3, 4, 6, 6, 6, 4, -6, 8, 1, 8, 12, 4, 4,
     0, 3, 0, 5, 0, 8, 18, -2, 0, 10, -4, -6, 8, 12, 2, 4, 0, 6, 6, 2] := by
  eta_coeff

end WeightTwoCusps
