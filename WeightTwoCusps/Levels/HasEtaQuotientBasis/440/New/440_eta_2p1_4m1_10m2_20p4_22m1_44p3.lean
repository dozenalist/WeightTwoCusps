module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 440

The eta expression is `η(2z) η(4z)^(-1) η(10z)^(-2) η(20z)^4 η(22z)^(-1) η(44z)^3`; see
[the local level table](../../TABLE.md#level-440).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(4z)^(-1) η(10z)^(-2) η(20z)^4 η(22z)^(-1) η(44z)^3` at level 440. -/
abbrev cuspForm_440_eta_2p1_4m1_10m2_20p4_22m1_44p3 : gamma0CuspForms 440 :=
  etaQuotientCuspForm 440 sparse![440; 1 => 1, 3 => -1, 9 => -2, 19 => 4, 21 => -1, 43 => 3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_440_eta_2p1_4m1_10m2_20p4_22m1_44p3_first_coeffs :
    first_coeffs 100 cuspForm_440_eta_2p1_4m1_10m2_20p4_22m1_44p3 =
    [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, -1, 0, 1, 0, 1, 0, -1,
     0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 2, 0, 1,
     0, -1, 0, -2, 0, 0, 0, 1, 0, 1, 0, -3, 0, 2, 0, 0, 0, 1, 0, -1,
     0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, -2, 0, -1, 0, -1, 0, 0, 0, 0,
     0, -2, 0, 0, 0, 1, 0, 2, 0, 1, 0, -2, 0, 0, 0, -1, 0, 2, 0, 0] := by
  eta_coeff

end WeightTwoCusps
