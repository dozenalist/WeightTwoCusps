module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 312

The eta expression is `η(2z) η(4z)^(-1) η(12z) η(24z) η(26z)^(-1) η(52z)^2 η(104z)`; see
[the local level table](../../TABLE.md#level-312).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(4z)^(-1) η(12z) η(24z) η(26z)^(-1) η(52z)^2 η(104z)` at level 312. -/
abbrev cuspForm_312_eta_2p1_4m1_12p1_24p1_26m1_52p2_104p1 : gamma0CuspForms 312 :=
  etaQuotientCuspForm 312 sparse![312; 1 => 1, 3 => -1, 11 => 1, 23 => 1, 25 => -1, 51 => 2, 103 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_312_eta_2p1_4m1_12p1_24p1_26m1_52p2_104p1_first_coeffs :
    first_coeffs 100 cuspForm_312_eta_2p1_4m1_12p1_24p1_26m1_52p2_104p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, -1, 0, 1, 0, -1,
     0, 0, 0, 0, 0, 2, 0, -1, 0, 1, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, -1,
     0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, -2, 0, -1, 0, 0, 0, -1,
     0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, -2, 0, -1] := by
  eta_coeff

end WeightTwoCusps
