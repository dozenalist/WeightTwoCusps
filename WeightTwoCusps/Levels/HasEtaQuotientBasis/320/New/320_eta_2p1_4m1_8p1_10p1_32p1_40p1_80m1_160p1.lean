module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 320

The eta expression is `η(2z) η(4z)^(-1) η(8z) η(10z) η(32z) η(40z) η(80z)^(-1) η(160z)`; see
[the local level table](../../TABLE.md#level-320).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(4z)^(-1) η(8z) η(10z) η(32z) η(40z) η(80z)^(-1) η(160z)` at level 320. -/
abbrev cuspForm_320_eta_2p1_4m1_8p1_10p1_32p1_40p1_80m1_160p1 : gamma0CuspForms 320 :=
  etaQuotientCuspForm 320 sparse![320; 1 => 1, 3 => -1, 7 => 1, 9 => 1, 31 => 1, 39 => 1, 79 => -1, 159 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_320_eta_2p1_4m1_8p1_10p1_32p1_40p1_80m1_160p1_first_coeffs :
    first_coeffs 100 cuspForm_320_eta_2p1_4m1_8p1_10p1_32p1_40p1_80m1_160p1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 2,
     0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -2, 0, -2,
     0, 1, 0, 0, 0, 1, 0, -1, 0, 1, 0, -2, 0, 1, 0, -1, 0, 3, 0, -2,
     0, 0, 0, -1, 0, -1, 0, 0, 0, 4, 0, 0, 0, -1, 0, 0, 0, 5, 0, 2,
     0, 1, 0, -4, 0, -1, 0, -2, 0, -2, 0, 2, 0, 0, 0, 1, 0, -3, 0, -2] := by
  eta_coeff

end WeightTwoCusps
