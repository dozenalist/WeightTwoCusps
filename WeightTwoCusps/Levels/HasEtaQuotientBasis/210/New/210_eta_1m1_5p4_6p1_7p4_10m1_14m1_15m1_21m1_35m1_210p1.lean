module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 210

The eta expression is `η(z)^(-1) η(5z)^4 η(6z) η(7z)^4 η(10z)^(-1) η(14z)^(-1) η(15z)^(-1) η(21z)^(-1) η(35z)^(-1) η(210z)`; see
[the local level table](../../TABLE.md#level-210).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(5z)^4 η(6z) η(7z)^4 η(10z)^(-1) η(14z)^(-1) η(15z)^(-1) η(21z)^(-1) η(35z)^(-1) η(210z)` at level 210. -/
abbrev cuspForm_210_eta_1m1_5p4_6p1_7p4_10m1_14m1_15m1_21m1_35m1_210p1 : gamma0CuspForms 210 :=
  etaQuotientCuspForm 210 sparse![210; 0 => -1, 4 => 4, 5 => 1, 6 => 4, 9 => -1, 13 => -1, 14 => -1, 20 => -1, 34 => -1, 209 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m1_5p4_6p1_7p4_10m1_14m1_15m1_21m1_35m1_210p1_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m1_5p4_6p1_7p4_10m1_14m1_15m1_21m1_35m1_210p1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 3, 5, 3, 6, 2, 4, -1, 0, -8, 3,
     -10, -3, -8, 1, -13, -1, -15, 1, -7, -7, -7, 7, -2, -8, -3, 1, 4, -14, 3, 5,
     8, -7, 0, 8, 16, -2, 5, 27, 18, 6, 1, 15, 5, -9, 8, 7, 9, 7, 4, -8,
     15, -26, 5, 3, -8, 0, 20, -10, -7, -15, 5, 2, -23, 1, 20, -7, 7, -7, 19, 15,
     -3, -7, 25, -2, -8, -28, -2, 0, -24, 9, -13, -10, 9, -9, -36, 15, -26, -10, -12, -9] := by
  eta_coeff

end WeightTwoCusps
