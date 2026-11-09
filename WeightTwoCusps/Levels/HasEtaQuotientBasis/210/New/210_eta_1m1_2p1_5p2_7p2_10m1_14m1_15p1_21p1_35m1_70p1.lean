module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 210

The eta expression is `η(z)^(-1) η(2z) η(5z)^2 η(7z)^2 η(10z)^(-1) η(14z)^(-1) η(15z) η(21z) η(35z)^(-1) η(70z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(5z)^2 η(7z)^2 η(10z)^(-1) η(14z)^(-1) η(15z) η(21z) η(35z)^(-1) η(70z)` at level 210. -/
abbrev cuspForm_210_eta_1m1_2p1_5p2_7p2_10m1_14m1_15p1_21p1_35m1_70p1 : gamma0CuspForms 210 :=
  etaQuotientCuspForm 210 sparse![210; 0 => -1, 1 => 1, 4 => 2, 6 => 2, 9 => -1, 13 => -1, 14 => 1, 20 => 1, 34 => -1, 69 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m1_2p1_5p2_7p2_10m1_14m1_15p1_21p1_35m1_70p1_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m1_2p1_5p2_7p2_10m1_14m1_15p1_21p1_35m1_70p1 =
    [0, 0, 0, 1, 1, 1, 2, 2, 1, 2, 1, 0, 2, 0, 0, 3, 2, 0, 2, -1,
     -1, 0, -2, -1, -1, -1, -1, -2, -2, 0, -5, -3, 0, -4, 1, -1, -7, -4, 1, -5,
     0, 3, 0, 4, 2, -1, -3, 1, -7, -4, -1, 3, 1, -1, -2, -3, 1, -5, -2, -4,
     2, 4, -1, -2, -1, -1, -4, 2, -5, 5, 1, -6, -1, 3, 0, -2, -1, -1, 15, 4,
     4, 0, 1, -2, 3, 1, 0, 4, 0, 1, 3, 3, -1, -1, -2, 3, 12, 6, 2, 2] := by
  eta_coeff

end WeightTwoCusps
