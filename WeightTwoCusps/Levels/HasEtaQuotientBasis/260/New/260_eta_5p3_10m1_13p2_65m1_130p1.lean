module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 260

The eta expression is `η(5z)^3 η(10z)^(-1) η(13z)^2 η(65z)^(-1) η(130z)`; see
[the local level table](../../TABLE.md#level-260).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(5z)^3 η(10z)^(-1) η(13z)^2 η(65z)^(-1) η(130z)` at level 260. -/
abbrev cuspForm_260_eta_5p3_10m1_13p2_65m1_130p1 : gamma0CuspForms 260 :=
  etaQuotientCuspForm 260 sparse![260; 4 => 3, 9 => -1, 12 => 2, 64 => -1, 129 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_260_eta_5p3_10m1_13p2_65m1_130p1_first_coeffs :
    first_coeffs 100 cuspForm_260_eta_5p3_10m1_13p2_65m1_130p1 =
    [0, 0, 0, 0, 1, 0, 0, 0, 0, -3, 0, 0, 0, 0, 1, 0, 0, -2, 0, 2,
     0, 0, 6, 0, 2, 0, 0, -2, 0, -1, -1, 0, -4, 0, -4, 3, 0, -4, 0, 1,
     -1, 0, 2, 2, -2, -2, 0, 8, -6, 0, -2, 0, -2, 2, 2, 1, 1, 4, 4, 4,
     4, -3, 0, 4, -1, -1, 1, -4, -2, 5, 2, 2, -8, -8, -11, 0, 2, 2, 2, 2,
     -2, -1, -8, -4, 6, -4, -4, 16, 0, 4, 1, 1, -2, 4, -5, -3, -2, -8, 8, -14] := by
  eta_coeff

end WeightTwoCusps
