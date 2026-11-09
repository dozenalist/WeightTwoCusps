module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 108

The eta expression is `η(2z)^3 η(18z)`; see
[the local level table](../../TABLE.md#level-108).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^3 η(18z)` at level 108. -/
abbrev cuspForm_108_eta_2p3_18p1 : gamma0CuspForms 108 :=
  etaQuotientCuspForm 108 sparse![108; 1 => 3, 17 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_108_eta_2p3_18p1_first_coeffs :
    first_coeffs 100 cuspForm_108_eta_2p3_18p1 =
    [0, 1, 0, -3, 0, 0, 0, 5, 0, 0, 0, 0, 0, -7, 0, 0, 0, 0, 0, -1,
     0, 12, 0, 0, 0, -5, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, -1, 0, -6,
     0, 0, 0, 8, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, -24, 0, 0,
     0, -13, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 17, 0, 15, 0, 0, 0, -13,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -35, 0, 12, 0, 0, 0, 5, 0, 0] := by
  eta_coeff

end WeightTwoCusps
