module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 68

The eta expression is `η(2z)^2 η(34z)^2`; see
[the local level table](../../TABLE.md#level-68).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^2 η(34z)^2` at level 68. -/
abbrev cuspForm_68_eta_2p2_34p2 : gamma0CuspForms 68 :=
  etaQuotientCuspForm 68 sparse![68; 1 => 2, 33 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_68_eta_2p2_34p2_first_coeffs :
    first_coeffs 100 cuspForm_68_eta_2p2_34p2 =
    [0, 0, 0, 1, 0, -2, 0, -1, 0, 2, 0, 1, 0, 2, 0, -2, 0, 0, 0, -2,
     0, -2, 0, 1, 0, 0, 0, 0, 0, 2, 0, 3, 0, -2, 0, 2, 0, -2, 0, 4,
     0, 0, 0, -6, 0, -2, 0, -4, 0, 2, 0, -1, 0, 4, 0, 6, 0, 0, 0, -2,
     0, 2, 0, -3, 0, -4, 0, 4, 0, -2, 0, -3, 0, 0, 0, 7, 0, 2, 0, -3,
     0, -2, 0, 2, 0, 2, 0, 2, 0, -2, 0, -4, 0, 2, 0, -4, 0, -4, 0, -5] := by
  eta_coeff

end WeightTwoCusps
