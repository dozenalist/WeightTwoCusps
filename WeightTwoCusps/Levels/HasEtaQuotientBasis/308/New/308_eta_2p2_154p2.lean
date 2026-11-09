module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 308

The eta expression is `η(2z)^2 η(154z)^2`; see
[the local level table](../../TABLE.md#level-308).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^2 η(154z)^2` at level 308. -/
abbrev cuspForm_308_eta_2p2_154p2 : gamma0CuspForms 308 :=
  etaQuotientCuspForm 308 sparse![308; 1 => 2, 153 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_308_eta_2p2_154p2_first_coeffs :
    first_coeffs 100 cuspForm_308_eta_2p2_154p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -2, 0, -1, 0, 2,
     0, 1, 0, 2, 0, -2, 0, 0, 0, -2, 0, -2, 0, 1, 0, 0, 0, 0, 0, 2,
     0, 3, 0, -2, 0, 2, 0, 0, 0, 0, 0, -2, 0, -2, 0, 0, 0, 0, 0, -2,
     0, -1, 0, 0, 0, 2, 0, 2, 0, -2, 0, 2, 0, 1, 0, 2, 0, 0, 0, 2,
     0, -2, 0, -2, 0, 2, 0, 0, 0, -2, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
