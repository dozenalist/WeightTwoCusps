module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«15».New.«15_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# The dilation-1 lift of 15.2.a.a to level 30

This is the function `f(z)`, with eta product `η(z)η(3z)η(5z)η(15z)`.
The original normalized newform is recorded at
https://www.lmfdb.org/ModularForm/GL2/Q/holomorphic/15/2/a/a/.
Its lift occurs in the cuspidal basis of
`M2_Gamma0_Eta_Quotient_Bases_N_1_to_500`; see
[the local level table](../../TABLE.md#level-30).
-/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The oldform `f(z)` at level 30, with source `15.2.a.a`. -/
abbrev cuspForm_15_2_a_a_old_30_1 : gamma0CuspForms 30 :=
  gamma0RescaleToLevel cuspForm_15_2_a_a 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta product. -/
theorem cuspForm_15_2_a_a_old_30_1_eq_eta :
    cuspForm_15_2_a_a_old_30_1 =
      etaQuotientCuspForm 30 sparse![30; 0 => 1, 2 => 1, 4 => 1, 14 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_15_2_a_a_old_30_1_first_coeffs : first_coeffs 100 cuspForm_15_2_a_a_old_30_1 =
    [0, 1, -1, -1, -1, 1, 1, 0, 3, 1, -1, -4, 1, -2, 0, -1, -1, 2, -1, 4,
     -1, 0, 4, 0, -3, 1, 2, -1, 0, -2, 1, 0, -5, 4, -2, 0, -1, -10, -4, 2,
     3, 10, 0, 4, 4, 1, 0, 8, 1, -7, -1, -2, 2, -10, 1, -4, 0, -4, 2, -4,
     1, -2, 0, 0, 7, -2, -4, 12, -2, 0, 0, -8, 3, 10, 10, -1, -4, 0, -2, 0,
     -1, 1, -10, 12, 0, 2, -4, 2, -12, -6, -1, 0, 0, 0, -8, 4, 5, 2, 7, -4] := by
  eta_coeff

end WeightTwoCusps

