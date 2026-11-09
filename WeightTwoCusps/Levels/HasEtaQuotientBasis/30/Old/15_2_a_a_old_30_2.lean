module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«15».New.«15_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# The dilation-2 lift of 15.2.a.a to level 30

This is the function `f(2z)`, with eta product `η(2z)η(6z)η(10z)η(30z)`.
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

/-- The oldform `f(2z)` at level 30, with source `15.2.a.a`. -/
abbrev cuspForm_15_2_a_a_old_30_2 : gamma0CuspForms 30 :=
  gamma0Rescale cuspForm_15_2_a_a 2

/-- The degeneracy lift is the corresponding cuspidal eta product. -/
theorem cuspForm_15_2_a_a_old_30_2_eq_eta :
    cuspForm_15_2_a_a_old_30_2 =
      etaQuotientCuspForm 30 sparse![30; 1 => 1, 5 => 1, 9 => 1, 29 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_15_2_a_a_old_30_2_first_coeffs : first_coeffs 100 cuspForm_15_2_a_a_old_30_2 =
    [0, 0, 1, 0, -1, 0, -1, 0, -1, 0, 1, 0, 1, 0, 0, 0, 3, 0, 1, 0,
     -1, 0, -4, 0, 1, 0, -2, 0, 0, 0, -1, 0, -1, 0, 2, 0, -1, 0, 4, 0,
     -1, 0, 0, 0, 4, 0, 0, 0, -3, 0, 1, 0, 2, 0, -1, 0, 0, 0, -2, 0,
     1, 0, 0, 0, -5, 0, 4, 0, -2, 0, 0, 0, -1, 0, -10, 0, -4, 0, 2, 0,
     3, 0, 10, 0, 0, 0, 4, 0, 4, 0, 1, 0, 0, 0, 8, 0, 1, 0, -7, 0] := by
  eta_coeff

end WeightTwoCusps

