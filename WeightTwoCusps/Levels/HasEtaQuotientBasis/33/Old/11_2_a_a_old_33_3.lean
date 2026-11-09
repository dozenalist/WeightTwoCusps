module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«11».New.«11_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# The dilation-3 lift of 11.2.a.a to level 33

This is the function `f(3z)`, with eta product `η(3z)²η(33z)²`.
The original normalized newform is recorded at
https://www.lmfdb.org/ModularForm/GL2/Q/holomorphic/11/2/a/a/.
Its lift occurs in the cuspidal basis of
`M2_Gamma0_Eta_Quotient_Bases_N_1_to_500`; see
[the local level table](../../TABLE.md#level-33).
-/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The oldform `f(3z)` at level 33, with source `11.2.a.a`. -/
abbrev cuspForm_11_2_a_a_old_33_3 : gamma0CuspForms 33 :=
  gamma0Rescale cuspForm_11_2_a_a 3

/-- The degeneracy lift is the corresponding cuspidal eta product. -/
theorem cuspForm_11_2_a_a_old_33_3_eq_eta :
    cuspForm_11_2_a_a_old_33_3 =
      etaQuotientCuspForm 33 sparse![33; 2 => 2, 32 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_11_2_a_a_old_33_3_first_coeffs : first_coeffs 100 cuspForm_11_2_a_a_old_33_3 =
    [0, 0, 0, 1, 0, 0, -2, 0, 0, -1, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0,
     0, -2, 0, 0, 0, 0, 0, -2, 0, 0, -2, 0, 0, 1, 0, 0, -2, 0, 0, 4,
     0, 0, 4, 0, 0, -1, 0, 0, -4, 0, 0, -2, 0, 0, 4, 0, 0, 0, 0, 0,
     2, 0, 0, 2, 0, 0, -2, 0, 0, -1, 0, 0, 0, 0, 0, -4, 0, 0, -8, 0,
     0, 5, 0, 0, -4, 0, 0, 0, 0, 0, 2, 0, 0, 7, 0, 0, 8, 0, 0, -1] := by
  eta_coeff

end WeightTwoCusps

