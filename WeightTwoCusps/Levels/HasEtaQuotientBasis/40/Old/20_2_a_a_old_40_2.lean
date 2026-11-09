module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«20».New.«20_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# The dilation-2 lift of 20.2.a.a to level 40

This is the function `f(2z)`, with eta product `η(4z)²η(20z)²`.
The original normalized newform is recorded at
https://www.lmfdb.org/ModularForm/GL2/Q/holomorphic/20/2/a/a/.
Its lift occurs in the cuspidal basis of
`M2_Gamma0_Eta_Quotient_Bases_N_1_to_500`; see
[the local level table](../../TABLE.md#level-40).
-/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The oldform `f(2z)` at level 40, with source `20.2.a.a`. -/
abbrev cuspForm_20_2_a_a_old_40_2 : gamma0CuspForms 40 :=
  gamma0Rescale cuspForm_20_2_a_a 2

/-- The degeneracy lift is the corresponding cuspidal eta product. -/
theorem cuspForm_20_2_a_a_old_40_2_eq_eta :
    cuspForm_20_2_a_a_old_40_2 =
      etaQuotientCuspForm 40 sparse![40; 3 => 2, 19 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_20_2_a_a_old_40_2_first_coeffs : first_coeffs 100 cuspForm_20_2_a_a_old_40_2 =
    [0, 0, 1, 0, 0, 0, -2, 0, 0, 0, -1, 0, 0, 0, 2, 0, 0, 0, 1, 0,
     0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, -6, 0, 0, 0, -4, 0,
     0, 0, -4, 0, 0, 0, 6, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 6, 0,
     0, 0, -4, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 2, 0, 0, 0, -4, 0,
     0, 0, 6, 0, 0, 0, -10, 0, 0, 0, -1, 0, 0, 0, -6, 0, 0, 0, -3, 0] := by
  eta_coeff

end WeightTwoCusps

