module

public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Basis.Constructor
public import WeightTwoCusps.Tactic.EtaOldform
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«11».New.«11_2_a_a»

/-! # Checks of degeneracy lifts and their normalization -/

@[expose] public section

noncomputable section

open UpperHalfPlane

namespace WeightTwoCusps.OldformsTests

abbrev f22 : gamma0CuspForms 22 :=
  gamma0RescaleToLevel cuspForm_11_2_a_a 1 (by decide)

abbrev g22 : gamma0CuspForms 22 :=
  gamma0Rescale cuspForm_11_2_a_a 2

/-- Dilation one is the original eta product, bundled at level 22. -/
theorem f22_eq_eta :
    f22 = etaQuotientCuspForm 22 sparse![22; 0 => 2, 10 => 2] := by
  eta_oldform

/-- Dilation two gives `η(2z)²η(22z)²` with leading coefficient one. -/
theorem g22_eq_eta :
    g22 = etaQuotientCuspForm 22 sparse![22; 1 => 2, 21 => 2] := by
  eta_oldform

example : first_coeffs 8 g22 = [0, 0, 1, 0, -2, 0, -1, 0] := by
  eta_coeff

/-- Actual degeneracy lifts can be used with the existing basis constructor. -/
def level22Basis : Module.Basis (Fin 2) ℂ (gamma0CuspForms 22) :=
  cuspFormBasis ![f22, g22]

-- A larger ambient level uses only a divisibility certificate.
example : gamma0CuspForms 44 :=
  gamma0RescaleToLevel cuspForm_11_2_a_a 2 (by decide)

-- Repeated lifts agree with the direct lift from the original source level.
example :
    gamma0RescaleToLevel (gamma0RescaleToLevel cuspForm_11_2_a_a 2 (by decide : 22 ∣ 22))
        2 (by decide : 44 ∣ 44) =
      gamma0RescaleToLevel cuspForm_11_2_a_a 4 (by decide : 44 ∣ 44) := by
  exact gamma0RescaleToLevel_trans cuspForm_11_2_a_a 2 2 (by decide) (by decide)
    (by decide) (by decide)

-- The public import exposes a complex linear map as well as the constructor.
example (f g : gamma0CuspForms 11) (c : ℂ) :
    (gamma0Rescaleₗ 2) (c • f + g) =
      c • (gamma0Rescaleₗ 2) f + (gamma0Rescaleₗ 2) g := by
  simp

example : True := by
  fail_if_success
    have := gamma0Rescale cuspForm_11_2_a_a 0
  fail_if_success
    have : gamma0CuspForms 14 :=
      gamma0RescaleToLevel cuspForm_11_2_a_a 2 (by decide)
  trivial

#print axioms gamma0Rescale
#print axioms gamma0RescaleToLevel_trans
#print axioms gamma0RescaleToLevel_injective
#print axioms level22Basis

end WeightTwoCusps.OldformsTests
