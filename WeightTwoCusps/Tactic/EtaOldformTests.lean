module

public import WeightTwoCusps.Tactic.EtaOldform
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«22».Old.«11_2_a_a_old_22_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«22».Old.«11_2_a_a_old_22_2»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«28».Old.«14_2_a_a_old_28_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«28».Old.«14_2_a_a_old_28_2»

/-! # Regression checks for exact oldform eta-product identities -/

@[expose] public noncomputable section

open WeightTwoCusps

namespace WeightTwoCusps.EtaOldformTests

-- Ordinary definitions, as well as abbreviations, are unfolded automatically.
def namedSource : gamma0CuspForms 14 := cuspForm_14_2_a_a

def namedLift : gamma0CuspForms 28 := gamma0Rescale namedSource 2

theorem namedLift_eq_eta :
    namedLift = etaQuotientCuspForm 28 sparse![28; 1 => 1, 3 => 1, 13 => 1, 27 => 1] := by
  eta_oldform

-- Dilation one, restriction, a larger ambient level, and reversed equalities.
example : gamma0RescaleToLevel cuspForm_11_2_a_a 1 (by decide : 11 * 1 ∣ 22) =
    etaQuotientCuspForm 22 sparse![22; 0 => 2, 10 => 2] := by
  eta_oldform

example : gamma0Restrict cuspForm_14_2_a_a (by decide : 14 ∣ 28) =
    etaQuotientCuspForm 28 sparse![28; 0 => 1, 1 => 1, 6 => 1, 13 => 1] := by
  eta_oldform

example : etaQuotientCuspForm 44 sparse![44; 1 => 2, 21 => 2] =
    gamma0RescaleToLevel cuspForm_11_2_a_a 2 (by decide : 11 * 2 ∣ 44) := by
  eta_oldform

-- The factor is not restricted to two, and successive dilations compose.
example : gamma0Rescale cuspForm_11_2_a_a 3 =
    etaQuotientCuspForm 33 sparse![33; 2 => 2, 32 => 2] := by
  eta_oldform

example : gamma0Rescale (gamma0Rescale cuspForm_11_2_a_a 2) 2 =
    etaQuotientCuspForm 44 sparse![44; 3 => 2, 43 => 2] := by
  eta_oldform

-- Negative exponents in a cuspidal eta quotient are preserved as well.
abbrev signedSource : gamma0CuspForms 38 :=
  etaQuotientCuspForm 38 sparse![38; 0 => 3, 1 => -1, 18 => -1, 37 => 3]

example : gamma0Rescale signedSource 2 = etaQuotientCuspForm 76
    sparse![76; 1 => 3, 3 => -1, 37 => -1, 75 => 3] := by
  eta_oldform

-- Named exponent vectors need no extra unfold arguments at the call site.
def namedExponents : Fin 11 → ℤ := sparse![11; 0 => 2, 10 => 2]

def namedEta : gamma0CuspForms 11 := etaQuotientCuspForm 11 namedExponents

example : gamma0Rescale namedEta 2 =
    etaQuotientCuspForm 22 sparse![22; 1 => 2, 21 => 2] := by
  eta_oldform

-- Local let aliases are followed as well.
example : gamma0Rescale cuspForm_11_2_a_a 2 =
    etaQuotientCuspForm 22 sparse![22; 1 => 2, 21 => 2] := by
  let f : gamma0CuspForms 11 := cuspForm_11_2_a_a
  change gamma0Rescale f 2 = _
  eta_oldform

-- A wrong dilation and an unsupported goal must be rejected, with no residual goals.
example : True := by
  fail_if_success
    have : gamma0Rescale cuspForm_11_2_a_a 2 =
        etaQuotientCuspForm 22 sparse![22; 0 => 2, 10 => 2] := by
      eta_oldform
  fail_if_success eta_oldform
  trivial

#print axioms namedLift_eq_eta
#print axioms cuspForm_11_2_a_a_old_22_1_eq_eta
#print axioms cuspForm_11_2_a_a_old_22_2_eq_eta
#print axioms cuspForm_14_2_a_a_old_28_1_eq_eta
#print axioms cuspForm_14_2_a_a_old_28_2_eq_eta

end WeightTwoCusps.EtaOldformTests
