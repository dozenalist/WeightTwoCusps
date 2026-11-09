module

import WeightTwoCusps

/-! # Regression tests for numeral dimension evaluation

These examples use the public entry point. They cover elliptic corrections,
composite levels, exceptional small levels, local hypotheses, and expressions
outside the positive-level analytic formulas' scope.
-/

open WeightTwoCusps WeightTwoCusps.Tactic

-- The arithmetic Γ₀ expression supports definitional simplification.
example : gamma0Dimension 0 = 1 := by dsimp
example : gamma0Dimension 1 = 0 := by dsimp
example : gamma0Dimension 11 = 1 := by dsimp
example : gamma0Dimension 13 = 0 := by dsimp
example : gamma0Dimension 37 = 2 := by dsimp
example : gamma0Dimension 49 = 1 := by dsimp
example : gamma0Dimension 50 = 2 := by dsimp
example : gamma0Dimension 1009 = 83 := by dsimp

-- The actual analytic spaces use proof-producing simplification.
example : Module.finrank ℂ (gamma0CuspForms 11) = 1 := by simp
example : Module.finrank ℂ (gamma0CuspForms 1) = 0 := by simp
example : Module.finrank ℂ (gamma0CuspForms 37) = 2 := by simp
example : Module.finrank ℂ (gamma0CuspForms 49) = 1 := by simp
example : Module.finrank ℂ (gamma0CuspForms 50) = 2 := by simp
example : Module.finrank ℂ (gamma0CuspForms 1009) = 83 := by simp
example : Module.finrank ℂ (gamma0CuspForms 13) = 0 := by
  simp only [gamma0CuspForms_finrank_ofNat]
example : Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 11) 2) = 1 := by simp

-- Γ₁ includes the exceptional level four and the totient convolution at sixteen.
example : gamma1Dimension 0 = 0 := by simp
example : gamma1Dimension 4 = 0 := by simp
example : gamma1Dimension 5 = 0 := by simp
example : gamma1Dimension 11 = 1 := by simp
example : gamma1Dimension 13 = 2 := by simp
example : gamma1Dimension 16 = 2 := by simp
example : Module.finrank ℂ (gamma1CuspForms 1) = 0 := by simp
example : Module.finrank ℂ (gamma1CuspForms 4) = 0 := by simp
example : Module.finrank ℂ (gamma1CuspForms 5) = 0 := by simp
example : Module.finrank ℂ (gamma1CuspForms 11) = 1 := by simp
example : Module.finrank ℂ (gamma1CuspForms 13) = 2 := by simp
example : Module.finrank ℂ (gamma1CuspForms 16) = 2 := by
  simp only [gamma1CuspForms_finrank_ofNat]
example : Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma1 13) 2) = 2 := by simp

-- Principal levels include the level-two index exception and the first positive genus.
example : gammaDimension 0 = 0 := by simp
example : gammaDimension 1 = 0 := by simp
example : gammaDimension 2 = 0 := by simp
example : gammaDimension 3 = 0 := by simp
example : gammaDimension 4 = 0 := by simp
example : gammaDimension 5 = 0 := by simp
example : gammaDimension 6 = 1 := by simp
example : gammaDimension 7 = 3 := by simp
example : gammaDimension 11 = 26 := by simp
example : gammaDimension 12 = 25 := by simp
example : Module.finrank ℂ (gammaCuspForms 1) = 0 := by simp
example : Module.finrank ℂ (gammaCuspForms 2) = 0 := by simp
example : Module.finrank ℂ (gammaCuspForms 6) = 1 := by simp
example : Module.finrank ℂ (gammaCuspForms 7) = 3 := by simp
example : Module.finrank ℂ (gammaCuspForms 11) = 26 := by
  simp only [gammaCuspForms_finrank_ofNat]
example : Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma 12) 2) = 25 := by simp

-- Congruence, casts, and local hypotheses must work without manual formula rewrites.
example : Module.finrank ℂ (gamma0CuspForms 11) + 3 = 4 := by simp
example : (Module.finrank ℂ (gamma1CuspForms 13) : ℚ) = 2 := by simp
example (h : gamma1Dimension 13 = 7) : False := by simp at h

-- Symbolic levels and level-zero analytic dimensions are deliberately left alone.
section Untouched

-- A no-op simplification is the behavior these tests are checking.
set_option linter.unusedTactic false

example (N : ℕ) (q : ℚ) (h : gamma0Dimension N = q) : gamma0Dimension N = q := by
  conv_lhs => dsimp only [gamma0Dimension_ofNat]
  guard_target = gamma0Dimension N = q
  exact h

example (N d : ℕ) (h : Module.finrank ℂ (gamma1CuspForms N) = d) :
    Module.finrank ℂ (gamma1CuspForms N) = d := by
  conv_lhs => simp only [gamma1CuspForms_finrank_ofNat]
  guard_target = Module.finrank ℂ (gamma1CuspForms N) = d
  exact h

example (d : ℕ) (h : Module.finrank ℂ (gamma0CuspForms 0) = d) :
    Module.finrank ℂ (gamma0CuspForms 0) = d := by
  conv_lhs => simp only [gamma0CuspForms_finrank_ofNat]
  guard_target = Module.finrank ℂ (gamma0CuspForms 0) = d
  exact h

example (d : ℕ) (h : Module.finrank ℂ (gamma1CuspForms 0) = d) :
    Module.finrank ℂ (gamma1CuspForms 0) = d := by
  conv_lhs => simp only [gamma1CuspForms_finrank_ofNat]
  guard_target = Module.finrank ℂ (gamma1CuspForms 0) = d
  exact h

example (d : ℕ) (h : Module.finrank ℂ (gammaCuspForms 0) = d) :
    Module.finrank ℂ (gammaCuspForms 0) = d := by
  conv_lhs => simp only [gammaCuspForms_finrank_ofNat]
  guard_target = Module.finrank ℂ (gammaCuspForms 0) = d
  exact h

example (d : ℕ) (h : Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 11) 4) = d) :
    Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 11) 4) = d := by
  conv_lhs => simp only [gamma0CuspForms_finrank_ofNat]
  guard_target = Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 11) 4) = d
  exact h

end Untouched
