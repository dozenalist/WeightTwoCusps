module

public import WeightTwoCusps.Tactic.Basic

/-! # Sparse-vector representation regressions -/

public section

open WeightTwoCusps.Tactic

example : (sparse![500; 0 => (2 : ℤ), 499 => -3]) 499 = -3 := rfl
example : (sparse![500; 0 => (2 : ℤ), 499 => -3]) 250 = 0 := rfl
example : (sparse![10; 2 => (1 : ℤ), 2 => -4]) 2 = -4 := rfl
example : (sparse![10;] : Fin 10 → ℤ) = fun _ ↦ 0 := rfl
example : (sparse![0;] : Fin 0 → ℤ) = ![] := by decide +kernel
example (a b : ℤ) : (sparse![20; 0 => a, 19 => b]) 19 = b := rfl
example : (sparse![4; 0 => (1 : ℤ), 3 => -2]) = ![1, 0, 0, -2] := by decide +kernel

example : True := by
  fail_if_success
    have : Fin 3 → ℤ := sparse![3; 3 => 1]
  trivial
