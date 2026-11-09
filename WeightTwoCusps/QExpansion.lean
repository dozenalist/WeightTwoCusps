module

public import Mathlib.NumberTheory.ModularForms.QExpansion

/-! # Finite lists of q-expansion coefficients -/

@[expose] public noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The first `m` coefficients of the period-one q-expansion, in increasing
order of degree, including the constant coefficient. -/
def first_coeffs : ℕ → (ℍ → ℂ) → List ℂ
  | 0, _ => []
  | m + 1, f => first_coeffs m f ++ [(qExpansion 1 f).coeff m]

@[simp] theorem first_coeffs_zero (f : ℍ → ℂ) : first_coeffs 0 f = [] := rfl

theorem first_coeffs_succ (m : ℕ) (f : ℍ → ℂ) :
    first_coeffs (m + 1) f = first_coeffs m f ++ [(qExpansion 1 f).coeff m] := rfl

@[simp] theorem first_coeffs_length (m : ℕ) (f : ℍ → ℂ) :
    (first_coeffs m f).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [first_coeffs_succ, ih]

/-- The recursive definition agrees with coefficient extraction over `range m`. -/
theorem first_coeffs_eq_map_range (m : ℕ) (f : ℍ → ℂ) :
    first_coeffs m f = (List.range m).map (fun n ↦ (qExpansion 1 f).coeff n) := by
  induction m with
  | zero => rfl
  | succ m ih => simp [first_coeffs_succ, ih, List.range_succ]

@[simp] theorem first_coeffs_getElem (m : ℕ) (f : ℍ → ℂ) (n : ℕ)
    (hn : n < (first_coeffs m f).length := by decide) :
    (first_coeffs m f)[n] = (qExpansion 1 f).coeff n := by
  simp [first_coeffs_eq_map_range]

end WeightTwoCusps
