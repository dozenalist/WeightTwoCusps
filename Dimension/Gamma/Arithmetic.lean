module

public import Dimension.Gamma.Basic

@[expose] public section

/-!
# Arithmetic form of the principal-level dimension formula

For `N ≥ 2`, write `μ` for the index of the image of `Γ(N)` in
`PSL₂(ℤ)`. The dimension formula is
`dim S₂(Γ(N)) = 1 + μ (N - 6) / (12 N)`.

The subtraction in this display takes place in `ℚ`; in particular it also
applies to the genus-zero levels `2, 3, 4, 5`.
-/

noncomputable section

open scoped MatrixGroups

namespace WeightTwoCusps

/-- The index of the image of `Γ(N)` in `PSL₂(ℤ)`, computed in `SL₂(ℤ)`
by adjoining the central element `-I`. -/
abbrev projectiveIndex (N : ℕ) : ℕ :=
  (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index

/-- The natural-number version of the dimension formula. The numerator is
written with natural subtraction so that no rounding convention is implicit. -/
def gammaDimension (N : ℕ) : ℕ :=
  if N = 1 then 0
  else (12 * N + N * projectiveIndex N - 6 * projectiveIndex N) / (12 * N)

/-- Solving the integral dimension relation in natural numbers. -/
lemma dimension_nat_of_relation {N μ d : ℕ} (hN : 0 < N)
    (h : 12 * N * d + 6 * μ = 12 * N + N * μ) :
    d = (12 * N + N * μ - 6 * μ) / (12 * N) := by
  have hsub : 12 * N + N * μ - 6 * μ = 12 * N * d := by omega
  rw [hsub, Nat.mul_div_cancel_left _ (by positivity)]

/-- Solving the integral dimension relation in rational numbers. -/
lemma dimension_rat_of_relation {N μ d : ℕ} (hN : 0 < N)
    (h : 12 * N * d + 6 * μ = 12 * N + N * μ) :
    (d : ℚ) = 1 + (μ : ℚ) * ((N : ℚ) - 6) / (12 * N) := by
  have hq : 12 * (N : ℚ) * d + 6 * μ = 12 * N + N * μ := by
    exact_mod_cast h
  have hNq : (N : ℚ) ≠ 0 := by positivity
  field_simp [hNq]
  nlinarith [hq]

end WeightTwoCusps
