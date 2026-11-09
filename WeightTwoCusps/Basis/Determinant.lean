module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import WeightTwoCusps.QExpansion
public import WeightTwoCusps.Tactic.EtaSimps
public import Mathlib.Tactic.Matrix.OfLists

/-! # Nonzero determinants from full-rank certificates -/

@[expose] public section

namespace WeightTwoCusps

/-- A sequential dot product exposed for kernel evaluation of certificates. -/
def certificateDot {α : Type*} [Mul α] [Add α] [Zero α] : ℕ → List α → List α → α
  | 0, _, _ => 0
  | n + 1, a, b => a.headD 0 * b.headD 0 + certificateDot n a.tail b.tail

theorem certificateDot_eq {α : Type*} [Mul α] [Add α] [Zero α]
    (n : ℕ) (a b : List α) :
    certificateDot n a b = Mathlib.Tactic.Matrix.ListMatrix.dotProduct n a b := by
  induction n generalizing a b with
  | zero => exact (Mathlib.Tactic.Matrix.ListMatrix.dotProduct_zero a b).symm
  | succ n ih => rw [certificateDot, Mathlib.Tactic.Matrix.ListMatrix.dotProduct_add_one, ih]

/-- Matrix multiplication by sequential list traversals, without a cubic-size
expanded arithmetic expression in the proof term. -/
def certificateMul {α : Type*} [Mul α] [Add α] [Zero α]
    (l m n : ℕ) (a b : List (List α)) : List (List α) :=
  let bt := Mathlib.Tactic.Matrix.ListMatrix.transpose n b
  (a.rightpad l []).map fun row ↦ bt.map (certificateDot m row)

theorem matrix_mul_eq_of_certificate {α : Type*} [Mul α] [AddCommMonoid α]
    {l m n : ℕ} {a b c : List (List α)} (h : certificateMul l m n a b = c) :
    Mathlib.Tactic.Matrix.ofLists l m a * Mathlib.Tactic.Matrix.ofLists m n b =
      Mathlib.Tactic.Matrix.ofLists l n c := by
  apply Mathlib.Tactic.Matrix.ofLists_mul
  have heq : @certificateDot α _ _ _ m = Mathlib.Tactic.Matrix.ListMatrix.dotProduct m :=
    funext fun a ↦ funext fun b ↦ certificateDot_eq m a b
  simpa only [certificateMul, heq, Mathlib.Tactic.Matrix.ListMatrix.mul] using h

/-- Rational determinant certificates transport to any characteristic-zero field. -/
theorem matrix_det_ne_zero_of_rat {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (h : A.det ≠ 0) :
    (A.map fun (x : ℚ) ↦ (x : K)).det ≠ 0 := by
  rw [← Rat.cast_det]
  exact_mod_cast h

/-- A full-rank square matrix over any field has nonzero determinant.
The index type is arbitrary, including the empty type. -/
theorem matrix_det_ne_zero_of_rank_eq_card {K : Type*} {ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K)
    (h : A.rank = Fintype.card ι) : A.det ≠ 0 := by
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det A).mp
  apply Matrix.mulVec_surjective_iff_isUnit.mp
  exact Matrix.mulVec_surjective_iff_rank_eq_card.mpr h

end WeightTwoCusps
