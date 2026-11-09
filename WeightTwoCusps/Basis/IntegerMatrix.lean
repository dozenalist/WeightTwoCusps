module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Matrix.OfLists
public import Mathlib.Data.List.GetD

/-!
# Determinant certificates over the integers

The verifier checks only the lower triangle and diagonal of a product modulo
an arbitrary modulus greater than one. The diagonal is normalized to one, so
neither primality nor invertibility of the supplied transform is a hypothesis.
All computations in the verifier use natural numbers, with one reduction per
dot product. Integer and rational matrices are connected by cast and row-scaling
lemmas; none of these results depend on cusp forms or a particular matrix size.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

namespace WeightTwoCusps

open Mathlib.Tactic.Matrix

/-- Integer determinant nonzeroness is preserved and reflected by a
characteristic-zero cast. The finite index type is unrestricted. -/
theorem matrix_det_intCast_iff {K ι : Type*} [CommRing K] [CharZero K]
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ) :
    (A.map (fun x ↦ (x : K))).det ≠ 0 ↔ A.det ≠ 0 := by
  rw [← Int.cast_det, Int.cast_ne_zero]

theorem matrix_det_ne_zero_of_int_eq {K ι : Type*} [CommRing K] [CharZero K]
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (B : Matrix ι ι ℤ)
    (heq : A = B.map (fun x ↦ (x : K))) (hB : B.det ≠ 0) : A.det ≠ 0 := by
  rw [heq]
  exact (matrix_det_intCast_iff B).mpr hB

/-- Clearing denominators can be certified just by a matrix equality. No
separate proof about the scaling factors is needed in this direction. -/
theorem matrix_det_ne_zero_of_int_rowScale {K ι : Type*} [CommRing K] [CharZero K]
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (B : Matrix ι ι ℤ)
    (s : ι → K) (heq : Matrix.diagonal s * A = B.map (fun x ↦ (x : K)))
    (hB : B.det ≠ 0) : A.det ≠ 0 := by
  intro hA
  have h := (matrix_det_intCast_iff (K := K) B).mpr hB
  rw [← heq, Matrix.det_mul, hA, mul_zero] at h
  exact h rfl

/-- With nonzero row scales, clearing denominators is an equivalence. -/
theorem matrix_det_int_rowScale_iff {K ι : Type*} [CommRing K] [IsDomain K] [CharZero K]
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) (B : Matrix ι ι ℤ)
    (s : ι → K) (hs : ∀ i, s i ≠ 0)
    (heq : Matrix.diagonal s * A = B.map (fun x ↦ (x : K))) :
    B.det ≠ 0 ↔ A.det ≠ 0 := by
  rw [← matrix_det_intCast_iff (K := K), ← heq, Matrix.det_mul]
  have hd : (Matrix.diagonal s).det ≠ 0 := by
    simp only [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    exact fun i _ ↦ hs i
  rw [mul_ne_zero_iff]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨hd, h⟩⟩

theorem matrix_diagonal_mul_eq {K ι : Type*} [Semiring K]
    [Fintype ι] [DecidableEq ι] (s : ι → K) (A : Matrix ι ι K) :
    Matrix.diagonal s * A = fun i j ↦ s i * A i j := by
  ext i j
  exact Matrix.diagonal_mul s A i j

/-- An exposed sequential dot product for kernel evaluation. -/
def modularDot : ℕ → List ℕ → List ℕ → ℕ
  | 0, _, _ => 0
  | n + 1, a, b => a.headD 0 * b.headD 0 + modularDot n a.tail b.tail

theorem modularDot_eq (n : ℕ) (a b : List ℕ) :
    modularDot n a b = ListMatrix.dotProduct n a b := by
  induction n generalizing a b with
  | zero => exact (ListMatrix.dotProduct_zero a b).symm
  | succ n ih => rw [modularDot, ListMatrix.dotProduct_add_one, ih]

/-- Reduce the input once, before any dot products are checked. -/
def matrixResidues (p : ℕ) (a : List (List ℤ)) : List (List ℕ) :=
  a.map (List.map fun z ↦ (z % (p : ℤ)).toNat)

/-- Only entries on and below the diagonal are computed. Missing entries of
the list representation are padded by zero, as in `ofLists`. -/
def modularUpperCheckColumns (p n : ℕ) (e cols : List (List ℕ)) : Bool :=
  (List.range n).all fun i ↦
    let row := e.getD i []
    (List.range (i + 1)).all fun j ↦
      let v := modularDot n row (cols.getD j []) % p
      if j < i then v == 0 else v == 1

/-- The convenience wrapper computes the columns itself. Tactics may instead
certify a materialized transpose once and use `modularUpperCheckColumns`. -/
def modularUpperCheck (p n : ℕ) (e a : List (List ℕ)) : Bool :=
  modularUpperCheckColumns p n e (ListMatrix.transpose n a)

theorem matrix_ofLists_map {R S : Type*} [Zero R] [Zero S]
    (f : R → S) (hf : f 0 = 0) (m n : ℕ) (a : List (List R)) :
    ofLists m n (a.map (List.map f)) = (ofLists m n a).map f := by
  ext i j
  simp only [ofLists_apply, ofList_apply, Matrix.map_apply]
  rw [← List.map_nil (f := f), List.getD_map, ← hf, List.getD_map]

theorem matrixResidues_cast (p n : ℕ) (hp : 0 < p) (a : List (List ℤ)) :
    (ofLists n n (matrixResidues p a)).map (fun x ↦ (x : ZMod p)) =
      (ofLists n n a).map (fun x ↦ (x : ZMod p)) := by
  rw [← matrix_ofLists_map (fun x : ℕ ↦ (x : ZMod p)) (by simp)]
  rw [← matrix_ofLists_map (fun x : ℤ ↦ (x : ZMod p)) (by simp)]
  unfold matrixResidues
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro row _
  simp only [Function.comp_apply, List.map_map]
  apply List.map_congr_left
  intro z _
  change (((z % (p : ℤ)).toNat : ℕ) : ZMod p) = (z : ZMod p)
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.emod_nonneg z (by omega))]
  exact ZMod.intCast_mod z p

private theorem modularDot_mul (n : ℕ) (e a : List (List ℕ)) (i j : Fin n) :
    modularDot n (e.getD i []) ((ListMatrix.transpose n a).getD j []) =
      (ofLists n n e * ofLists n n a) i j := by
  rw [modularDot_eq, ListMatrix.dotProduct_eq, Matrix.mul_apply']
  congr 1
  · exact (ofLists_apply n n e i).symm
  · funext k
    simp only [ofList_apply, ofLists_apply]
    exact ListMatrix.getD_transpose a k j.isLt

/-- The certificate proves that the product over `ZMod p` is unit upper
triangular. The checker never computes entries above the diagonal. -/
theorem modularUpperCheck_sound (p n : ℕ) (e a : List (List ℕ))
    (h : modularUpperCheck p n e a = true) :
    let C := ((ofLists n n e * ofLists n n a).map (fun x ↦ (x : ZMod p)))
    C.IsUpperTriangular ∧ ∀ i, C i i = 1 := by
  have entry (i j : Fin n) (hji : j ≤ i) :
      if j < i then
        (ofLists n n e * ofLists n n a) i j % p = 0
      else (ofLists n n e * ofLists n n a) i j % p = 1 := by
    have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
    have hij := List.all_eq_true.mp hi j.val (List.mem_range.mpr (by omega))
    rw [← modularDot_mul]
    by_cases hj : j.val < i.val
    · simpa only [Fin.lt_def, hj, ↓reduceIte, beq_iff_eq] using hij
    · simpa only [Fin.lt_def, hj, ↓reduceIte, beq_iff_eq] using hij
  constructor
  · intro i j hji
    change (((ofLists n n e * ofLists n n a) i j : ℕ) : ZMod p) = 0
    have hz := entry i j (le_of_lt hji)
    rw [ite_eq_left (show j < i from hji)] at hz
    rw [← ZMod.natCast_mod, hz, Nat.cast_zero]
  · intro i
    have ho := entry i i le_rfl
    simp only [lt_self_iff_false, ↓reduceIte] at ho
    change (((ofLists n n e * ofLists n n a) i i : ℕ) : ZMod p) = 1
    rw [← ZMod.natCast_mod, ho, Nat.cast_one]

/-- A natural-number partial-product certificate modulo any `p > 1`
proves that the original integer matrix has nonzero determinant. -/
theorem matrix_det_ne_zero_of_modularUpperCheck (p n : ℕ) (hp : 1 < p)
    (a : List (List ℤ)) (e : List (List ℕ))
    (h : modularUpperCheck p n e (matrixResidues p a) = true) :
    (ofLists n n a).det ≠ 0 := by
  have : Fact (1 < p) := ⟨hp⟩
  obtain ⟨hu, hd⟩ := modularUpperCheck_sound p n e (matrixResidues p a) h
  have hdet : ((ofLists n n e * ofLists n n (matrixResidues p a)).map
      (fun x ↦ (x : ZMod p))).det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hu]
    simp only [hd, Finset.prod_const_one]
  rw [show ((ofLists n n e * ofLists n n (matrixResidues p a)).map
      (fun x ↦ (x : ZMod p))) =
      (ofLists n n e).map (fun x ↦ (x : ZMod p)) *
      (ofLists n n (matrixResidues p a)).map (fun x ↦ (x : ZMod p)) from
      Matrix.map_mul (f := Nat.castRingHom (ZMod p)),
    matrixResidues_cast p n (by omega) a, Matrix.det_mul,
    ← Int.cast_det] at hdet
  intro hz
  rw [hz, Int.cast_zero, mul_zero] at hdet
  exact zero_ne_one hdet

/-- Materializing the reduced columns keeps their transposition and integer
reduction out of every individual dot-product evaluation. -/
theorem matrix_det_ne_zero_of_modularColumns (p n : ℕ) (hp : 1 < p)
    (a : List (List ℤ)) (e cols : List (List ℕ))
    (hc : ListMatrix.transpose n (matrixResidues p a) = cols)
    (h : modularUpperCheckColumns p n e cols = true) :
    (ofLists n n a).det ≠ 0 := by
  apply matrix_det_ne_zero_of_modularUpperCheck p n hp a e
  simpa only [modularUpperCheck, hc] using h

end WeightTwoCusps
