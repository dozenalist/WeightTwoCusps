module

public import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Computable arithmetic on integer coefficient sequences

These operations use finite sums and integer arithmetic. Their correctness
lemmas identify them with coefficients of complex formal power series.
The inverse operation is intended for series with constant coefficient one.
-/

@[expose] public section

namespace WeightTwoCusps.EtaQuotient

open PowerSeries Complex

set_option backward.isDefEq.respectTransparency false

/-- Euler coefficients using exposed integer arithmetic. The square-root
bound follows from `k² ≤ pentagonal k`, avoiding a linear search in the degree.
Mathlib's `pentagonal` definition is opaque across module boundaries. -/
def eulerCoefficient (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc (-(Nat.sqrt n : ℤ)) (Nat.sqrt n : ℤ),
    if (k * (3 * k - 1) / 2).toNat = n then (-1 : ℤ) ^ k.natAbs else 0

/-- Cauchy convolution of integer coefficient sequences. -/
def convolution (a b : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), a k * b (n - k)

/-- A Cauchy coefficient only depends on the input coefficients up to its degree. -/
theorem convolution_congr {a b a' b' : ℕ → ℤ} {n : ℕ}
    (ha : ∀ k ≤ n, a k = a' k) (hb : ∀ k ≤ n, b k = b' k) :
    convolution a b n = convolution a' b' n := by
  apply Finset.sum_congr rfl
  intro k hk
  rw [ha k (by simpa using Finset.mem_range.mp hk), hb (n - k) (Nat.sub_le n k)]

/-- Substitution `q ↦ q^N` on integer coefficient sequences. -/
def dilateCoefficient (N : ℕ) (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  if N ∣ n then a (n / N) else 0

private theorem natAbs_le_sqrt_pentagonal (k : ℤ) : k.natAbs ≤ Nat.sqrt (pentagonal k) := by
  apply Nat.le_sqrt'.mpr
  have h := two_mul_natCast_pentagonal k
  have hprod : 0 ≤ k * (k - 1) := by
    rcases (show k ≤ 0 ∨ 1 ≤ k by omega) with hk | hk
    · exact mul_nonneg_of_nonpos_of_nonpos hk (by omega)
    · exact mul_nonneg (by omega) (by omega)
  have habs : (k.natAbs : ℤ) ^ 2 = k ^ 2 := by simp
  have hs : (k.natAbs : ℤ) ^ 2 ≤ (pentagonal k : ℤ) := by nlinarith
  exact_mod_cast hs

theorem eulerCoefficient_cast (n : ℕ) :
    (eulerCoefficient n : ℂ) = (PowerSeries.pentagonalSeries ℂ).coeff n := by
  classical
  have heq : eulerCoefficient n =
      ∑ k ∈ Finset.Icc (-(Nat.sqrt n : ℤ)) (Nat.sqrt n : ℤ),
        if pentagonal k = n then (k.negOnePow : ℤ) else 0 := by
    unfold eulerCoefficient
    apply Finset.sum_congr rfl
    intro k _
    rw [pentagonal_def]
    split_ifs
    · have h := Int.coe_negOnePow ℤ k
      simpa only [Int.cast_id] using h.symm
    · rfl
  by_cases hn : n ∈ Set.range pentagonal
  · obtain ⟨k, rfl⟩ := hn
    have hk := natAbs_le_sqrt_pentagonal k
    have hmem : k ∈ Finset.Icc (-(Nat.sqrt (pentagonal k) : ℤ)) (Nat.sqrt (pentagonal k) : ℤ) := by
      simp only [Finset.mem_Icc]
      have hk' : (k.natAbs : ℤ) ≤ (Nat.sqrt (pentagonal k) : ℤ) := by exact_mod_cast hk
      rw [Int.natCast_natAbs] at hk'
      exact abs_le.mp hk'
    rw [heq, Finset.sum_eq_single_of_mem k hmem]
    · simp
    · intro j _ hj
      simp only [pentagonal_inj]
      simp [hj]
  · rw [PowerSeries.coeff_pentagonalSeries_eq_zero ℂ hn]
    simp only [heq]
    have h : ∀ k : ℤ, pentagonal k ≠ n := by simpa using hn
    simp [h]

theorem hasSum_eulerCoefficient {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n ↦ (eulerCoefficient n : ℂ) * q ^ n) (eulerFunction q) := by
  simpa only [eulerCoefficient_cast] using hasSum_eulerFunction_pentagonalSeries hq

/-- Substituting a positive integer power preserves convergence of a power series. -/
theorem hasSum_dilateCoefficient (N : ℕ) (hN : 0 < N) {a : ℕ → ℤ} {q A : ℂ}
    (ha : HasSum (fun n ↦ (a n : ℂ) * (q ^ N) ^ n) A) :
    HasSum (fun n ↦ (dilateCoefficient N a n : ℂ) * q ^ n) A := by
  have : NeZero N := ⟨hN.ne'⟩
  have hinj : Function.Injective (fun n : ℕ ↦ N * n) := by
    intro a b h
    exact Nat.eq_of_mul_eq_mul_left hN h
  apply (hinj.hasSum_iff ?_).mp
  · simpa [Function.comp_def, dilateCoefficient, pow_mul, Nat.mul_div_cancel_left _ hN] using ha
  · intro n hn
    have hd : ¬N ∣ n := by
      intro h
      obtain ⟨k, rfl⟩ := h
      exact hn ⟨k, rfl⟩
    simp [dilateCoefficient, hd]

/-- Coefficients of the constant series one. -/
def oneCoefficient (n : ℕ) : ℤ := if n = 0 then 1 else 0

/-- Coefficients of a natural power, using finite Cauchy products. -/
def powCoefficient (a : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0 => oneCoefficient
  | k + 1 => convolution a (powCoefficient a k)

/-- Coefficients of the reciprocal of a series whose constant coefficient is one. -/
def inverseCoefficient (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  if _hn : n = 0 then 1
  else - ∑ x ∈ Finset.antidiagonal n,
    if _hx : x.2 < n then a x.1 * inverseCoefficient a x.2 else 0
termination_by n

/-- Coefficients of an integer power of a series with constant coefficient one. -/
def zpowCoefficient (a : ℕ → ℤ) : ℤ → ℕ → ℤ
  | .ofNat k => powCoefficient a k
  | .negSucc k => powCoefficient (inverseCoefficient a) (k + 1)

/-- Coefficients of a finite ordered product of series. -/
def productCoefficient : List (ℕ → ℤ) → ℕ → ℤ
  | [] => oneCoefficient
  | a :: as => convolution a (productCoefficient as)

theorem convolution_cast {a b : ℕ → ℤ} {A B : PowerSeries ℂ}
    (ha : ∀ n, A.coeff n = (a n : ℂ)) (hb : ∀ n, B.coeff n = (b n : ℂ)) (n : ℕ) :
    (A * B).coeff n = (convolution a b n : ℂ) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [convolution, Int.cast_sum, Int.cast_mul, ha, hb]

theorem powCoefficient_cast {a : ℕ → ℤ} {A : PowerSeries ℂ}
    (ha : ∀ n, A.coeff n = (a n : ℂ)) (k n : ℕ) :
    (A ^ k).coeff n = (powCoefficient a k n : ℂ) := by
  induction k generalizing n with
  | zero => simp [powCoefficient, oneCoefficient, PowerSeries.coeff_one]
  | succ k ih =>
    rw [pow_succ', powCoefficient]
    exact convolution_cast ha ih n

theorem inverseCoefficient_cast {a : ℕ → ℤ} {A : PowerSeries ℂ}
    (ha : ∀ n, A.coeff n = (a n : ℂ)) (h0 : A.coeff 0 = 1) (n : ℕ) :
    A⁻¹.coeff n = (inverseCoefficient a n : ℂ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [PowerSeries.coeff_inv, ← PowerSeries.coeff_zero_eq_constantCoeff, h0,
      inverseCoefficient]
    split_ifs with hn
    · simp
    · simp only [inv_one, neg_one_mul, Int.cast_neg, Int.cast_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      split_ifs with hxn
      · simp only [Int.cast_mul, ha, ih x.2 hxn]
      · simp

theorem productCoefficient_cast {as : List (ℕ → ℤ)} {As : List (PowerSeries ℂ)}
    (h : List.Forall₂ (fun a A ↦ ∀ n, A.coeff n = (a n : ℂ)) as As) (n : ℕ) :
    As.prod.coeff n = (productCoefficient as n : ℂ) := by
  induction h generalizing n with
  | nil => simp [productCoefficient, oneCoefficient, PowerSeries.coeff_one]
  | cons ha hab ih =>
    simp only [List.prod_cons, productCoefficient]
    exact convolution_cast ha ih n

end WeightTwoCusps.EtaQuotient
