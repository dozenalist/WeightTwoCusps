module

public import WeightTwoCusps.EtaQuotient.QExpansion.Euler
public import WeightTwoCusps.EtaQuotient.QExpansion.Sequence
public import Mathlib.Data.List.Forall2

/-!
# Integer coefficients of signed eta quotients

Euler's pentagonal series, finite Cauchy products, and reciprocal recursion
give a computable formula for every coefficient. The bridge to the analytic
q-expansion uses only the nonnegative integral infinity order; modularity
and the Newman--Ligozat criterion are not needed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open UpperHalfPlane

namespace WeightTwoCusps.EtaQuotient

theorem qExpansion_eulerFactorPower_add {m : ℕ} (hm : 0 < m) (a b : ℤ) :
    qExpansion 1 (eulerFactorPower m (a + b)) =
      qExpansion 1 (eulerFactorPower m a) * qExpansion 1 (eulerFactorPower m b) := by
  have heq : eulerFactorPower m (a + b) = eulerFactorPower m a * eulerFactorPower m b := by
    ext z
    exact zpow_add₀ (eulerFactor_ne_zero hm z) a b
  rw [heq, UpperHalfPlane.qExpansion_mul (eulerFactorPower_analytic hm a)
    (eulerFactorPower_analytic hm b)]

@[simp] theorem qExpansion_eulerFactorPower_zero (m : ℕ) :
    qExpansion 1 (eulerFactorPower m 0) = 1 := by
  rw [show eulerFactorPower m 0 = (1 : ℍ → ℂ) by ext z; simp [eulerFactorPower],
    UpperHalfPlane.qExpansion_one]

theorem qExpansion_eulerFactorPower_nat {m : ℕ} (hm : 0 < m) (k : ℕ) :
    qExpansion 1 (eulerFactorPower m (k : ℤ)) =
      qExpansion 1 (eulerFactorPower m 1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, qExpansion_eulerFactorPower_add hm, ih, pow_succ]

theorem qExpansion_eulerFactorPower_neg {m : ℕ} (hm : 0 < m) (a : ℤ) :
    qExpansion 1 (eulerFactorPower m (-a)) =
      (qExpansion 1 (eulerFactorPower m a))⁻¹ := by
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, eulerFactorPower_coeff_zero hm]
    exact one_ne_zero)).mpr
  rw [← qExpansion_eulerFactorPower_add hm, neg_add_cancel,
    qExpansion_eulerFactorPower_zero]

/-- All coefficients of a signed normalized eta factor are computable integers. -/
theorem qExpansion_eulerFactorPower_coeff {m : ℕ} (hm : 0 < m) (a : ℤ) (n : ℕ) :
    (qExpansion 1 (eulerFactorPower m a)).coeff n =
      (zpowCoefficient (dilateCoefficient m eulerCoefficient) a n : ℂ) := by
  cases a with
  | ofNat k =>
    change (qExpansion 1 (eulerFactorPower m (k : ℤ))).coeff n = _
    rw [qExpansion_eulerFactorPower_nat hm]
    exact powCoefficient_cast (qExpansion_eulerFactor_coeff hm) k n
  | negSucc k =>
    change (qExpansion 1 (eulerFactorPower m (-((k + 1 : ℕ) : ℤ)))).coeff n = _
    rw [qExpansion_eulerFactorPower_neg hm, qExpansion_eulerFactorPower_nat hm,
      ← PowerSeries.inv_pow]
    exact powCoefficient_cast (inverseCoefficient_cast (qExpansion_eulerFactor_coeff hm)
      (eulerFactorPower_coeff_zero hm 1)) (k + 1) n

end WeightTwoCusps.EtaQuotient

end

namespace WeightTwoCusps.EtaQuotient

/-- The positive divisors in increasing order, with an exposed finite algorithm. -/
def divisorList (N : ℕ) : List ℕ :=
  if N = 0 then [] else (List.range (N + 1)).filter fun m ↦ N % m = 0

/-- Integer coefficients of the normalized Euler unit of an eta quotient. -/
def unitCoefficient (N : ℕ) (r : Fin N → ℤ) : ℕ → ℤ :=
  productCoefficient ((divisorList N).map fun m ↦
    zpowCoefficient (dilateCoefficient m eulerCoefficient) (exponent r m))

/-- The integer infinity order, used when the weighted exponent sum is
nonnegative and divisible by 24. -/
def infinityOrder (N : ℕ) (r : Fin N → ℤ) : ℕ := (infinitySum N r / 24).toNat

/-- Computable coefficient formula, including the initial shift by the infinity order.
Its agreement with the analytic expansion requires the hypotheses in
`qExpansion_coeff_eq_coefficient`. -/
def coefficient (N : ℕ) (r : Fin N → ℤ) (n : ℕ) : ℤ :=
  if infinityOrder N r ≤ n then unitCoefficient N r (n - infinityOrder N r) else 0

noncomputable section

set_option backward.isDefEq.respectTransparency false

open UpperHalfPlane

@[simp] theorem mem_divisorList {N m : ℕ} : m ∈ divisorList N ↔ m ∈ N.divisors := by
  by_cases hN : N = 0
  · simp [divisorList, hN]
  · simp only [divisorList, hN, ite_false, List.mem_filter, List.mem_range,
      decide_eq_true_eq, Nat.mem_divisors, Nat.dvd_iff_mod_eq_zero]
    constructor
    · rintro ⟨_, hm⟩
      exact ⟨hm, hN⟩
    · rintro ⟨hm, _⟩
      exact ⟨Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hN)
        (Nat.dvd_of_mod_eq_zero hm)), hm⟩

@[simp] theorem divisorList_toFinset (N : ℕ) : (divisorList N).toFinset = N.divisors := by
  ext m
  simp

theorem divisorList_nodup (N : ℕ) : (divisorList N).Nodup := by
  unfold divisorList
  split_ifs
  · exact List.nodup_nil
  · exact List.nodup_range.filter _

/-- The finite coefficient algorithm agrees with the analytic Euler-unit expansion. -/
theorem qExpansion_unitPart_coeff (N : ℕ) (r : Fin N → ℤ) (n : ℕ) :
    (qExpansion 1 (unitPart N r)).coeff n = (unitCoefficient N r n : ℂ) := by
  change (qExpansion 1 (fun z ↦ ∏ m ∈ N.divisors,
    eulerFactorPower m (exponent r m) z)).coeff n = _
  rw [qExpansion_prod _ _ (fun m hm ↦ eulerFactorPower_analytic (Nat.pos_of_mem_divisors hm) _)]
  have h := productCoefficient_cast (as := (divisorList N).map fun m ↦
      zpowCoefficient (dilateCoefficient m eulerCoefficient) (exponent r m))
    (As := (divisorList N).map fun m ↦ qExpansion 1 (eulerFactorPower m (exponent r m)))
    (by
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
      intro m hm j
      exact qExpansion_eulerFactorPower_coeff (Nat.pos_of_mem_divisors (by simpa using hm)) _ j) n
  rw [← List.prod_toFinset _ (divisorList_nodup N), divisorList_toFinset] at h
  exact h

/-- A coefficient at or above the infinity order is a shifted Euler-unit coefficient. -/
theorem qExpansion_coeff_add {N : ℕ} {r : Fin N → ℤ} {v : ℕ}
    (hv : infinitySum N r = 24 * (v : ℤ)) (n : ℕ) :
    (qExpansion 1 (etaQuotient N r)).coeff (v + n) = (unitCoefficient N r n : ℂ) := by
  rw [qExpansion_eq_X_pow_mul hv, add_comm v n, PowerSeries.coeff_X_pow_mul,
    qExpansion_unitPart_coeff]

/-- Every coefficient is given by a finite integer computation, for signed exponents. -/
theorem qExpansion_coeff_eq_coefficient {N : ℕ} {r : Fin N → ℤ}
    (hi : (24 : ℤ) ∣ infinitySum N r) (h0 : 0 ≤ infinitySum N r) (n : ℕ) :
    (qExpansion 1 (etaQuotient N r)).coeff n = (coefficient N r n : ℂ) := by
  have hv := infinitySum_eq_twentyFour_mul_order hi h0
  rw [qExpansion_eq_X_pow_mul hv, PowerSeries.coeff_X_pow_mul', coefficient, infinityOrder]
  split_ifs with hn
  · exact qExpansion_unitPart_coeff N r _
  · simp

/-- In particular every analytic coefficient is an integer. -/
theorem qExpansion_coeff_integral {N : ℕ} {r : Fin N → ℤ}
    (hi : (24 : ℤ) ∣ infinitySum N r) (h0 : 0 ≤ infinitySum N r) (n : ℕ) :
    ∃ a : ℤ, (qExpansion 1 (etaQuotient N r)).coeff n = (a : ℂ) :=
  ⟨coefficient N r n, qExpansion_coeff_eq_coefficient hi h0 n⟩

end

end WeightTwoCusps.EtaQuotient
