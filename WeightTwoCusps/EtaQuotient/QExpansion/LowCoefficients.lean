module

public import WeightTwoCusps.EtaQuotient.QExpansion.Computable

/-! # Symbolic formulas for the first coefficients of signed eta quotients -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open UpperHalfPlane

namespace WeightTwoCusps.EtaQuotient

private def logCoefficientTwo (A : PowerSeries ℂ) : ℂ := A.coeff 2 - A.coeff 1 ^ 2 / 2

private theorem coeff_two_mul (A B : PowerSeries ℂ) (hA : A.coeff 0 = 1)
    (hB : B.coeff 0 = 1) :
    (A * B).coeff 2 = A.coeff 2 + A.coeff 1 * B.coeff 1 + B.coeff 2 := by
  rw [PowerSeries.coeff_mul,
    show Finset.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} by decide]
  simp [hA, hB]
  ring

private theorem logCoefficientTwo_mul (A B : PowerSeries ℂ) (hA : A.coeff 0 = 1)
    (hB : B.coeff 0 = 1) :
    logCoefficientTwo (A * B) = logCoefficientTwo A + logCoefficientTwo B := by
  simp only [logCoefficientTwo, coeff_two_mul A B hA hB, PowerSeries.coeff_one_mul,
    ← PowerSeries.coeff_zero_eq_constantCoeff, hA, hB, mul_one]
  ring

private def eulerLogCoefficientTwo {m : ℕ} (hm : 0 < m) : ℤ →+ ℂ where
  toFun a := logCoefficientTwo (qExpansion 1 (eulerFactorPower m a))
  map_zero' := by simp [logCoefficientTwo]
  map_add' a b := by
    rw [qExpansion_eulerFactorPower_add hm]
    exact logCoefficientTwo_mul _ _ (eulerFactorPower_coeff_zero hm a)
      (eulerFactorPower_coeff_zero hm b)

private theorem euler_logCoefficientTwo_one {m : ℕ} (hm : 0 < m) :
    logCoefficientTwo (qExpansion 1 (eulerFactorPower m 1)) =
      if m = 1 then -(3 / 2 : ℂ) else if m = 2 then -1 else 0 := by
  have he2 : eulerCoefficient 2 = -1 := by decide +kernel
  rw [logCoefficientTwo, qExpansion_eulerFactor_coeff hm,
    qExpansion_eulerFactorPower_coeff_one hm]
  by_cases hm1 : m = 1
  · subst m
    norm_num [dilateCoefficient, he2]
  · by_cases hm2 : m = 2
    · subst m
      have he1 : eulerCoefficient 1 = -1 := by decide +kernel
      norm_num [dilateCoefficient, he1]
    · have hmd : ¬m ∣ 2 := by
        intro hd
        rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd with h | h
        · exact hm1 h
        · exact hm2 h
      simp [dilateCoefficient, hmd, hm1, hm2]

private theorem euler_logCoefficientTwo {m : ℕ} (hm : 0 < m) (a : ℤ) :
    logCoefficientTwo (qExpansion 1 (eulerFactorPower m a)) =
      if m = 1 then -(3 / 2 : ℂ) * (a : ℂ) else if m = 2 then -(a : ℂ) else 0 := by
  have h := (eulerLogCoefficientTwo hm).map_zsmul a (1 : ℤ)
  simp only [zsmul_eq_mul, mul_one] at h
  change logCoefficientTwo (qExpansion 1 (eulerFactorPower m a)) =
    (a : ℂ) * logCoefficientTwo (qExpansion 1 (eulerFactorPower m 1)) at h
  rw [h, euler_logCoefficientTwo_one hm]
  split_ifs <;> ring

private theorem logCoefficientTwo_prod {ι : Type*} (s : Finset ι)
    (f : ι → PowerSeries ℂ) (h0 : ∀ i ∈ s, (f i).coeff 0 = 1) :
    logCoefficientTwo (∏ i ∈ s, f i) = ∑ i ∈ s, logCoefficientTwo (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [logCoefficientTwo]
  | @insert a s ha ih =>
    have hs : ∀ i ∈ s, (f i).coeff 0 = 1 := fun i hi ↦ h0 i (Finset.mem_insert_of_mem hi)
    have hs0 : (∏ i ∈ s, f i).coeff 0 = 1 := by
      simp only [PowerSeries.coeff_zero_eq_constantCoeff, map_prod]
      exact Finset.prod_eq_one (fun i hi ↦ by
        simpa only [← PowerSeries.coeff_zero_eq_constantCoeff] using hs i hi)
    rw [Finset.prod_insert ha, logCoefficientTwo_mul _ _ (h0 a (Finset.mem_insert_self _ _)) hs0,
      ih hs, Finset.sum_insert ha]

/-- The exponent of a divisor factor, with zero at nondivisors. -/
def divisorExponent (N : ℕ) (r : Fin N → ℤ) (m : ℕ) : ℤ :=
  if m ∈ N.divisors then exponent r m else 0

/-- The second normalized coefficient, for arbitrary signed exponents.
The exponent at 2 contributes only when 2 divides the level. -/
theorem qExpansion_unitPart_coeff_two (N : ℕ) (r : Fin N → ℤ) :
    (qExpansion 1 (unitPart N r)).coeff 2 =
      (exponent r 1 : ℂ) * ((exponent r 1 : ℂ) - 3) / 2 - (divisorExponent N r 2 : ℂ) := by
  have hlog : logCoefficientTwo (qExpansion 1 (unitPart N r)) =
      ∑ m ∈ N.divisors, if m = 1 then -(3 / 2 : ℂ) * (exponent r m : ℂ)
        else if m = 2 then -(exponent r m : ℂ) else 0 := by
    change logCoefficientTwo (qExpansion 1 (fun z ↦ ∏ m ∈ N.divisors,
      eulerFactorPower m (exponent r m) z)) = _
    rw [qExpansion_prod _ _ (fun m hm ↦ eulerFactorPower_analytic (Nat.pos_of_mem_divisors hm) _),
      logCoefficientTwo_prod _ _
        (fun m hm ↦ eulerFactorPower_coeff_zero (Nat.pos_of_mem_divisors hm) _)]
    exact Finset.sum_congr rfl
      (fun m hm ↦ euler_logCoefficientTwo (Nat.pos_of_mem_divisors hm) _)
  have hsplit : (∑ m ∈ N.divisors, if m = 1 then -(3 / 2 : ℂ) * (exponent r m : ℂ)
        else if m = 2 then -(exponent r m : ℂ) else 0) =
      -(3 / 2 : ℂ) * (exponent r 1 : ℂ) - (divisorExponent N r 2 : ℂ) := by
    by_cases hN : N = 0
    · subst N
      simp [exponent, divisorExponent]
    · have h1 : 1 ∈ N.divisors := Nat.one_mem_divisors.mpr hN
      have heq (m : ℕ) :
          (if m = 1 then -(3 / 2 : ℂ) * (exponent r m : ℂ)
            else if m = 2 then -(exponent r m : ℂ) else 0) =
          (if m = 1 then -(3 / 2 : ℂ) * (exponent r m : ℂ) else 0) +
            (if m = 2 then -(exponent r m : ℂ) else 0) := by
        by_cases hm1 : m = 1 <;> by_cases hm2 : m = 2 <;> simp_all
      simp_rw [heq]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', h1, ite_true, divisorExponent, Int.cast_ite, Int.cast_zero]
      split_ifs <;> ring
  rw [hsplit, logCoefficientTwo, qExpansion_unitPart_coeff_one] at hlog
  linear_combination hlog

/-- The coefficient two places after the leading term. -/
theorem qExpansion_coeff_leading_add_two {N : ℕ} {r : Fin N → ℤ} {v : ℕ}
    (hv : infinitySum N r = 24 * (v : ℤ)) :
    (qExpansion 1 (etaQuotient N r)).coeff (v + 2) =
      (exponent r 1 : ℂ) * ((exponent r 1 : ℂ) - 3) / 2 - (divisorExponent N r 2 : ℂ) := by
  rw [qExpansion_eq_X_pow_mul hv, add_comm v 2, PowerSeries.coeff_X_pow_mul,
    qExpansion_unitPart_coeff_two]

end WeightTwoCusps.EtaQuotient
