module

public import WeightTwoCusps.EtaQuotient.Criteria

/-! # Reducing arbitrary cusp denominators to divisor denominators -/

@[expose] public section

namespace WeightTwoCusps.EtaQuotient

/-- The arithmetic order sum depends on `c` only through `gcd(c,N)`. -/
theorem cuspSum_gcd_level (N : ℕ) (r : Fin N → ℤ) (c : ℕ) :
    cuspSum N r (Nat.gcd c N) = cuspSum N r c := by
  apply Finset.sum_congr rfl
  intro m hm
  rw [Nat.gcd_assoc, Nat.gcd_eq_right (Nat.dvd_of_mem_divisors hm)]

/-- The finite weak inequalities already cover every nonnegative integer denominator. -/
theorem holomorphicAtCusps_iff_all_denominators {N : ℕ} (hN : 0 < N) (r : Fin N → ℤ) :
    HolomorphicAtCusps N r ↔ ∀ c : ℕ, 0 ≤ cuspSum N r c := by
  constructor
  · intro h c
    have hc : Nat.gcd c N ∈ N.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right c N, hN.ne'⟩
    simpa only [cuspSum_gcd_level] using h (Nat.gcd c N) hc
  · intro h c _
    exact h c

/-- The same reduction applies to the strict inequalities for cusp forms. -/
theorem vanishingAtCusps_iff_all_denominators {N : ℕ} (hN : 0 < N) (r : Fin N → ℤ) :
    VanishingAtCusps N r ↔ ∀ c : ℕ, 0 < cuspSum N r c := by
  constructor
  · intro h c
    have hc : Nat.gcd c N ∈ N.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right c N, hN.ne'⟩
    simpa only [cuspSum_gcd_level] using h (Nat.gcd c N) hc
  · intro h c _
    exact h c

/-- The two usual denominators in Ligozat's formula agree at divisor cusps. -/
theorem gcd_sq_level {N c : ℕ} (hc : c ∈ N.divisors) :
    Nat.gcd (c ^ 2) N = c * Nat.gcd c (N / c) := by
  calc
    Nat.gcd (c ^ 2) N = Nat.gcd (c * c) (c * (N / c)) := by
      rw [pow_two, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hc)]
    _ = c * Nat.gcd c (N / c) := Nat.gcd_mul_left c c (N / c)

/-- The denominator underlying the natural cusp-width factor divides the level. -/
theorem cusp_denominator_dvd {N c : ℕ} (hc : c ∈ N.divisors) :
    c * Nat.gcd c (N / c) ∣ N := by
  obtain ⟨u, hu⟩ := Nat.gcd_dvd_right c (N / c)
  refine ⟨u, ?_⟩
  calc N = c * (N / c) := (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hc)).symm
    _ = c * (Nat.gcd c (N / c) * u) := congrArg (fun x : ℕ ↦ c * x) hu
    _ = (c * Nat.gcd c (N / c)) * u := by ring

/-- Ligozat's arithmetic formula in the alternate `gcd(c²,N)` normalization. -/
theorem cuspOrder_eq_gcd_sq {N c : ℕ} (hc : c ∈ N.divisors) (r : Fin N → ℤ) :
    cuspOrder N r c = (N : ℚ) / (24 * Nat.gcd (c ^ 2) N) * cuspSum N r c := by
  rw [cuspOrder, gcd_sq_level hc, Nat.cast_mul]
  rw [show (24 : ℚ) * Nat.gcd c (N / c) * c = 24 * ((c : ℚ) * Nat.gcd c (N / c)) by ring]

end WeightTwoCusps.EtaQuotient
