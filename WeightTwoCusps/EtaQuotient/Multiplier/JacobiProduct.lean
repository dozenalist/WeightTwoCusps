module

public import WeightTwoCusps.EtaQuotient.Basic
public import WeightTwoCusps.EtaQuotient.Multiplier.JacobiSymbol
public import Mathlib.Data.Rat.Lemmas

/-!
# Rational squares and products of quadratic symbols

Negative eta exponents cause no difficulty for the square condition: splitting
each exponent into its parity and twice an integer reduces the rational
character product to a natural number times a rational square.
-/

@[expose] public section

open scoped BigOperators

namespace WeightTwoCusps.EtaQuotient

private theorem zpow_parity_factorization {G : Type*} [CommGroupWithZero G]
    (x : G) (hx : x ≠ 0) (e : ℤ) :
    x ^ e = x ^ (e % 2).toNat * (x ^ (e / 2)) ^ 2 := by
  have he : ((e % 2).toNat : ℤ) + e / 2 * 2 = e := by
    have hh := Int.emod_nonneg e (by norm_num : (2 : ℤ) ≠ 0)
    omega
  rw [← zpow_natCast, ← zpow_natCast (x ^ (e / 2)) 2, ← zpow_mul,
    ← zpow_add₀ hx]
  change x ^ e = x ^ (((e % 2).toNat : ℤ) + e / 2 * 2)
  rw [he]

private theorem zpow_eq_pow_parity_of_sq_eq_one {G : Type*} [CommGroupWithZero G]
    (x : G) (hx : x ≠ 0) (hs : x ^ 2 = 1) (e : ℤ) :
    x ^ e = x ^ (e % 2).toNat := by
  rw [zpow_parity_factorization x hx e]
  have hsq : (x ^ (e / 2)) ^ 2 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm (e / 2), zpow_mul,
      zpow_natCast, hs, one_zpow]
  rw [hsq, mul_one]

/-- Clearing the even parts of signed exponents leaves a square natural
product whenever the original rational product is a square. -/
theorem isSquare_parityProduct_of_isSquare (s : Finset ℕ) (r : ℕ → ℤ)
    (hpos : ∀ m ∈ s, 0 < m)
    (hs : IsSquare (∏ m ∈ s, (m : ℚ) ^ r m)) :
    IsSquare (∏ m ∈ s, m ^ (r m % 2).toNat) := by
  let P : ℕ := ∏ m ∈ s, m ^ (r m % 2).toNat
  let Q : ℚ := ∏ m ∈ s, (m : ℚ) ^ (r m / 2)
  have hQ : Q ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro m hm
    exact zpow_ne_zero _ (by exact_mod_cast (hpos m hm).ne')
  have hfac : (∏ m ∈ s, (m : ℚ) ^ r m) = (P : ℚ) * Q ^ 2 := by
    simp only [P, Q, Nat.cast_prod, Nat.cast_pow, ← Finset.prod_pow,
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro m hm
    exact zpow_parity_factorization _ (by exact_mod_cast (hpos m hm).ne') _
  apply Rat.isSquare_natCast_iff.mp
  have hdiv := hs.div (show IsSquare (Q ^ 2) from ⟨Q, by simp [pow_two]⟩)
  rw [hfac] at hdiv
  simpa only [mul_div_assoc, div_self (pow_ne_zero 2 hQ), mul_one] using hdiv

/-- A square rational product of positive natural bases has trivial Jacobi
product, allowing arbitrary signed integer exponents. -/
theorem prod_jacobiSym_zpow_eq_one_of_isSquare (s : Finset ℕ) (r : ℕ → ℤ) (d : ℕ)
    (hpos : ∀ m ∈ s, 0 < m)
    (hcop : ∀ m ∈ s, (m : ℤ).gcd d = 1)
    (hs : IsSquare (∏ m ∈ s, (m : ℚ) ^ r m)) :
    (∏ m ∈ s, (jacobiSym m d : ℂ) ^ r m) = 1 := by
  let J : ℕ →* ℤ := {
    toFun := fun m ↦ jacobiSym m d
    map_one' := jacobiSym.one_left d
    map_mul' := fun m n ↦ by simp only [Nat.cast_mul, jacobiSym.mul_left] }
  let P : ℕ := ∏ m ∈ s, m ^ (r m % 2).toNat
  have hJP : J P = ∏ m ∈ s, jacobiSym m d ^ (r m % 2).toNat := by
    simp only [P, map_prod, map_pow]
    rfl
  have hJP0 : J P ≠ 0 := by
    rw [hJP]
    apply Finset.prod_ne_zero_iff.mpr
    intro m hm
    exact pow_ne_zero _ (jacobiSym.ne_zero (hcop m hm))
  have hPsq : IsSquare P := isSquare_parityProduct_of_isSquare s r hpos hs
  obtain ⟨t, ht⟩ := hPsq
  have hJP1 : J P = 1 := by
    rw [ht, map_mul]
    rcases jacobiSym.trichotomy t d with h | h | h
    · have hz : J P = 0 := by rw [ht, map_mul]; change jacobiSym t d * jacobiSym t d = 0; simp [h]
      exact (hJP0 hz).elim
    · change jacobiSym t d * jacobiSym t d = 1
      simp [h]
    · change jacobiSym t d * jacobiSym t d = 1
      simp [h]
  calc
    (∏ m ∈ s, (jacobiSym m d : ℂ) ^ r m) =
        ∏ m ∈ s, (jacobiSym m d : ℂ) ^ (r m % 2).toNat := by
      apply Finset.prod_congr rfl
      intro m hm
      exact zpow_eq_pow_parity_of_sq_eq_one _
        (by exact_mod_cast jacobiSym.ne_zero (hcop m hm))
        (by exact_mod_cast jacobiSym.sq_one (hcop m hm)) _
    _ = (J P : ℂ) := by rw [hJP]; push_cast; rfl
    _ = 1 := by rw [hJP1]; norm_num

/-- The rational-square condition kills the quadratic factor in the
eta-quotient multiplier. Natural divisor numerators also cover negative
odd denominators through the signed Jacobi convention. -/
theorem prod_extendedJacobi_zpow_eq_one_of_isSquare (N : ℕ) (r : Fin N → ℤ) (d : ℤ)
    (hcop : Int.gcd (N : ℤ) d = 1) (hs : IsSquare (characterProduct N r)) :
    (∏ m ∈ N.divisors, (extendedJacobi m d : ℂ) ^ exponent r m) = 1 := by
  simp_rw [extendedJacobi.of_nonneg_left (Nat.cast_nonneg _)]
  apply prod_jacobiSym_zpow_eq_one_of_isSquare N.divisors (exponent r) d.natAbs
    (fun m hm ↦ Nat.pos_of_mem_divisors hm) ?_ hs
  intro m hm
  have h := (Int.isCoprime_iff_gcd_eq_one.mpr hcop).of_isCoprime_of_dvd_left
    (by exact_mod_cast Nat.dvd_of_mem_divisors hm : (m : ℤ) ∣ N)
  simpa only [Int.gcd, Int.natAbs_natCast] using Int.isCoprime_iff_gcd_eq_one.mp h

end WeightTwoCusps.EtaQuotient
