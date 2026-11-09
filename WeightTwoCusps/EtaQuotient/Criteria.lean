module

public import WeightTwoCusps.EtaQuotient.Basic
public import Mathlib.Data.Rat.Sqrt

/-!
# Arithmetic data for the Newman–Ligozat criterion

These definitions state the classical arithmetic conditions. This file proves
arithmetic properties of the conditions, not the general modularity theorem.

References:
* D. Savitt, *An elementary proof of Newman's eta-quotient theorem*, Theorem 1.1
  and Remark 1.2, <https://math.jhu.edu/~savitt/papers/pdfs/newman.pdf>.
* G. Ligozat, *Courbes modulaires de genre 1*, Mémoires de la SMF 43 (1975),
  §3.2, <https://www.numdam.org/article/MSMF_1975__43__5_0.pdf>.
-/

@[expose] public section

open scoped BigOperators

namespace WeightTwoCusps.EtaQuotient

/-- Twenty-four times the unnormalized order at a cusp of denominator `c`. -/
def cuspSum (N : ℕ) (r : Fin N → ℤ) (c : ℕ) : ℚ :=
  ∑ m ∈ N.divisors, (Nat.gcd c m : ℚ) ^ 2 / m * exponent r m

/-- Ligozat's order with respect to the local parameter of `Γ₀(N)`.
For positive `c ∣ N`, the cusp width is `N / (c * gcd(c, N/c))`.
This is the arithmetic formula; identifying it with the analytic order is a
separate theorem, not assumed in this definition. -/
def cuspOrder (N : ℕ) (r : Fin N → ℤ) (c : ℕ) : ℚ :=
  (N : ℚ) / (24 * Nat.gcd c (N / c) * c) * cuspSum N r c

/-- Newman's two congruences, with a specified integral weight and positive level. -/
structure NewmanConditions (N : ℕ) (r : Fin N → ℤ) (k : ℤ) : Prop where
  level_pos : 0 < N
  weight : HasWeight N r k
  infinity_congruence : (24 : ℤ) ∣ infinitySum N r
  zero_congruence : (24 : ℤ) ∣ zeroSum N r

/-- The classical condition for trivial quadratic character: even weight and a
rational square `∏ m^rₘ`. Negative exponents are allowed. -/
def TrivialCharacter (N : ℕ) (r : Fin N → ℤ) (k : ℤ) : Prop :=
  Even k ∧ IsSquare (characterProduct N r)
deriving Decidable

/-- The finite list of weak inequalities required for holomorphy at the cusps. -/
def HolomorphicAtCusps (N : ℕ) (r : Fin N → ℤ) : Prop :=
  ∀ c ∈ N.divisors, 0 ≤ cuspSum N r c
deriving Decidable

/-- Strict Ligozat inequalities, required for a cusp form. -/
def VanishingAtCusps (N : ℕ) (r : Fin N → ℤ) : Prop :=
  ∀ c ∈ N.divisors, 0 < cuspSum N r c
deriving Decidable

/-- The arithmetic Newman–Ligozat conditions for a form with trivial character.
They suffice for `etaQuotientMF`; the unrestricted converse remains open here. -/
structure NewmanLigozatConditions (N : ℕ) (r : Fin N → ℤ) (k : ℤ) : Prop
    extends NewmanConditions N r k where
  trivial_character : TrivialCharacter N r k
  holomorphic_cusps : HolomorphicAtCusps N r

instance (N : ℕ) (r : Fin N → ℤ) (k : ℤ) : Decidable (NewmanConditions N r k) :=
  decidable_of_iff (0 < N ∧ exponentSum N r = 2 * k ∧
      (24 : ℤ) ∣ infinitySum N r ∧ (24 : ℤ) ∣ zeroSum N r)
    ⟨fun ⟨hN, hk, hi, hz⟩ ↦ ⟨hN, hk, hi, hz⟩,
      fun h ↦ ⟨h.level_pos, h.weight, h.infinity_congruence, h.zero_congruence⟩⟩

instance (N : ℕ) (r : Fin N → ℤ) (k : ℤ) : Decidable (NewmanLigozatConditions N r k) :=
  decidable_of_iff (NewmanConditions N r k ∧ TrivialCharacter N r k ∧
      HolomorphicAtCusps N r)
    ⟨fun ⟨h, ht, hc⟩ ↦ ⟨h, ht, hc⟩,
      fun h ↦ ⟨h.toNewmanConditions, h.trivial_character, h.holomorphic_cusps⟩⟩

theorem vanishing_implies_holomorphic {N : ℕ} {r : Fin N → ℤ}
    (h : VanishingAtCusps N r) : HolomorphicAtCusps N r :=
  fun c hc ↦ (h c hc).le

theorem cuspOrder_nonneg_iff {N c : ℕ} (hN : 0 < N) (hc : c ∈ N.divisors)
    (r : Fin N → ℤ) : 0 ≤ cuspOrder N r c ↔ 0 ≤ cuspSum N r c := by
  have hcpos := Nat.pos_of_mem_divisors hc
  have hg : 0 < Nat.gcd c (N / c) := Nat.gcd_pos_of_pos_left _ hcpos
  have hp : (0 : ℚ) < (N : ℚ) / (24 * Nat.gcd c (N / c) * c) := by positivity
  exact mul_nonneg_iff_of_pos_left hp

theorem cuspOrder_pos_iff {N c : ℕ} (hN : 0 < N) (hc : c ∈ N.divisors)
    (r : Fin N → ℤ) : 0 < cuspOrder N r c ↔ 0 < cuspSum N r c := by
  have hcpos := Nat.pos_of_mem_divisors hc
  have hg : 0 < Nat.gcd c (N / c) := Nat.gcd_pos_of_pos_left _ hcpos
  have hp : (0 : ℚ) < (N : ℚ) / (24 * Nat.gcd c (N / c) * c) := by positivity
  exact mul_pos_iff_of_pos_left hp

/-- The cusp represented by `1/N` is the infinity cusp. -/
theorem cuspSum_level (N : ℕ) (r : Fin N → ℤ) :
    cuspSum N r N = (infinitySum N r : ℚ) := by
  rw [cuspSum, infinitySum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Nat.gcd_eq_right (Nat.dvd_of_mem_divisors hm)]
  push_cast
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hm).ne'
  field_simp

theorem cuspOrder_level {N : ℕ} (hN : 0 < N) (r : Fin N → ℤ) :
    cuspOrder N r N = (infinitySum N r : ℚ) / 24 := by
  rw [cuspOrder, Nat.div_self hN, Nat.gcd_one_right, cuspSum_level]
  have hN0 : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  simp

theorem cuspOrder_one {N : ℕ} (_hN : 0 < N) (r : Fin N → ℤ) :
    cuspOrder N r 1 = (zeroSum N r : ℚ) / 24 := by
  simp only [cuspOrder, cuspSum, Nat.gcd_one_left, Nat.cast_one, one_pow,
    mul_one, zeroSum, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  have he : (N / m : ℕ) * m = N := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hm)
  have he' : ((N / m : ℕ) : ℚ) * m = N := by exact_mod_cast he
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hm).ne'
  field_simp
  linear_combination -(exponent r m : ℚ) * he'

theorem holomorphicAtCusps_of_nonneg {N : ℕ} {r : Fin N → ℤ}
    (h : ∀ m ∈ N.divisors, 0 ≤ exponent r m) : HolomorphicAtCusps N r := by
  intro c hc
  apply Finset.sum_nonneg
  intro m hm
  exact mul_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) (by exact_mod_cast h m hm)

/-- Both endpoint inequalities are necessary parts of the finite Ligozat conditions. -/
theorem infinitySum_nonneg {N : ℕ} (hN : 0 < N) {r : Fin N → ℤ}
    (h : HolomorphicAtCusps N r) : 0 ≤ infinitySum N r := by
  have hi := h N (Nat.mem_divisors_self N hN.ne')
  rw [cuspSum_level] at hi
  exact_mod_cast hi

theorem zeroSum_nonneg {N : ℕ} (hN : 0 < N) {r : Fin N → ℤ}
    (h : HolomorphicAtCusps N r) : 0 ≤ zeroSum N r := by
  have hc : 1 ∈ N.divisors := Nat.one_mem_divisors.mpr hN.ne'
  have hi := (cuspOrder_nonneg_iff hN hc r).mpr (h 1 hc)
  rw [cuspOrder_one hN] at hi
  have hq : (0 : ℚ) ≤ zeroSum N r := by linarith
  exact_mod_cast hq

/-- At prime level Ligozat's finite inequalities are exactly the two endpoint inequalities. -/
theorem holomorphicAtCusps_prime_iff {p : ℕ} (hp : p.Prime) (r : Fin p → ℤ) :
    HolomorphicAtCusps p r ↔ 0 ≤ infinitySum p r ∧ 0 ≤ zeroSum p r := by
  refine ⟨fun h ↦ ⟨infinitySum_nonneg hp.pos h, zeroSum_nonneg hp.pos h⟩, ?_⟩
  rintro ⟨hInfty, hzero⟩ c hc
  have hd := (Nat.mem_divisors.mp hc).1
  rcases (Nat.dvd_prime hp).mp hd with rfl | rfl
  · apply (cuspOrder_nonneg_iff hp.pos hc r).mp
    rw [cuspOrder_one hp.pos]
    exact div_nonneg (by exact_mod_cast hzero) (by norm_num)
  · rw [cuspSum_level]
    exact_mod_cast hInfty

/-- Doubling exponents always gives a rational square in the character product. -/
theorem characterProduct_double_isSquare (N : ℕ) (r : Fin N → ℤ) :
    IsSquare (characterProduct N (double r)) := by
  refine ⟨characterProduct N r, ?_⟩
  simp only [characterProduct, exponent_double, ← sq, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro m hm
  rw [mul_comm (2 : ℤ), zpow_mul, zpow_ofNat]

end WeightTwoCusps.EtaQuotient
