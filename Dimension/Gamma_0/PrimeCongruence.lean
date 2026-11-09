module

public import Dimension.Gamma_0.Prime
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.FieldTheory.Finite.Basic

/-! # The explicit prime-level formula for `p ≡ 11 (mod 12)` -/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

theorem no_elliptic_two_roots_of_mod_four_eq_three (p : ℕ) [Fact p.Prime]
    (hp : p % 4 = 3) : ∀ a : ZMod p, a ^ 2 + 1 ≠ 0 := by
  intro a ha
  have hs : a ^ 2 = -1 := eq_neg_of_add_eq_zero_left ha
  exact (ZMod.mod_four_ne_three_of_sq_eq_neg_one hs) hp

theorem no_elliptic_three_roots_of_mod_three_eq_two (p : ℕ) [Fact p.Prime]
    (hp : p % 3 = 2) : ∀ a : ZMod p, a ^ 2 + a + 1 ≠ 0 := by
  intro a ha
  have ha0 : a ≠ 0 := by
    intro hz
    simpa [hz] using ha
  have ha3 : a ^ 3 = 1 := by linear_combination (a - 1) * ha
  have hd : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one ha3
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
  · have hone : a = 1 := orderOf_eq_one_iff.mp h1
    rw [hone] at ha
    norm_num at ha
    have hpdiv : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp ha
    rcases (Nat.dvd_prime Nat.prime_three).mp hpdiv with h | h <;> omega
  · have hdiv := ZMod.orderOf_dvd_card_sub_one ha0
    rw [h3] at hdiv
    have hm := Nat.mod_eq_zero_of_dvd hdiv
    have hpp : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega

/-- A uniform explicit dimension formula on a congruence class of prime levels. -/
theorem gamma0CuspForms_dimension_formula_prime_mod_twelve_eq_eleven
    (p : ℕ) [Fact p.Prime] (hp : p % 12 = 11) :
    (Module.finrank ℂ (gamma0CuspForms p) : ℚ) = ((p : ℚ) + 1) / 12 := by
  apply gamma0CuspForms_dimension_formula_prime_of_no_roots
  · exact no_elliptic_two_roots_of_mod_four_eq_three p (by omega)
  · exact no_elliptic_three_roots_of_mod_three_eq_two p (by omega)

end WeightTwoCusps
