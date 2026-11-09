module

public import Dimension.Gamma_0.ProjectiveIndex
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Nat.Factorization.Basic

@[expose] public section

/-!
# Arithmetic terms in the weight-two `Γ₀(N)` formula

The two root counts and the divisor sum below are the classical elliptic and
cusp corrections. Identifying them with the geometric counts, and establishing
the analytic dimension relation, are separate mathematical steps.
-/

namespace WeightTwoCusps

/-- The number of roots of `x² + 1` modulo `N`, using natural representatives. -/
def gamma0EllipticTwoCount (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun a => (a ^ 2 + 1) % N = 0).card

/-- The number of roots of `x² + x + 1` modulo `N`. -/
def gamma0EllipticThreeCount (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun a => (a ^ 2 + a + 1) % N = 0).card

theorem gamma0EllipticTwoCount_eq_zero_of_no_roots (N : ℕ)
    (h : ∀ a : ZMod N, a ^ 2 + 1 ≠ 0) : gamma0EllipticTwoCount N = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  apply h a
  have ha' := (Finset.mem_filter.mp ha).2
  rw [← Nat.cast_pow, ← Nat.cast_one, ← Nat.cast_add, ZMod.natCast_eq_zero_iff]
  exact Nat.dvd_of_mod_eq_zero ha'

theorem gamma0EllipticThreeCount_eq_zero_of_no_roots (N : ℕ)
    (h : ∀ a : ZMod N, a ^ 2 + a + 1 ≠ 0) : gamma0EllipticThreeCount N = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  apply h a
  have ha' := (Finset.mem_filter.mp ha).2
  rw [← Nat.cast_pow, ← Nat.cast_add, ← Nat.cast_one, ← Nat.cast_add,
    ZMod.natCast_eq_zero_iff]
  exact Nat.dvd_of_mod_eq_zero ha'

/-- The divisor sum in the classical `Γ₀(N)` cusp count. -/
def gamma0CuspCount (N : ℕ) : ℕ :=
  ∑ d ∈ N.divisors, Nat.totient (Nat.gcd d (N / d))

/-- The rational arithmetic expression expected for `dim S₂(Γ₀(N))`.
This definition does not assert its equality with the analytic dimension. -/
noncomputable def gamma0Dimension (N : ℕ) : ℚ :=
  1 + CongruenceIndex.psi N / 12 - (gamma0EllipticTwoCount N : ℚ) / 4 -
    (gamma0EllipticThreeCount N : ℚ) / 3 - (gamma0CuspCount N : ℚ) / 2

/-- Solving the integral genus relation avoids natural-number subtraction. -/
lemma gamma0_dimension_rat_of_relation {d μ e₂ e₃ c : ℕ}
    (h : 12 * d + 3 * e₂ + 4 * e₃ + 6 * c = 12 + μ) :
    (d : ℚ) = 1 + (μ : ℚ) / 12 - (e₂ : ℚ) / 4 - (e₃ : ℚ) / 3 - (c : ℚ) / 2 := by
  have hq : (12 : ℚ) * d + 3 * e₂ + 4 * e₃ + 6 * c = 12 + μ := by
    exact_mod_cast h
  linarith

end WeightTwoCusps
