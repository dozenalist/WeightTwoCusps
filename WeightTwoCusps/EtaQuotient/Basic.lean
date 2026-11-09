module

public import WeightTwoCusps.Eta.Basic
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# Eta quotients with integer exponents

The function `r : Fin N → ℤ` assigns its entry `i` to `η((i + 1)z)`.
Only divisors of `N` occur in the product; other entries are ignored.
Integer powers allow negative exponents, and eta has no zeros on `ℍ`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Complex UpperHalfPlane
open scoped Topology Manifold ModularForm MatrixGroups

namespace WeightTwoCusps

namespace EtaQuotient

/-- The exponent belonging to `η(mz)`, extended by zero outside `1, …, N`. -/
def exponent {N : ℕ} (r : Fin N → ℤ) (m : ℕ) : ℤ :=
  if h : 0 < m ∧ m ≤ N then r ⟨m - 1, by omega⟩ else 0

@[simp] theorem exponent_succ {N : ℕ} (r : Fin N → ℤ) (i : Fin N) :
    exponent r (i.val + 1) = r i := by
  simp [exponent, i.isLt]

theorem exponent_of_mem_divisors {N m : ℕ} (r : Fin N → ℤ) (hm : m ∈ N.divisors) :
    exponent r m = r ⟨m - 1, by
      have := Nat.pos_of_mem_divisors hm
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisors hm))
        (Nat.dvd_of_mem_divisors hm)
      omega⟩ := by
  simp [exponent, Nat.pos_of_mem_divisors hm,
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisors hm))
      (Nat.dvd_of_mem_divisors hm)]

/-- The sum of the exponents, twice the expected weight. -/
def exponentSum (N : ℕ) (r : Fin N → ℤ) : ℤ := ∑ m ∈ N.divisors, exponent r m

/-- The weighted exponent sum controlling translation at infinity. -/
def infinitySum (N : ℕ) (r : Fin N → ℤ) : ℤ := ∑ m ∈ N.divisors, (m : ℤ) * exponent r m

/-- The weighted exponent sum at the cusp zero. -/
def zeroSum (N : ℕ) (r : Fin N → ℤ) : ℤ := ∑ m ∈ N.divisors, ((N / m : ℕ) : ℤ) * exponent r m

/-- Having integral weight `k` means that the exponent sum is `2k`. -/
def HasWeight (N : ℕ) (r : Fin N → ℤ) (k : ℤ) : Prop := exponentSum N r = 2 * k

/-- Double every exponent, representing the square of an eta quotient. -/
def double {N : ℕ} (r : Fin N → ℤ) : Fin N → ℤ := fun i ↦ 2 * r i

@[simp] theorem exponent_double {N : ℕ} (r : Fin N → ℤ) (m : ℕ) :
    exponent (double r) m = 2 * exponent r m := by
  unfold exponent double
  split <;> simp

@[simp] theorem exponentSum_double (N : ℕ) (r : Fin N → ℤ) :
    exponentSum N (double r) = 2 * exponentSum N r := by
  simp [exponentSum, Finset.mul_sum]

@[simp] theorem infinitySum_double (N : ℕ) (r : Fin N → ℤ) :
    infinitySum N (double r) = 2 * infinitySum N r := by
  simp only [infinitySum, exponent_double, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  ring

@[simp] theorem zeroSum_double (N : ℕ) (r : Fin N → ℤ) :
    zeroSum N (double r) = 2 * zeroSum N r := by
  simp only [zeroSum, exponent_double, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- The positive rational number in the quadratic Nebentypus character. -/
def characterProduct (N : ℕ) (r : Fin N → ℤ) : ℚ :=
  ∏ m ∈ N.divisors, (m : ℚ) ^ exponent r m

end EtaQuotient

/-- The eta quotient `∏_{0 < m ∣ N} η(mz)^(r_m)`, with integer exponents. -/
def etaQuotient (N : ℕ) (r : Fin N → ℤ) (z : ℍ) : ℂ :=
  ∏ m ∈ N.divisors, ModularForm.eta ((m : ℂ) * (z : ℂ)) ^ EtaQuotient.exponent r m

namespace EtaQuotient

@[simp] theorem level_zero (r : Fin 0 → ℤ) (z : ℍ) : etaQuotient 0 r z = 1 := by
  simp [etaQuotient]

@[simp] theorem zero_exponents (N : ℕ) (z : ℍ) : etaQuotient N 0 z = 1 := by
  simp [etaQuotient, exponent]

@[simp] theorem level_one (r : Fin 1 → ℤ) (z : ℍ) :
    etaQuotient 1 r z = ModularForm.eta z ^ exponent r 1 := by
  simp [etaQuotient]

/-- Every factor of an eta quotient is nonzero on the upper half-plane. -/
theorem factor_ne_zero {N m : ℕ} (hm : m ∈ N.divisors) (z : ℍ) :
    ModularForm.eta ((m : ℂ) * (z : ℂ)) ≠ 0 := by
  apply ModularForm.eta_ne_zero
  simpa using mul_pos (show (0 : ℝ) < m by exact_mod_cast Nat.pos_of_mem_divisors hm) z.im_pos

theorem ne_zero (N : ℕ) (r : Fin N → ℤ) (z : ℍ) : etaQuotient N r z ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr fun m hm ↦ zpow_ne_zero _ (factor_ne_zero hm z)

@[simp] theorem double_apply (N : ℕ) (r : Fin N → ℤ) (z : ℍ) :
    etaQuotient N (double r) z = etaQuotient N r z ^ 2 := by
  simp only [etaQuotient, exponent_double, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro m hm
  rw [mul_comm (2 : ℤ), zpow_mul, zpow_ofNat]

/-- Arbitrary integer exponents preserve holomorphy, since eta never vanishes. -/
theorem holo (N : ℕ) (r : Fin N → ℤ) : MDiff (etaQuotient N r) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine DifferentiableOn.congr (f := fun z : ℂ ↦
    ∏ m ∈ N.divisors, ModularForm.eta ((m : ℂ) * z) ^ exponent r m) ?_ ?_
  · apply DifferentiableOn.fun_finsetProd
    intro m hm z hz
    have hpos : 0 < (((m : ℂ) * z).im) := by
      simpa using mul_pos (show (0 : ℝ) < m by exact_mod_cast Nat.pos_of_mem_divisors hm) hz
    exact (((ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hpos).comp z
      ((differentiableAt_const (m : ℂ)).mul differentiableAt_id)).zpow
        (Or.inl (ModularForm.eta_ne_zero hpos))).differentiableWithinAt
  · intro z hz
    simp [etaQuotient, UpperHalfPlane.ofComplex_apply_of_im_pos hz]

/-- Pointwise multiplication adds the exponent functions. -/
theorem mul_of_exponent_add (N : ℕ) (r s t : Fin N → ℤ)
    (h : ∀ m ∈ N.divisors, exponent t m = exponent r m + exponent s m) (z : ℍ) :
    etaQuotient N t z = etaQuotient N r z * etaQuotient N s z := by
  rw [etaQuotient, etaQuotient, etaQuotient, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro m hm
  rw [h m hm, zpow_add₀ (factor_ne_zero hm z)]

theorem characterProduct_pos (N : ℕ) (r : Fin N → ℤ) : 0 < characterProduct N r := by
  apply Finset.prod_pos
  intro m hm
  exact zpow_pos (by exact_mod_cast Nat.pos_of_mem_divisors hm) _

end EtaQuotient
end WeightTwoCusps
