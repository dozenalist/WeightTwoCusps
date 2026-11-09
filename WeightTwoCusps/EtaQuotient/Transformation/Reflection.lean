module

public import WeightTwoCusps.EtaQuotient.Transformation.Inversion
public import WeightTwoCusps.EtaQuotient.Cusps.Infinity

/-!
# Reflection of exponents and holomorphy at the cusp zero

Reflection is the divisor involution `m ↦ N/m` in Savitt's Proposition 3.1.
It transports the infinity analysis to the cusp zero.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Complex Filter
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm Topology

namespace WeightTwoCusps.EtaQuotient

/-- The exponent function obtained by reversing the divisor exponents. -/
def reflect (N : ℕ) (r : Fin N → ℤ) : Fin N → ℤ :=
  fun i ↦ exponent r (N / (i.val + 1))

theorem exponent_reflect {N m : ℕ} (hm : m ∈ N.divisors) (r : Fin N → ℤ) :
    exponent (reflect N r) m = exponent r (N / m) := by
  have hmpos := Nat.pos_of_mem_divisors hm
  have hmle := Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisors hm))
    (Nat.dvd_of_mem_divisors hm)
  rw [exponent_of_mem_divisors _ hm]
  simp only [reflect]
  rw [show m - 1 + 1 = m by omega]

theorem infinitySum_reflect (N : ℕ) (r : Fin N → ℤ) :
    infinitySum N (reflect N r) = zeroSum N r := by
  rw [infinitySum, zeroSum]
  calc (∑ m ∈ N.divisors, (m : ℤ) * exponent (reflect N r) m)
      = ∑ m ∈ N.divisors, (m : ℤ) * exponent r (N / m) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [exponent_reflect hm]
    _ = ∑ m ∈ N.divisors, ((N / m : ℕ) : ℤ) * exponent r m := by
      rw [← Nat.sum_divisorsAntidiagonal (fun m d ↦ (m : ℤ) * exponent r d)]
      exact Nat.sum_divisorsAntidiagonal' (fun m d ↦ (m : ℤ) * exponent r d)

theorem reciprocalProduct_eq_reflect_dilate {N : ℕ} (hN : 0 < N) (r : Fin N → ℤ) (z : ℍ) :
    reciprocalProduct N r z =
      etaQuotient N (reflect N r) (Eta.dilate (1 / N) (by positivity) z) := by
  rw [reciprocalProduct, etaQuotient]
  calc (∏ m ∈ N.divisors, ModularForm.eta ((z : ℂ) / m) ^ exponent r m)
      = ∏ m ∈ N.divisors, ModularForm.eta ((z : ℂ) / (N / m : ℕ)) ^ exponent r (N / m) :=
        (Nat.prod_div_divisors N
          (fun m : ℕ ↦ ModularForm.eta ((z : ℂ) / (m : ℂ)) ^ exponent r m)).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro m hm
      rw [exponent_reflect hm]
      congr 2
      simp only [Eta.coe_dilate, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
      have he : ((N / m : ℕ) : ℂ) * m = N := by
        exact_mod_cast Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hm)
      have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
      have hm0 : ((N / m : ℕ) : ℂ) ≠ 0 := by
        have : 0 < N / m := Nat.div_pos (Nat.le_of_dvd hN (Nat.dvd_of_mem_divisors hm))
          (Nat.pos_of_mem_divisors hm)
        exact_mod_cast this.ne'
      field_simp
      linear_combination -he * (z : ℂ)

/-- Nonnegative second endpoint order suffices for boundedness after `S`. -/
theorem slash_S_isBoundedAtImInfty {N : ℕ} (hN : 0 < N) {r : Fin N → ℤ} {k : ℤ}
    (hk : HasWeight N r k) (h : 0 ≤ zeroSum N r) :
    IsBoundedAtImInfty (etaQuotient N r ∣[k] ModularGroup.S) := by
  rw [slash_S hk]
  apply Filter.BoundedAtFilter.smul
  have hb := isBoundedAtImInfty_of_nonneg (N := N) (r := reflect N r)
    (by rwa [infinitySum_reflect])
  have ht := Eta.tendsto_dilate_atImInfty (1 / N) (by positivity : (0 : ℝ) < 1 / N)
  have hb' := hb.comp_tendsto ht
  exact hb'.congr' (Filter.Eventually.of_forall (fun z ↦
    (reciprocalProduct_eq_reflect_dilate hN r z).symm)) Filter.EventuallyEq.rfl

/-- Strict second endpoint order suffices for vanishing after `S`. -/
theorem slash_S_isZeroAtImInfty {N : ℕ} (hN : 0 < N) {r : Fin N → ℤ} {k : ℤ}
    (hk : HasWeight N r k) (h : 0 < zeroSum N r) :
    IsZeroAtImInfty (etaQuotient N r ∣[k] ModularGroup.S) := by
  rw [slash_S hk]
  apply Filter.ZeroAtFilter.smul
  have hz := isZeroAtImInfty_of_pos (N := N) (r := reflect N r)
    (by rwa [infinitySum_reflect])
  have ht := Eta.tendsto_dilate_atImInfty (1 / N) (by positivity : (0 : ℝ) < 1 / N)
  exact (hz.comp ht).congr (fun z ↦ (reciprocalProduct_eq_reflect_dilate hN r z).symm)

private theorem reciprocalProduct_dilate_level {N : ℕ} (hN : 0 < N) (r : Fin N → ℤ) (z : ℍ) :
    reciprocalProduct N r (Eta.dilate N (by exact_mod_cast hN) z) =
      etaQuotient N (reflect N r) z := by
  rw [reciprocalProduct_eq_reflect_dilate hN]
  congr 1
  apply UpperHalfPlane.ext
  simp only [Eta.coe_dilate, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- The full boundedness criterion at the cusp zero. -/
theorem slash_S_isBoundedAtImInfty_iff {N : ℕ} (hN : 0 < N) {r : Fin N → ℤ} {k : ℤ}
    (hk : HasWeight N r k) :
    IsBoundedAtImInfty (etaQuotient N r ∣[k] ModularGroup.S) ↔ 0 ≤ zeroSum N r := by
  refine ⟨fun h ↦ ?_, slash_S_isBoundedAtImInfty hN hk⟩
  rw [slash_S hk] at h
  have hr : IsBoundedAtImInfty (reciprocalProduct N r) := by
    have hi := h.smul (inversionConstant N r)⁻¹
    have heq : (inversionConstant N r)⁻¹ • (inversionConstant N r • reciprocalProduct N r) =
        reciprocalProduct N r := by
      ext z
      simp [Pi.smul_apply, smul_eq_mul, inversionConstant_ne_zero]
    rw [heq] at hi
    exact hi
  have hc := hr.comp_tendsto (Eta.tendsto_dilate_atImInfty N (by exact_mod_cast hN))
  have hb : IsBoundedAtImInfty (etaQuotient N (reflect N r)) :=
    hc.congr' (Filter.Eventually.of_forall (reciprocalProduct_dilate_level hN r))
      Filter.EventuallyEq.rfl
  have hi := (isBoundedAtImInfty_iff N (reflect N r)).mp hb
  rwa [infinitySum_reflect] at hi

end WeightTwoCusps.EtaQuotient
