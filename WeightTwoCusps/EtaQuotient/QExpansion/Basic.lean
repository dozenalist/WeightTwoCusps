module

public import WeightTwoCusps.EtaQuotient.Cusps.Infinity
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.RingTheory.PowerSeries.Order

/-!
# q-expansions of eta quotients

The normalized Euler product is periodic, holomorphic and tends to one at
infinity for arbitrary integer exponents. Whenever the infinity exponent
sum is `24v` with `v ≥ 0`, the q-expansion begins with `q^v` with coefficient
one, including for eta quotients with negative exponents.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Function Complex Filter
open UpperHalfPlane hiding I
open scoped Topology Manifold ModularForm Real MatrixGroups

namespace WeightTwoCusps.EtaQuotient

private theorem qParam_one_periodic : Periodic (Periodic.qParam 1) 1 := by
  intro z
  simp only [Periodic.qParam, Complex.ofReal_one, div_one, mul_add, mul_one]
  exact Complex.exp_periodic _

theorem eulerPart_add_nat (m : ℕ) (z : ℂ) : eulerPart (z + m) = eulerPart z := by
  have hq : Periodic.qParam 1 (z + m) = Periodic.qParam 1 z := by
    simpa using qParam_one_periodic.nat_mul m z
  simp only [eulerPart, ModularForm.eta_q, hq]

/-- The Euler factor has strict period one, independently of the congruences. -/
theorem unitPart_periodic (N : ℕ) (r : Fin N → ℤ) :
    Periodic (unitPart N r ∘ UpperHalfPlane.ofComplex) 1 := by
  apply UpperHalfPlane.periodic_comp_ofComplex
  intro z
  simp only [unitPart, UpperHalfPlane.coe_vadd, Complex.ofReal_one, mul_add, mul_one]
  apply Finset.prod_congr rfl
  intro m hm
  rw [add_comm (m : ℂ), eulerPart_add_nat]

/-- The normalized Euler product is holomorphic even with negative exponents. -/
theorem unitPart_holo (N : ℕ) (r : Fin N → ℤ) : MDiff (unitPart N r) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine DifferentiableOn.congr (f := fun z : ℂ ↦
    ∏ m ∈ N.divisors, eulerPart ((m : ℂ) * z) ^ exponent r m) ?_ ?_
  · apply DifferentiableOn.fun_finsetProd
    intro m hm z hz
    have hpos : 0 < (((m : ℂ) * z).im) := by
      simpa using mul_pos (show (0 : ℝ) < m by exact_mod_cast Nat.pos_of_mem_divisors hm) hz
    exact (((ModularForm.differentiableAt_eta_tprod hpos).comp z
      ((differentiableAt_const (m : ℂ)).mul differentiableAt_id)).zpow
        (Or.inl (ModularForm.eta_tprod_ne_zero hpos))).differentiableWithinAt
  · intro z hz
    simp [unitPart, UpperHalfPlane.ofComplex_apply_of_im_pos hz]

theorem unitPart_analyticAt_cuspFunction (N : ℕ) (r : Fin N → ℤ) :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 (unitPart N r)) 0 :=
  UpperHalfPlane.analyticAt_cuspFunction_zero (by norm_num) (unitPart_periodic N r)
    (unitPart_holo N r) ((unitPart_tendsto_one N r).isBigO_one ℝ)

@[simp] theorem qExpansion_unitPart_coeff_zero (N : ℕ) (r : Fin N → ℤ) :
    (UpperHalfPlane.qExpansion 1 (unitPart N r)).coeff 0 = 1 := by
  rw [UpperHalfPlane.qExpansion_coeff_zero (by norm_num)
    (unitPart_analyticAt_cuspFunction N r) (unitPart_periodic N r)]
  exact (unitPart_tendsto_one N r).limUnder_eq

/-- The normalized Euler product has a convergent power series on the full q-disc. -/
theorem hasSum_unitPart (N : ℕ) (r : Fin N → ℤ) (z : ℍ) :
    HasSum (fun n ↦ (UpperHalfPlane.qExpansion 1 (unitPart N r)).coeff n *
      Periodic.qParam 1 z ^ n) (unitPart N r z) := by
  simpa only [smul_eq_mul] using UpperHalfPlane.hasSum_qExpansion (by norm_num)
    (unitPart_periodic N r) (unitPart_holo N r) ((unitPart_tendsto_one N r).isBigO_one ℝ) z

/-- If the weighted exponent sum is `24v`, the quotient is `q^v` times its Euler unit. -/
theorem eq_qParam_pow_mul_unitPart {N : ℕ} {r : Fin N → ℤ} {v : ℕ}
    (hv : infinitySum N r = 24 * (v : ℤ)) (z : ℍ) :
    etaQuotient N r z = Periodic.qParam 1 z ^ v * unitPart N r z := by
  rw [eq_exp_mul_unitPart]
  congr 1
  simp only [hv, Periodic.qParam, Complex.ofReal_one, div_one, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Translation congruence supplies the strict period used in the q-expansion. -/
theorem periodic_of_infinity_congruence {N : ℕ} {r : Fin N → ℤ}
    (h : (24 : ℤ) ∣ infinitySum N r) :
    Periodic (etaQuotient N r ∘ UpperHalfPlane.ofComplex) 1 := by
  apply UpperHalfPlane.periodic_comp_ofComplex
  intro z
  rw [← modular_T_smul, transform_T]
  rw [(ZMod.intCast_zmod_eq_zero_iff_dvd (infinitySum N r) 24).mpr h,
    AddChar.map_zero_eq_one, one_mul]

/-- The complete convergent series is the Euler-unit series shifted by `v`. -/
theorem hasSum_etaQuotient {N : ℕ} {r : Fin N → ℤ} {v : ℕ}
    (hv : infinitySum N r = 24 * (v : ℤ)) (z : ℍ) :
    HasSum (fun n ↦ (PowerSeries.X ^ v * UpperHalfPlane.qExpansion 1 (unitPart N r)).coeff n *
      Periodic.qParam 1 z ^ n) (etaQuotient N r z) := by
  rw [← hasSum_nat_add_iff' v]
  have hz : (∑ n ∈ Finset.range v,
      (PowerSeries.X ^ v * UpperHalfPlane.qExpansion 1 (unitPart N r)).coeff n *
        Periodic.qParam 1 z ^ n) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [PowerSeries.coeff_X_pow_mul', ite_eq_right (not_le.mpr (Finset.mem_range.mp hn)), zero_mul]
  rw [hz, sub_zero, eq_qParam_pow_mul_unitPart hv]
  convert (hasSum_unitPart N r z).mul_left (Periodic.qParam 1 z ^ v) using 1
  ext n
  rw [PowerSeries.coeff_X_pow_mul, pow_add]
  ring

/-- The analytic q-expansion factors as `X^v` times a unit with constant coefficient one. -/
theorem qExpansion_eq_X_pow_mul {N : ℕ} {r : Fin N → ℤ} {v : ℕ}
    (hv : infinitySum N r = 24 * (v : ℤ)) :
    UpperHalfPlane.qExpansion 1 (etaQuotient N r) =
      PowerSeries.X ^ v * UpperHalfPlane.qExpansion 1 (unitPart N r) := by
  let : FunLike (ℍ → ℂ) ℍ ℂ := { coe := id, coe_injective := Function.injective_id }
  have hp := periodic_of_infinity_congruence (hv ▸ dvd_mul_right 24 (v : ℤ))
  have hb := isBoundedAtImInfty_of_nonneg (show 0 ≤ infinitySum N r by rw [hv]; positivity)
  ext n
  symm
  exact UpperHalfPlane.qExpansion_coeff_unique (h := 1) (etaQuotient N r) (by norm_num)
    (UpperHalfPlane.analyticAt_cuspFunction_zero (by norm_num) hp (holo N r) hb)
    (fun z ↦ by convert hasSum_etaQuotient hv z using 1; rfl) n

/-- Every coefficient below the leading exponent vanishes. -/
theorem qExpansion_coeff_eq_zero_of_lt {N : ℕ} {r : Fin N → ℤ} {v n : ℕ}
    (hv : infinitySum N r = 24 * (v : ℤ)) (hn : n < v) :
    (UpperHalfPlane.qExpansion 1 (etaQuotient N r)).coeff n = 0 := by
  rw [qExpansion_eq_X_pow_mul hv, PowerSeries.coeff_X_pow_mul', ite_eq_right (not_le.mpr hn)]

/-- The first nonzero q-expansion coefficient of an eta quotient is one. -/
theorem qExpansion_coeff_leading {N : ℕ} {r : Fin N → ℤ} {v : ℕ}
    (hv : infinitySum N r = 24 * (v : ℤ)) :
    (UpperHalfPlane.qExpansion 1 (etaQuotient N r)).coeff v = 1 := by
  rw [qExpansion_eq_X_pow_mul hv]
  simpa using PowerSeries.coeff_X_pow_mul (UpperHalfPlane.qExpansion 1 (unitPart N r)) v 0

/-- The analytic q-expansion order is exactly the infinity part of Ligozat's formula. -/
theorem qExpansion_order {N : ℕ} {r : Fin N → ℤ} {v : ℕ}
    (hv : infinitySum N r = 24 * (v : ℤ)) :
    (UpperHalfPlane.qExpansion 1 (etaQuotient N r)).order = v := by
  apply PowerSeries.order_eq_nat.mpr
  exact ⟨by rw [qExpansion_coeff_leading hv]; exact one_ne_zero,
    fun n hn ↦ qExpansion_coeff_eq_zero_of_lt hv hn⟩

/-- The leading exponent can be read directly from the finite arithmetic data. -/
theorem infinitySum_eq_twentyFour_mul_order {N : ℕ} {r : Fin N → ℤ}
    (hi : (24 : ℤ) ∣ infinitySum N r) (h0 : 0 ≤ infinitySum N r) :
    infinitySum N r = 24 * (((infinitySum N r / 24).toNat : ℕ) : ℤ) := by
  obtain ⟨t, ht⟩ := hi
  have ht0 : 0 ≤ t := by omega
  rw [ht]
  simp [Int.toNat_of_nonneg ht0]

/-- The infinity order requires no separately supplied leading exponent. -/
theorem qExpansion_order_of_congruence {N : ℕ} {r : Fin N → ℤ}
    (hi : (24 : ℤ) ∣ infinitySum N r) (h0 : 0 ≤ infinitySum N r) :
    (UpperHalfPlane.qExpansion 1 (etaQuotient N r)).order = (infinitySum N r / 24).toNat :=
  qExpansion_order (infinitySum_eq_twentyFour_mul_order hi h0)

end WeightTwoCusps.EtaQuotient
