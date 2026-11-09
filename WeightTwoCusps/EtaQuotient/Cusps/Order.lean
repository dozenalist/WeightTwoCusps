module

public import WeightTwoCusps.EtaQuotient.Criteria.General
public import WeightTwoCusps.EtaQuotient.QExpansion.Basic
public import Mathlib.Analysis.Analytic.Order

/-! # Analytic orders in local cusp parameters -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Function Complex Filter
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm Topology Real Manifold

namespace WeightTwoCusps.EtaQuotient

/-- The order of the q-expansion agrees with the analytic order of the cusp function. -/
theorem qExpansion_order_eq_analyticOrder {h : ℝ} {f : ℍ → ℂ}
    (hf : AnalyticAt ℂ (UpperHalfPlane.cuspFunction h f) 0) :
    (UpperHalfPlane.qExpansion h f).order = analyticOrderAt
      (UpperHalfPlane.cuspFunction h f) 0 := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [PowerSeries.nat_le_order_iff, natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf]
  simp only [UpperHalfPlane.qExpansion, PowerSeries.coeff_mk, mul_eq_zero,
    inv_eq_zero, Nat.cast_eq_zero, Nat.factorial_ne_zero, false_or]

/-- A nonzero periodic holomorphic function has a nonzero leading coefficient
after division by the power of its q-parameter given by its q-expansion order. -/
theorem exists_qExpansion_leading_limit {h : ℝ} {f : ℍ → ℂ} (hh : 0 < h)
    (hp : Periodic (f ∘ UpperHalfPlane.ofComplex) h) (hf : MDiff f)
    (hb : IsBoundedAtImInfty f) (hne : f UpperHalfPlane.I ≠ 0) :
    ∃ (n : ℕ) (u : ℂ), (UpperHalfPlane.qExpansion h f).order = n ∧ u ≠ 0 ∧
      Tendsto (fun z : ℍ ↦ f z / Periodic.qParam h z ^ n) atImInfty (𝓝 u) := by
  have hseries : UpperHalfPlane.qExpansion h f ≠ 0 := by
    intro hz
    have hzero := (UpperHalfPlane.qExpansion_eq_zero_iff hh hp hf hb).mp hz
    exact hne (congrFun hzero UpperHalfPlane.I)
  let n := (UpperHalfPlane.qExpansion h f).order.toNat
  have hn : (UpperHalfPlane.qExpansion h f).order = n :=
    (ENat.natCast_toNat_eq_self.mpr (PowerSeries.order_eq_top.not.mpr hseries)).symm
  have ha := UpperHalfPlane.analyticAt_cuspFunction_zero hh hp hf hb
  have horder : analyticOrderAt (UpperHalfPlane.cuspFunction h f) 0 = n :=
    (qExpansion_order_eq_analyticOrder ha).symm.trans hn
  obtain ⟨g, hg, hg0, hfg⟩ := ha.analyticOrderAt_eq_natCast.mp horder
  have hq := qParam_tendsto_atImInfty hh
  refine ⟨n, g 0, hn, hg0, ?_⟩
  apply (hg.continuousAt.tendsto.comp hq).congr'
  filter_upwards [hq.eventually hfg] with z hz
  rw [← UpperHalfPlane.eq_cuspFunction z hh.ne' hp, hz]
  simp only [sub_zero, smul_eq_mul]
  exact (mul_div_cancel_left₀ _ (pow_ne_zero n (Periodic.qParam_ne_zero (h := h) z))).symm

/-- The logarithmic growth of a periodic holomorphic function reads off its local order. -/
theorem log_norm_div_im_tendsto_of_qExpansion {h : ℝ} {f : ℍ → ℂ} (hh : 0 < h)
    (hp : Periodic (f ∘ UpperHalfPlane.ofComplex) h) (hf : MDiff f)
    (hb : IsBoundedAtImInfty f) (hne : ∀ z, f z ≠ 0) :
    ∃ n : ℕ, (UpperHalfPlane.qExpansion h f).order = n ∧
      Tendsto (fun z : ℍ ↦ Real.log ‖f z‖ / z.im) atImInfty
        (𝓝 (-2 * π * (n : ℝ) / h)) := by
  obtain ⟨n, u, hn, hu, ht⟩ := exists_qExpansion_leading_limit hh hp hf hb (hne _)
  have hi : Tendsto (fun z : ℍ ↦ z.im) atImInfty atTop := tendsto_comap
  have hlog := ht.norm.log (norm_ne_zero_iff.mpr hu)
  have hlim := (hlog.div_atTop hi).add_const (-2 * π * (n : ℝ) / h)
  rw [zero_add] at hlim
  refine ⟨n, hn, hlim.congr (fun z ↦ ?_)⟩
  rw [norm_div, Real.log_div (norm_ne_zero_iff.mpr (hne z))
    (norm_ne_zero_iff.mpr (pow_ne_zero n (Periodic.qParam_ne_zero (h := h) z))),
    norm_pow, Real.log_pow, Periodic.norm_qParam, Real.log_exp]
  have him : z.im ≠ 0 := z.im_pos.ne'
  simp only [UpperHalfPlane.coe_im]
  field_simp
  ring

/-- Every integral-weight slash of an eta quotient is nonzero on `ℍ`. -/
theorem slash_ne_zero (N : ℕ) (r : Fin N → ℤ) (k : ℤ) (γ : SL(2, ℤ)) (z : ℍ) :
    (etaQuotient N r ∣[k] γ) z ≠ 0 := by
  rw [ModularForm.SL_slash_apply]
  exact mul_ne_zero (ne_zero N r (γ • z)) (zpow_ne_zero _ (denom_ne_zero γ z))

theorem cuspUnit_ne_zero (N : ℕ) (r : Fin N → ℤ) (γ : SL(2, ℤ)) (z : ℍ) :
    cuspUnit N r γ z ≠ 0 :=
  mul_ne_zero (Complex.exp_ne_zero _) (slash_ne_zero N (double r) (exponentSum N r) γ z)

/-- The exact logarithmic growth at a rational cusp for doubled exponents. -/
theorem log_norm_double_slash_div_im_tendsto (N : ℕ) (r : Fin N → ℤ) (γ : SL(2, ℤ)) :
    Tendsto (fun z : ℍ ↦ Real.log ‖(etaQuotient N (double r) ∣[exponentSum N r] γ) z‖ / z.im)
      atImInfty (𝓝 (-2 * π * (cuspSum N r (γ 1 0).natAbs : ℝ) / 12)) := by
  obtain ⟨u, hu, ht⟩ := cuspUnit_tendsto_nonzero N r γ
  have hi : Tendsto (fun z : ℍ ↦ z.im) atImInfty atTop := tendsto_comap
  have hlog := ht.norm.log (norm_ne_zero_iff.mpr hu)
  have hlim := (hlog.div_atTop hi).add_const
    (-2 * π * (cuspSum N r (γ 1 0).natAbs : ℝ) / 12)
  rw [zero_add] at hlim
  apply hlim.congr
  intro z
  rw [norm_double_slash_eq_exp_mul_cuspUnit,
    Real.log_mul (Real.exp_ne_zero _) (norm_ne_zero_iff.mpr (cuspUnit_ne_zero N r γ z)),
    Real.log_exp]
  field_simp
  ring

/-- The exact logarithmic growth at every rational cusp, with arbitrary integer exponents. -/
theorem log_norm_slash_div_im_tendsto {N : ℕ} {r : Fin N → ℤ} {k : ℤ}
    (hk : HasWeight N r k) (γ : SL(2, ℤ)) :
    Tendsto (fun z : ℍ ↦ Real.log ‖(etaQuotient N r ∣[k] γ) z‖ / z.im)
      atImInfty (𝓝 (-2 * π * (cuspSum N r (γ 1 0).natAbs : ℝ) / 24)) := by
  have ht := (log_norm_double_slash_div_im_tendsto N r γ).div_const 2
  convert ht using 1
  · ext z
    rw [double_slash_eq_square hk γ]
    simp only [norm_pow, Real.log_pow]
    ring
  · congr 1
    ring

/-- Any positive period identifies the analytic order with the Ligozat sum.
This also proves that the predicted local order is an integer. -/
theorem qExpansion_order_slash {N : ℕ} {r : Fin N → ℤ} {k : ℤ} {h : ℝ}
    (hk : HasWeight N r k) (γ : SL(2, ℤ)) (hh : 0 < h)
    (hp : Periodic ((etaQuotient N r ∣[k] γ) ∘ UpperHalfPlane.ofComplex) h)
    (hb : IsBoundedAtImInfty (etaQuotient N r ∣[k] γ)) :
    ∃ n : ℕ, (UpperHalfPlane.qExpansion h (etaQuotient N r ∣[k] γ)).order = n ∧
      (n : ℝ) = h / 24 * (cuspSum N r (γ 1 0).natAbs : ℝ) := by
  obtain ⟨n, hn, ht⟩ := log_norm_div_im_tendsto_of_qExpansion hh hp
    ((holo N r).slash k (Matrix.SpecialLinearGroup.mapGL ℝ γ)) hb (slash_ne_zero N r k γ)
  have heq := tendsto_nhds_unique ht (log_norm_slash_div_im_tendsto hk γ)
  refine ⟨n, hn, ?_⟩
  have hp0 := Real.pi_pos.ne'
  field_simp at heq
  nlinarith

/-- The usual integral width attached to a denominator. -/
def cuspWidth (N c : ℕ) : ℕ := N / Nat.gcd (c ^ 2) N

theorem cuspWidth_pos {N : ℕ} (hN : 0 < N) (c : ℕ) : 0 < cuspWidth N c := by
  apply Nat.div_pos
  · exact Nat.le_of_dvd hN (Nat.gcd_dvd_right _ _)
  · exact Nat.gcd_pos_of_pos_right _ hN

theorem cuspWidth_dvd_iff {N : ℕ} (hN : 0 < N) (c w : ℕ) :
    cuspWidth N c ∣ w ↔ N ∣ c ^ 2 * w := by
  rw [cuspWidth, Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_right _ _)
    (Nat.gcd_pos_of_pos_right _ hN)]
  simpa only [Nat.gcd_comm] using (Nat.dvd_gcd_mul_iff_dvd_mul (k := N) (n := c ^ 2) (m := w))

theorem conjugate_T_lowerLeft (γ : SL(2, ℤ)) (w : ℤ) :
    (γ * ModularGroup.T ^ w * γ⁻¹) 1 0 = -(γ 1 0) ^ 2 * w := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.SL2_inv_expl,
    ModularGroup.coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

/-- Translation by the predicted width fixes the cusp modulo `Γ₀(N)`. -/
theorem conjugate_T_cuspWidth_mem (N : ℕ) (γ : SL(2, ℤ)) :
    γ * ModularGroup.T ^ (cuspWidth N (γ 1 0).natAbs : ℤ) * γ⁻¹ ∈
      CongruenceSubgroup.Gamma0 N := by
  rw [CongruenceSubgroup.Gamma0_mem, conjugate_T_lowerLeft]
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr
  have hg := Nat.gcd_dvd_left ((γ 1 0).natAbs ^ 2) N
  obtain ⟨t, ht⟩ := hg
  have hw : N ∣ (γ 1 0).natAbs ^ 2 * cuspWidth N (γ 1 0).natAbs := by
    refine ⟨t, ?_⟩
    dsimp [cuspWidth]
    nth_rw 1 [ht]
    rw [mul_right_comm, Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)]
  have hcast : (N : ℤ) ∣ (γ 1 0) ^ 2 * (cuspWidth N (γ 1 0).natAbs : ℤ) := by
    rw [Int.natCast_dvd]
    simpa only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] using hw
  simpa only [neg_mul] using dvd_neg.mpr hcast

/-- The predicted width is minimal: integral cusp translations are exactly its multiples. -/
theorem conjugate_T_mem_iff_cuspWidth_dvd {N : ℕ} (hN : 0 < N)
    (γ : SL(2, ℤ)) (w : ℕ) :
    γ * ModularGroup.T ^ (w : ℤ) * γ⁻¹ ∈ CongruenceSubgroup.Gamma0 N ↔
      cuspWidth N (γ 1 0).natAbs ∣ w := by
  rw [CongruenceSubgroup.Gamma0_mem, conjugate_T_lowerLeft,
    ZMod.intCast_zmod_eq_zero_iff_dvd, neg_mul, dvd_neg, Int.natCast_dvd]
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
  exact (cuspWidth_dvd_iff hN _ _).symm

private theorem periodic_slash_of_conjugate_T_mem {N : ℕ} {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (γ : SL(2, ℤ)) (w : ℕ)
    (hw : γ * ModularGroup.T ^ (w : ℤ) * γ⁻¹ ∈ CongruenceSubgroup.Gamma0 N) :
    Periodic (((f : ℍ → ℂ) ∣[k] γ) ∘ UpperHalfPlane.ofComplex) (w : ℝ) := by
  have hfix : ((f : ℍ → ℂ) ∣[k] γ) ∣[k] (ModularGroup.T ^ (w : ℤ)) =
      (f : ℍ → ℂ) ∣[k] γ := by
    have h : (f : ℍ → ℂ) ∣[k] (γ * ModularGroup.T ^ (w : ℤ) * γ⁻¹) = f :=
      SlashInvariantForm.slash_action_eqn f _ (Subgroup.mem_map_of_mem _ hw)
    have he := congrArg (fun g : ℍ → ℂ ↦ g ∣[k] γ) h
    simpa only [← SlashAction.slash_mul, inv_mul_cancel_right] using he
  apply UpperHalfPlane.periodic_comp_ofComplex
  intro z
  have he := congrFun hfix z
  rw [ModularForm.SL_slash_apply, modular_T_zpow_smul] at he
  have hd : denom ((ModularGroup.T ^ (w : ℤ)) : SL(2, ℤ)) z = 1 := by
    change (((ModularGroup.T ^ (w : ℤ)) 1 0 : ℤ) : ℂ) * (z : ℂ) +
      (((ModularGroup.T ^ (w : ℤ)) 1 1 : ℤ) : ℂ) = 1
    simp only [ModularGroup.coe_T_zpow]
    norm_num
  rw [hd, one_zpow, mul_one] at he
  simpa only [Int.cast_natCast] using he

/-- Every modular form is periodic in the predicted local cusp parameter. -/
theorem periodic_slash_cuspWidth {N : ℕ} {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (γ : SL(2, ℤ)) :
    Periodic (((f : ℍ → ℂ) ∣[k] γ) ∘ UpperHalfPlane.ofComplex)
      (cuspWidth N (γ 1 0).natAbs : ℝ) :=
  periodic_slash_of_conjugate_T_mem f γ _ (conjugate_T_cuspWidth_mem N γ)

/-- The arithmetic formula is the analytic q-expansion order in the usual
local parameter, for every modular eta quotient and every divisor cusp. -/
theorem cuspOrder_eq_qExpansion_order {N c : ℕ} (hN : 0 < N) (hc : c ∈ N.divisors)
    {r : Fin N → ℤ} {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (hf : (f : ℍ → ℂ) = etaQuotient N r) (γ : SL(2, ℤ))
    (hγc : (γ 1 0).natAbs = c) :
    ∃ n : ℕ,
      (UpperHalfPlane.qExpansion (cuspWidth N c : ℝ) (etaQuotient N r ∣[k] γ)).order = n ∧
        cuspOrder N r c = (n : ℚ) := by
  have : NeZero N := ⟨hN.ne'⟩
  have hk := hasWeight_of_modularForm hN f hf
  have hp := periodic_slash_cuspWidth f γ
  rw [hf, hγc] at hp
  have hb := ModularFormClass.bdd_at_infty_slash f γ
  rw [hf] at hb
  obtain ⟨n, hn, horder⟩ := qExpansion_order_slash hk γ
    (by exact_mod_cast cuspWidth_pos hN c) hp hb
  rw [hγc] at horder
  refine ⟨n, hn, ?_⟩
  have heq : (cuspOrder N r c : ℝ) = (n : ℝ) := by
    rw [cuspOrder_eq_gcd_sq hc]
    push_cast
    rw [horder, cuspWidth, Nat.cast_div_charZero (Nat.gcd_dvd_right _ _)]
    ring
  exact_mod_cast heq

/-- Ligozat's order is integral for every genuine modular eta quotient. -/
theorem cuspOrder_integral_of_modularForm {N c : ℕ} (hN : 0 < N) (hc : c ∈ N.divisors)
    {r : Fin N → ℤ} {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (hf : (f : ℍ → ℂ) = etaQuotient N r) : ∃ n : ℕ, cuspOrder N r c = n := by
  let γ : SL(2, ℤ) := ⟨!![1, 0; (c : ℤ), 1], by simp⟩
  obtain ⟨n, _, hn⟩ := cuspOrder_eq_qExpansion_order hN hc f hf γ (by simp [γ])
  exact ⟨n, hn⟩

end WeightTwoCusps.EtaQuotient
