module

public import WeightTwoCusps.Oldforms.Rescale
public import WeightTwoCusps.QExpansion
public import Mathlib.RingTheory.PowerSeries.Expand

/-! # Q-expansions of degeneracy lifts -/

@[expose] public noncomputable section

open UpperHalfPlane
open scoped MatrixGroups Topology

namespace WeightTwoCusps

namespace Oldforms

/-- Positive dilation raises the local q-parameter to the dilation factor. -/
theorem qParam_dilate (h : ℝ) (d : ℕ) (hd : 0 < d) (z : ℍ) :
    Function.Periodic.qParam h (Eta.dilate d (by exact_mod_cast hd) z) =
      Function.Periodic.qParam h z ^ d := by
  simp only [Eta.coe_dilate, Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Insert zero coefficients into a convergent power series. -/
theorem hasSum_expand (p : PowerSeries ℂ) (d : ℕ) (hd : d ≠ 0) (q a : ℂ)
    (hs : HasSum (fun n ↦ p.coeff n * (q ^ d) ^ n) a) :
    HasSum (fun n ↦ (p.expand d hd).coeff n * q ^ n) a := by
  have hinj : Function.Injective (fun n : ℕ ↦ d * n) := mul_right_injective₀ hd
  apply (hinj.hasSum_iff ?_).mp
  · simpa only [Function.comp_def, PowerSeries.coeff_expand_mul, pow_mul] using hs
  · intro n hn
    have hnd : ¬ d ∣ n := by
      rintro ⟨m, rfl⟩
      exact hn ⟨m, rfl⟩
    simp [PowerSeries.coeff_expand_of_not_dvd d hd p hnd]

end Oldforms

/-- Rescaling replaces `q` by `q^d` at every positive strict period of the source. -/
theorem gamma0Rescale_qExpansion {M : ℕ} (f : gamma0CuspForms M) (d : ℕ)
    (hd : 0 < d) {h : ℝ} (hh : 0 < h)
    (hΓ : h ∈ (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)).strictPeriods) :
    qExpansion h (gamma0Rescale f d hd) = (qExpansion h f).expand d hd.ne' := by
  have hΓ' : h ∈ (CongruenceSubgroup.Gamma0 (M * d) :
      Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simpa using hΓ
  let : Fact (IsCusp .infty
      (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods hh hΓ⟩
  ext n
  symm
  refine ModularFormClass.qExpansion_coeff_unique (f := gamma0Rescale f d hd)
    (c := fun m ↦ ((qExpansion h f).expand d hd.ne').coeff m) hh hΓ' ?_ n
  intro z
  have hs := ModularForm.hasSum_qExpansion f hh hΓ (Eta.dilate d (by exact_mod_cast hd) z)
  rw [Oldforms.qParam_dilate h d hd z] at hs
  have hs' := Oldforms.hasSum_expand (qExpansion h f) d hd.ne'
    (Function.Periodic.qParam h z) _ hs
  simpa only [gamma0Rescale_apply, smul_eq_mul] using hs'

/-- Increasing the period by a positive integer inserts zero coefficients. -/
theorem gamma0_qExpansion_nat_mul {M : ℕ} (f : gamma0CuspForms M) {h : ℝ}
    (hh : 0 < h)
    (hΓ : h ∈ (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)).strictPeriods)
    (d : ℕ) (hd : 0 < d) :
    qExpansion (h * d) f = (qExpansion h f).expand d hd.ne' := by
  have hΓ' : h * d ∈ (CongruenceSubgroup.Gamma0 M :
      Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simpa [nsmul_eq_mul, mul_comm] using
      (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)).strictPeriods.nsmul_mem hΓ d
  let : Fact (IsCusp .infty
      (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods hh hΓ⟩
  have hq (z : ℍ) : Function.Periodic.qParam h z =
      Function.Periodic.qParam (h * d) z ^ d := by
    simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp [show (h : ℂ) ≠ 0 by exact_mod_cast hh.ne',
      show (d : ℂ) ≠ 0 by exact_mod_cast hd.ne']
  ext n
  symm
  refine ModularFormClass.qExpansion_coeff_unique (f := f)
    (c := fun m ↦ ((qExpansion h f).expand d hd.ne').coeff m) (by positivity) hΓ' ?_ n
  intro z
  have hs := ModularForm.hasSum_qExpansion f hh hΓ z
  rw [hq z] at hs
  simpa only [smul_eq_mul] using
    Oldforms.hasSum_expand (qExpansion h f) d hd.ne' (Function.Periodic.qParam (h * d) z) _ hs

/-- Dividing the natural period of a lift changes its q-parameter accordingly.
No assumption that `h` is a strict period of the source group is needed. -/
theorem gamma0Rescale_qExpansion_period {M : ℕ} (f : gamma0CuspForms M)
    (d : ℕ) (hd : 0 < d) {h : ℝ} (hh : 0 < h) :
    qExpansion h (gamma0Rescale f d hd) = qExpansion (h * d) f := by
  let : Fact (IsCusp .infty
      (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos (by simp)⟩
  let : Fact (IsCusp .infty
      (CongruenceSubgroup.Gamma0 (M * d) : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos (by simp)⟩
  have hhd : 0 < h * (d : ℝ) := mul_pos hh (by exact_mod_cast hd)
  have heq : cuspFunction h (gamma0Rescale f d hd) =ᶠ[𝓝 (0 : ℂ)]
      cuspFunction (h * d) f := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with q hq
    by_cases hq0 : q = 0
    · subst q
      rw [(CuspFormClass.zero_at_infty (gamma0Rescale f d hd)).cuspFunction_apply_zero hh,
        (CuspFormClass.zero_at_infty f).cuspFunction_apply_zero hhd]
    · have hqn : ‖q‖ < 1 := by simpa only [mem_ball_zero_iff] using hq
      have hqh := Function.Periodic.im_invQParam_pos_of_norm_lt_one hh hqn hq0
      have hqhd := Function.Periodic.im_invQParam_pos_of_norm_lt_one hhd hqn hq0
      change Function.Periodic.cuspFunction h
          ((gamma0Rescale f d hd : ℍ → ℂ) ∘ ofComplex) q =
        Function.Periodic.cuspFunction (h * d) ((f : ℍ → ℂ) ∘ ofComplex) q
      rw [Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq0,
        Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq0]
      simp only [Function.comp_apply]
      rw [gamma0Rescale_apply f d hd]
      congr 1
      apply UpperHalfPlane.ext
      rw [Eta.coe_dilate, ofComplex_apply_of_im_pos hqh, ofComplex_apply_of_im_pos hqhd]
      simp only [Function.Periodic.invQParam, Complex.ofReal_mul,
        Complex.ofReal_natCast]
      ring
  ext n
  simp only [UpperHalfPlane.qExpansion_coeff]
  rw [Filter.EventuallyEq.iteratedDeriv_eq n heq]

/-- A positive integral period is an expansion of the period-one series. -/
theorem gamma0_qExpansion_nat {M : ℕ} (f : gamma0CuspForms M)
    (h : ℕ) (hh : 0 < h) : qExpansion h f = (qExpansion 1 f).expand h hh.ne' := by
  simpa only [one_mul] using gamma0_qExpansion_nat_mul f one_pos (by simp) h hh

@[simp] theorem gamma0Restrict_qExpansion {M N : ℕ} (f : gamma0CuspForms M)
    (hMN : M ∣ N) (h : ℝ) : qExpansion h (gamma0Restrict f hMN) = qExpansion h f := rfl

@[simp] theorem gamma0RescaleToLevel_qExpansion {M N : ℕ} (f : gamma0CuspForms M)
    (d : ℕ) (hMN : M * d ∣ N) (hd : 0 < d) (h : ℝ) :
    qExpansion h (gamma0RescaleToLevel f d hMN hd) = qExpansion h (gamma0Rescale f d hd) := rfl

/-- Coefficients of a degeneracy lift at period one. -/
@[simp] theorem gamma0Rescale_qExpansion_coeff {M : ℕ} (f : gamma0CuspForms M)
    (d : ℕ) (hd : 0 < d) (n : ℕ) :
    (qExpansion 1 (gamma0Rescale f d hd)).coeff n =
      if d ∣ n then (qExpansion 1 f).coeff (n / d) else 0 := by
  rw [gamma0Rescale_qExpansion f d hd one_pos (by simp), PowerSeries.coeff_expand]

/-- The coefficient rule at any positive strict period of the source group. -/
theorem gamma0Rescale_qExpansion_coeff_of_period {M : ℕ} (f : gamma0CuspForms M)
    (d : ℕ) (hd : 0 < d) {h : ℝ} (hh : 0 < h)
    (hΓ : h ∈ (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)).strictPeriods)
    (n : ℕ) : (qExpansion h (gamma0Rescale f d hd)).coeff n =
      if d ∣ n then (qExpansion h f).coeff (n / d) else 0 := by
  rw [gamma0Rescale_qExpansion f d hd hh hΓ, PowerSeries.coeff_expand]

@[simp] theorem gamma0Rescale_qExpansion_coeff_mul {M : ℕ} (f : gamma0CuspForms M)
    (d : ℕ) (hd : 0 < d) (n : ℕ) :
    (qExpansion 1 (gamma0Rescale f d hd)).coeff (d * n) = (qExpansion 1 f).coeff n := by
  rw [gamma0Rescale_qExpansion f d hd one_pos (by simp), PowerSeries.coeff_expand_mul]

theorem gamma0Rescale_qExpansion_coeff_of_not_dvd {M : ℕ} (f : gamma0CuspForms M)
    (d : ℕ) (hd : 0 < d) {n : ℕ} (hn : ¬ d ∣ n) :
    (qExpansion 1 (gamma0Rescale f d hd)).coeff n = 0 := by
  rw [gamma0Rescale_qExpansion_coeff, ite_eq_right hn]

@[simp] theorem gamma0RescaleToLevel_qExpansion_coeff {M N : ℕ} (f : gamma0CuspForms M)
    (d : ℕ) (hMN : M * d ∣ N) (hd : 0 < d) (n : ℕ) :
    (qExpansion 1 (gamma0RescaleToLevel f d hMN hd)).coeff n =
      if d ∣ n then (qExpansion 1 f).coeff (n / d) else 0 := by
  rw [gamma0RescaleToLevel_qExpansion, gamma0Rescale_qExpansion_coeff]

/-- Coefficients at a positive integral period, normalized back to period one. -/
theorem gamma0_qExpansion_nat_coeff {M : ℕ} (f : gamma0CuspForms M)
    (h : ℕ) (hh : 0 < h) (n : ℕ) :
    (qExpansion h f).coeff n = if h ∣ n then (qExpansion 1 f).coeff (n / h) else 0 := by
  have heq := gamma0_qExpansion_nat_mul f one_pos (by simp) h hh
  simpa only [one_mul, PowerSeries.coeff_expand] using congrArg (fun p ↦ p.coeff n) heq

/-- Insert zeros between entries of a finite coefficient table and truncate at `m`. -/
def rescaleCoefficients (d m : ℕ) (a : List ℂ) : List ℂ :=
  (List.range m).map fun n ↦ if d ∣ n then a[n / d]?.getD 0 else 0

/-- A finite lift needs only the source coefficients through degree `m / d`. -/
theorem gamma0Rescale_first_coeffs {M : ℕ} (f : gamma0CuspForms M)
    (d : ℕ) (hd : 0 < d) (m : ℕ) :
    first_coeffs m (gamma0Rescale f d hd) =
      rescaleCoefficients d m (first_coeffs (m / d + 1) f) := by
  rw [first_coeffs_eq_map_range, rescaleCoefficients]
  apply List.map_congr_left
  intro n hn
  have hn' : n < m := List.mem_range.mp hn
  have hindex : n / d < (first_coeffs (m / d + 1) f).length := by
    rw [first_coeffs_length]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hn'.le)
  rw [gamma0Rescale_qExpansion_coeff]
  simp only [List.getElem?_eq_getElem hindex, Option.getD_some, first_coeffs_getElem]

/-- Dilation one preserves a prefix without constructing an intermediate list. -/
theorem gamma0Rescale_first_coeffs_one {M : ℕ} (f : gamma0CuspForms M)
    (hd : 0 < (1 : ℕ)) (m : ℕ) :
    first_coeffs m (gamma0Rescale f 1 hd) = first_coeffs m f := by
  simp only [first_coeffs_eq_map_range, gamma0Rescale_qExpansion_coeff,
    Nat.one_dvd, ↓reduceIte, Nat.div_one]

/-- Use any sufficient source precision, allowing a tactic to supply a numeral. -/
theorem gamma0Rescale_first_coeffs_of_bound {M : ℕ} (f : gamma0CuspForms M)
    (d : ℕ) (hd : 0 < d) (m p : ℕ) (hp : m ≤ d * p) :
    first_coeffs m (gamma0Rescale f d hd) =
      rescaleCoefficients d m (first_coeffs p f) := by
  rw [first_coeffs_eq_map_range, rescaleCoefficients]
  apply List.map_congr_left
  intro n hn
  have hnm : n < m := List.mem_range.mp hn
  have hindex : n / d < (first_coeffs p f).length := by
    rw [first_coeffs_length]
    exact Nat.div_lt_of_lt_mul (lt_of_lt_of_le hnm hp)
  rw [gamma0Rescale_qExpansion_coeff]
  simp only [List.getElem?_eq_getElem hindex, Option.getD_some, first_coeffs_getElem]

@[simp] theorem gamma0RescaleToLevel_first_coeffs {M N : ℕ} (f : gamma0CuspForms M)
    (d : ℕ) (hMN : M * d ∣ N) (hd : 0 < d) (m : ℕ) :
    first_coeffs m (gamma0RescaleToLevel f d hMN hd) =
      first_coeffs m (gamma0Rescale f d hd) := rfl

@[simp] theorem gamma0Restrict_first_coeffs {M N : ℕ} (f : gamma0CuspForms M)
    (hMN : M ∣ N) (m : ℕ) : first_coeffs m (gamma0Restrict f hMN) = first_coeffs m f := rfl

end WeightTwoCusps
