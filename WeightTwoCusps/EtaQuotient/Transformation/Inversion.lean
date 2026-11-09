module

public import WeightTwoCusps.EtaQuotient.Transformation.Translation

/-!
# Inversion and the second Newman congruence

Following Savitt, Proposition 3.1 and Corollary 3.2, inversion interchanges
the two endpoint congruences. The intermediate reciprocal dilation product
avoids reindexing the exponent function by the involution `m ↦ N/m`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Function Complex
open UpperHalfPlane hiding I
open scoped Topology MatrixGroups ModularForm Real

namespace WeightTwoCusps.EtaQuotient

private theorem sqrt_pos_mul (a : ℝ) (ha : 0 < a) (z : ℂ) (hz : z ≠ 0) :
    Complex.sqrt ((a : ℂ) * z) = Complex.sqrt (a : ℂ) * Complex.sqrt z := by
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [sqrt_eq_exp (mul_ne_zero ha0 hz), sqrt_eq_exp ha0,
    sqrt_eq_exp hz, Complex.log_ofReal_mul ha hz, Complex.ofReal_log ha.le,
    add_div, Complex.exp_add]

/-- The product with reciprocal dilation factors. -/
def reciprocalProduct (N : ℕ) (r : Fin N → ℤ) (z : ℍ) : ℂ :=
  ∏ m ∈ N.divisors, ModularForm.eta ((z : ℂ) / m) ^ exponent r m

theorem reciprocalProduct_ne_zero (N : ℕ) (r : Fin N → ℤ) (z : ℍ) :
    reciprocalProduct N r z ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro m hm
  apply zpow_ne_zero
  apply ModularForm.eta_ne_zero
  simpa using div_pos z.im_pos (show (0 : ℝ) < m by exact_mod_cast Nat.pos_of_mem_divisors hm)

/-- The nonzero scalar in the `S`-transformation. -/
def inversionConstant (N : ℕ) (r : Fin N → ℤ) : ℂ :=
  ∏ m ∈ N.divisors,
    ((Complex.sqrt I)⁻¹ * Complex.sqrt ((1 : ℂ) / m)) ^ exponent r m

theorem inversionConstant_ne_zero (N : ℕ) (r : Fin N → ℤ) : inversionConstant N r ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro m hm
  apply zpow_ne_zero
  apply mul_ne_zero
  · apply inv_ne_zero
    simp [Complex.sqrt, Complex.cpow_eq_zero_iff]
  · have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hm).ne'
    simp [Complex.sqrt, Complex.cpow_eq_zero_iff, hm0]

private theorem prod_const_zpow {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (a : ℂ) (ha : a ≠ 0) : (∏ i ∈ s, a ^ f i) = a ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, zpow_add₀ ha]

private theorem eta_dilate_S {m : ℕ} (hm : 0 < m) (z : ℍ) :
    ModularForm.eta ((m : ℂ) * (ModularGroup.S • z : ℍ)) =
      ((Complex.sqrt I)⁻¹ * Complex.sqrt ((1 : ℂ) / m)) *
        Complex.sqrt (z : ℂ) * ModularForm.eta ((z : ℂ) / m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  let w := Eta.dilate (1 / m) (one_div_pos.mpr hmR) z
  have hw : (w : ℂ) = (z : ℂ) / m := by simp [w, div_eq_mul_inv, mul_comm]
  have h := ModularForm.eta_comp_eq_csqrt_I_inv w.im_pos
  simp only [Function.comp_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at h
  have harg : (m : ℂ) * (ModularGroup.S • z : ℍ) = -(1 : ℂ) / (w : ℂ) := by
    rw [modular_S_smul, UpperHalfPlane.coe_mk, hw]
    field_simp
  rw [harg, h, hw]
  have hs : Complex.sqrt ((z : ℂ) / m) =
      Complex.sqrt ((1 : ℂ) / m) * Complex.sqrt (z : ℂ) := by
    simpa [div_eq_mul_inv, mul_comm] using sqrt_pos_mul (1 / m)
      (one_div_pos.mpr hmR) (z : ℂ) z.ne_zero
  rw [hs]
  ring

/-- Integral weight makes the square-root factors combine into `z^k`. -/
theorem transform_S {N : ℕ} {r : Fin N → ℤ} {k : ℤ} (hk : HasWeight N r k) (z : ℍ) :
    etaQuotient N r (ModularGroup.S • z) =
      inversionConstant N r * (z : ℂ) ^ k * reciprocalProduct N r z := by
  rw [etaQuotient, ← Finset.prod_attach N.divisors]
  have hfactor (m : {m // m ∈ N.divisors}) := eta_dilate_S (Nat.pos_of_mem_divisors m.property) z
  simp_rw [hfactor, mul_zpow]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  rw [prod_const_zpow _ _ _ (by
    simpa [Complex.sqrt, Complex.cpow_eq_zero_iff] using z.ne_zero)]
  simp only [Finset.sum_attach]
  change _ * Complex.sqrt (z : ℂ) ^ exponentSum N r * _ = _
  rw [hk, zpow_mul, zpow_ofNat, show Complex.sqrt (z : ℂ) ^ 2 = (z : ℂ) from
    Complex.cpow_ofNat_inv_pow (z : ℂ) 2]
  congr 1
  · apply congrArg (fun a : ℂ ↦ a * (z : ℂ) ^ k)
    simpa only [inversionConstant, mul_zpow] using Finset.prod_attach N.divisors (fun m : ℕ ↦
      ((Complex.sqrt I)⁻¹ * Complex.sqrt ((1 : ℂ) / (m : ℂ))) ^ exponent r m)
  · exact Finset.prod_attach N.divisors
      (fun m : ℕ ↦ ModularForm.eta ((z : ℂ) / (m : ℂ)) ^ exponent r m)

theorem slash_S {N : ℕ} {r : Fin N → ℤ} {k : ℤ} (hk : HasWeight N r k) :
    etaQuotient N r ∣[k] ModularGroup.S = inversionConstant N r • reciprocalProduct N r := by
  ext z
  rw [ModularForm.SL_slash_apply, transform_S hk z, ModularGroup.denom_S]
  simp only [Pi.smul_apply, smul_eq_mul, zpow_neg]
  field_simp [z.ne_zero]

private theorem character_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 24) :
    translationCharacter (∑ i ∈ s, f i) = ∏ i ∈ s, translationCharacter (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, AddChar.map_add_eq_mul, ih]

theorem reciprocalProduct_transform_T_level (N : ℕ) (r : Fin N → ℤ) (z : ℍ) :
    reciprocalProduct N r (ModularGroup.T ^ (N : ℤ) • z) =
      translationCharacter (zeroSum N r) * reciprocalProduct N r z := by
  simp only [reciprocalProduct, modular_T_zpow_smul, coe_vadd,
    Int.cast_natCast, Complex.ofReal_natCast]
  rw [← Finset.prod_attach N.divisors]
  have hfactor (m : {m // m ∈ N.divisors}) :
      ModularForm.eta (((N : ℂ) + (z : ℂ)) / (m : ℕ)) =
        translationCharacter (N / (m : ℕ)) * ModularForm.eta ((z : ℂ) / (m : ℕ)) := by
    have hm0 : ((m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors m.property).ne'
    have hdiv : ((N / (m : ℕ) : ℕ) : ℂ) = (N : ℂ) / (m : ℕ) := by
      apply (eq_div_iff hm0).mpr
      exact_mod_cast Nat.div_mul_cancel (Nat.dvd_of_mem_divisors m.property)
    rw [add_div, add_comm, ← hdiv, eta_add_nat]
  simp_rw [hfactor, mul_zpow]
  rw [Finset.prod_mul_distrib]
  rw [zeroSum, Int.cast_sum, character_sum]
  congr 1
  · rw [Finset.prod_attach N.divisors (fun m : ℕ ↦
      translationCharacter (N / m : ℕ) ^ exponent r m)]
    apply Finset.prod_congr rfl
    intro m hm
    rw [← AddChar.map_zsmul_eq_zpow]
    congr 1
    simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_natCast, mul_comm]
  · exact Finset.prod_attach N.divisors
      (fun m : ℕ ↦ ModularForm.eta ((z : ℂ) / (m : ℂ)) ^ exponent r m)

/-- A lower unipotent matrix; its lower-left entry is `-N`. -/
def lowerUnipotent (N : ℕ) : SL(2, ℤ) :=
  ModularGroup.S * ModularGroup.T ^ (N : ℤ) * ModularGroup.S⁻¹

theorem lowerUnipotent_mem (N : ℕ) : lowerUnipotent N ∈ CongruenceSubgroup.Gamma0 N := by
  rw [CongruenceSubgroup.Gamma0_mem]
  simp only [lowerUnipotent, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.SL2_inv_expl, ModularGroup.coe_S, ModularGroup.coe_T_zpow,
    Matrix.mul_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The second congruence is exactly lower-unipotent invariance. -/
theorem slash_lower_eq_self_iff {N : ℕ} {r : Fin N → ℤ} {k : ℤ} (hk : HasWeight N r k) :
    etaQuotient N r ∣[k] lowerUnipotent N = etaQuotient N r ↔
      (24 : ℤ) ∣ zeroSum N r := by
  have hconj : etaQuotient N r ∣[k] lowerUnipotent N = etaQuotient N r ↔
      (etaQuotient N r ∣[k] ModularGroup.S) ∣[k] (ModularGroup.T ^ (N : ℤ)) =
        etaQuotient N r ∣[k] ModularGroup.S := by
    constructor
    · intro h
      have he := congrArg (fun f : ℍ → ℂ ↦ f ∣[k] ModularGroup.S) h
      simpa [lowerUnipotent, SlashAction.slash_mul, ← SlashAction.slash_mul, mul_assoc] using he
    · intro h
      have he := congrArg (fun f : ℍ → ℂ ↦ f ∣[k] ModularGroup.S⁻¹) h
      simpa [lowerUnipotent, SlashAction.slash_mul, ← SlashAction.slash_mul, mul_assoc] using he
  rw [hconj, slash_S hk, ModularForm.SL_smul_slash]
  have ht : reciprocalProduct N r ∣[k] (ModularGroup.T ^ (N : ℤ)) =
      translationCharacter (zeroSum N r) • reciprocalProduct N r := by
    ext z
    have hd : denom ((ModularGroup.T ^ (N : ℤ)) : SL(2, ℤ)) z = 1 := by
      change (((ModularGroup.T ^ (N : ℤ)) 1 0 : ℤ) : ℂ) * (z : ℂ) +
        ((ModularGroup.T ^ (N : ℤ)) 1 1 : ℤ) = 1
      simp only [ModularGroup.coe_T_zpow]
      norm_num
    rw [ModularForm.SL_slash_apply, reciprocalProduct_transform_T_level, hd]
    simp
  rw [ht, smul_smul]
  constructor
  · intro h
    have he := congrFun h UpperHalfPlane.I
    simp only [Pi.smul_apply, smul_eq_mul] at he
    have hx : translationCharacter (zeroSum N r) = 1 := by
      apply mul_left_cancel₀ (inversionConstant_ne_zero N r)
      apply mul_right_cancel₀ (reciprocalProduct_ne_zero N r UpperHalfPlane.I)
      simpa only [mul_one] using he
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 24).mp
      ((translationCharacter_eq_one_iff _).mp hx)
  · intro h
    rw [(ZMod.intCast_zmod_eq_zero_iff_dvd (zeroSum N r) 24).mpr h,
      AddChar.map_zero_eq_one, mul_one]

theorem zeroSum_dvd_of_modularForm {N : ℕ} {r : Fin N → ℤ} {k : ℤ} (hk : HasWeight N r k)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (hf : (f : ℍ → ℂ) = etaQuotient N r) : (24 : ℤ) ∣ zeroSum N r := by
  apply (slash_lower_eq_self_iff hk).mp
  rw [← hf]
  exact SlashInvariantForm.slash_action_eqn f _
    (Subgroup.mem_map_of_mem _ (lowerUnipotent_mem N))

end WeightTwoCusps.EtaQuotient
