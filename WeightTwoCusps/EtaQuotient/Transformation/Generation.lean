module

public import WeightTwoCusps.EtaQuotient.Transformation.Inversion
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# Congruence descent for Newman's theorem

The group-theoretic part of Savitt's Proposition 3.8: a congruence subgroup
containing translation and the level-`N` lower translation contains `Γ₁(N)`.
Reference: <https://math.jhu.edu/~savitt/papers/pdfs/newman.pdf>.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace WeightTwoCusps.EtaQuotient

/-- Integral lower translation. -/
def lowerTranslation (n : ℤ) : SL(2, ℤ) := ⟨!![1, 0; n, 1], by simp⟩

private def lowerTranslationHom : Multiplicative ℤ →* SL(2, ℤ) where
  toFun n := lowerTranslation n.toAdd
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp [lowerTranslation]
  map_mul' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lowerTranslation, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Fin.sum_univ_two, add_comm]

theorem lowerTranslation_zpow (n t : ℤ) : lowerTranslation n ^ t = lowerTranslation (t * n) := by
  exact (lowerTranslationHom.map_zpow (Multiplicative.ofAdd n) t).symm

theorem lowerTranslation_neg_level (N : ℕ) : lowerTranslation (-(N : ℤ)) = lowerUnipotent N := by
  ext i j
  simp only [lowerTranslation, lowerUnipotent, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.SL2_inv_expl, ModularGroup.coe_S, ModularGroup.coe_T_zpow,
    Matrix.mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp [Matrix.vecMul]

private theorem lowerTranslation_mem_of_level {H : Subgroup SL(2, ℤ)} {N : ℕ}
    (hN : lowerUnipotent N ∈ H) (t : ℤ) : lowerTranslation (t * (N : ℤ)) ∈ H := by
  have h := H.zpow_mem hN (-t)
  rw [← lowerTranslation_neg_level, lowerTranslation_zpow, neg_mul_neg] at h
  exact h

/-- Adjoining `T` to a principal congruence subgroup supplies `Γ₁` at the same level. -/
theorem Gamma1_le_of_Gamma_le_of_T_mem {H : Subgroup SL(2, ℤ)} {M : ℕ}
    (hT : ModularGroup.T ∈ H) (hM : CongruenceSubgroup.Gamma M ≤ H) :
    CongruenceSubgroup.Gamma1 M ≤ H := by
  intro γ hγ
  obtain ⟨ha, hd, hc⟩ := (CongruenceSubgroup.Gamma1_mem M γ).mp hγ
  let δ := ModularGroup.T ^ (-(γ 0 1)) * γ
  have hδ : δ ∈ CongruenceSubgroup.Gamma M := by
    rw [CongruenceSubgroup.Gamma_mem]
    simp only [δ, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow,
      Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Int.cast_add, Int.cast_mul, Int.cast_neg,
      Int.cast_one, Int.cast_zero, ha, hd, hc]
    simp
  have hδH := hM hδ
  have heq : γ = ModularGroup.T ^ (γ 0 1) * δ := by
    simp [δ, ← mul_assoc]
  rw [heq]
  exact H.mul_mem (H.zpow_mem hT _) hδH

private theorem T_mul_entries (t : ℤ) (γ : SL(2, ℤ)) :
    (ModularGroup.T ^ t * γ) 0 0 = γ 0 0 + t * γ 1 0 ∧
    (ModularGroup.T ^ t * γ) 1 0 = γ 1 0 := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow,
    Matrix.mul_apply, Fin.sum_univ_two]
  simp

private theorem lower_mul_entries (t : ℤ) (γ : SL(2, ℤ)) :
    (lowerTranslation t * γ) 0 0 = γ 0 0 ∧
    (lowerTranslation t * γ) 1 0 = t * γ 0 0 + γ 1 0 := by
  simp [lowerTranslation, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem det_cast (M : ℕ) (γ : SL(2, ℤ)) :
    (γ 0 0 : ZMod M) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have hd := congrArg (Int.cast : ℤ → ZMod M) γ.det_coe
  simpa only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one] using hd

private theorem mem_of_unit_lower_coefficient {H : Subgroup SL(2, ℤ)} {N p : ℕ}
    [Fact p.Prime] (hT : ModularGroup.T ∈ H) (hL : lowerUnipotent N ∈ H)
    (hdeep : CongruenceSubgroup.Gamma1 (p * N) ≤ H) (γ : SL(2, ℤ)) (a c : ℤ)
    (ha : γ 0 0 = 1 + (N : ℤ) * a) (hc : γ 1 0 = (N : ℤ) * c)
    (hu : (c : ZMod p) ≠ 0) : γ ∈ H := by
  let t : ℤ := ((a : ZMod p) / (c : ZMod p)).val
  have ht : (p : ℤ) ∣ a - t * c := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    simp only [Int.cast_sub, Int.cast_mul, t, Int.cast_natCast, ZMod.natCast_zmod_val]
    field_simp
    ring
  obtain ⟨s, hs⟩ := ht
  let δ := ModularGroup.T ^ (-t) * γ
  have hδa : ((p * N : ℕ) : ℤ) ∣ δ 0 0 - 1 := by
    refine ⟨s, ?_⟩
    rw [(T_mul_entries (-t) γ).1, ha, hc]
    push_cast
    linear_combination (N : ℤ) * hs
  let ε := lowerTranslation ((-c) * (N : ℤ)) * δ
  have hεa : (ε 0 0 : ZMod (p * N)) = 1 := by
    have hcast := (ZMod.intCast_zmod_eq_zero_iff_dvd (δ 0 0 - 1) (p * N)).mpr hδa
    rw [(lower_mul_entries _ δ).1]
    simpa only [Int.cast_sub, Int.cast_one, sub_eq_zero] using hcast
  have hεc : (ε 1 0 : ZMod (p * N)) = 0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    have he : ε 1 0 = -(c * (N : ℤ)) * (δ 0 0 - 1) := by
      rw [(lower_mul_entries _ δ).2, show δ 1 0 = γ 1 0 from (T_mul_entries (-t) γ).2, hc]
      ring
    rw [he]
    exact dvd_mul_of_dvd_right hδa _
  have hε : ε ∈ CongruenceSubgroup.Gamma1 (p * N) := by
    apply (CongruenceSubgroup.Gamma1_mem _ _).mpr
    refine ⟨hεa, ?_, hεc⟩
    simpa only [hεa, hεc, one_mul, mul_zero, sub_zero] using det_cast (p * N) ε
  have hδH : δ ∈ H := (H.mul_mem_cancel_left (lowerTranslation_mem_of_level hL (-c))).mp
    (hdeep hε)
  exact (H.mul_mem_cancel_left (H.zpow_mem hT (-t))).mp hδH

/-- Removing one prime factor from the auxiliary congruence level. -/
theorem Gamma1_le_of_prime_mul_level {H : Subgroup SL(2, ℤ)} {N p : ℕ}
    [Fact p.Prime] (hT : ModularGroup.T ∈ H) (hL : lowerUnipotent N ∈ H)
    (hdeep : CongruenceSubgroup.Gamma1 (p * N) ≤ H) :
    CongruenceSubgroup.Gamma1 N ≤ H := by
  intro γ hγ
  obtain ⟨hγa, _, hγc⟩ := (CongruenceSubgroup.Gamma1_mem N γ).mp hγ
  have haD : (N : ℤ) ∣ γ 0 0 - 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp
    simpa only [Int.cast_sub, Int.cast_one, sub_eq_zero] using hγa
  have hcD : (N : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hγc
  obtain ⟨a, ha⟩ := haD
  obtain ⟨c, hc⟩ := hcD
  have ha' : γ 0 0 = 1 + (N : ℤ) * a := by linear_combination ha
  by_cases hc0 : (c : ZMod p) = 0
  · let θ := lowerTranslation (N : ℤ) * γ
    have hθa : θ 0 0 = 1 + (N : ℤ) * a := by
      rw [(lower_mul_entries _ γ).1, ha']
    have hθc : θ 1 0 = (N : ℤ) * (γ 0 0 + c) := by
      rw [(lower_mul_entries _ γ).2, hc]
      ring
    have hunit : ((γ 0 0 + c : ℤ) : ZMod p) ≠ 0 := by
      simp only [Int.cast_add, hc0, add_zero]
      intro hz
      have hcz : (γ 1 0 : ZMod p) = 0 := by simp [hc, hc0]
      have hd := det_cast p γ
      simp only [hz, hcz, zero_mul, mul_zero, sub_self, zero_ne_one] at hd
    have hθ := mem_of_unit_lower_coefficient hT hL hdeep θ a (γ 0 0 + c) hθa hθc hunit
    exact (H.mul_mem_cancel_left (by simpa using lowerTranslation_mem_of_level hL 1)).mp hθ
  · exact mem_of_unit_lower_coefficient hT hL hdeep γ a c ha' hc hc0

/-- Repeated prime descent removes every positive auxiliary level factor. -/
theorem Gamma1_le_of_mul_level {H : Subgroup SL(2, ℤ)} {N : ℕ}
    (hT : ModularGroup.T ∈ H) (hL : lowerUnipotent N ∈ H) (D : ℕ) (hD : 0 < D)
    (hdeep : CongruenceSubgroup.Gamma1 (D * N) ≤ H) :
    CongruenceSubgroup.Gamma1 N ≤ H := by
  induction D using Nat.strong_induction_on with
  | h D ih =>
    by_cases hD1 : D = 1
    · simpa only [hD1, one_mul] using hdeep
    · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hD1
      have : Fact p.Prime := ⟨hp⟩
      have hdpos : 0 < D / p := Nat.div_pos (Nat.le_of_dvd hD hpd) hp.pos
      have hdlt : D / p < D := Nat.div_lt_self hD hp.one_lt
      have hLd : lowerUnipotent (D / p * N) ∈ H := by
        simpa only [neg_mul, ← Nat.cast_mul, lowerTranslation_neg_level] using
          lowerTranslation_mem_of_level hL (-(D / p : ℕ) : ℤ)
      have hdeep' : CongruenceSubgroup.Gamma1 (p * (D / p * N)) ≤ H := by
        simpa only [← mul_assoc, Nat.mul_div_cancel' hpd] using hdeep
      exact ih (D / p) hdlt hdpos (Gamma1_le_of_prime_mul_level hT hLd hdeep')

private theorem Gamma_le_of_dvd {M L : ℕ} (hML : M ∣ L) :
    CongruenceSubgroup.Gamma L ≤ CongruenceSubgroup.Gamma M := by
  intro γ hγ
  obtain ⟨ha, hb, hc, hd⟩ := (CongruenceSubgroup.Gamma_mem).mp hγ
  let φ : ZMod L →+* ZMod M := ZMod.castHom hML _
  apply CongruenceSubgroup.Gamma_mem.mpr
  exact ⟨by simpa only [map_one, map_intCast] using congrArg φ ha,
    by simpa [φ] using congrArg φ hb,
    by simpa [φ] using congrArg φ hc,
    by simpa only [map_one, map_intCast] using congrArg φ hd⟩

/-- Savitt's congruence-subgroup generation theorem (Proposition 3.8).
The congruence hypothesis is essential: the two translations alone do not
generate `Γ₁(N)` in general. -/
theorem Gamma1_le_of_isCongruenceSubgroup {H : Subgroup SL(2, ℤ)} (N : ℕ)
    (hH : CongruenceSubgroup.IsCongruenceSubgroup H)
    (hT : ModularGroup.T ∈ H) (hL : lowerUnipotent N ∈ H) :
    CongruenceSubgroup.Gamma1 N ≤ H := by
  obtain ⟨M, hM, hMH⟩ := hH
  have hprincipal : CongruenceSubgroup.Gamma (M * N) ≤ H :=
    (Gamma_le_of_dvd (dvd_mul_right M N)).trans hMH
  exact Gamma1_le_of_mul_level hT hL M (Nat.pos_of_ne_zero hM)
    (Gamma1_le_of_Gamma_le_of_T_mem hT hprincipal)

/-- The subgroup fixing a function under the weight-`k` slash action. -/
def slashStabilizer (f : ℍ → ℂ) (k : ℤ) : Subgroup SL(2, ℤ) where
  carrier := {γ | f ∣[k] γ = f}
  one_mem' := by
    change f ∣[k] (1 : SL(2, ℤ)) = f
    exact SlashAction.slash_one k f
  mul_mem' {γ δ} hγ hδ := by
    change f ∣[k] γ = f at hγ
    change f ∣[k] δ = f at hδ
    change f ∣[k] (γ * δ) = f
    rw [SlashAction.slash_mul, hγ, hδ]
  inv_mem' {γ} hγ := by
    change f ∣[k] γ = f at hγ
    change f ∣[k] γ⁻¹ = f
    have he := congrArg (fun g : ℍ → ℂ ↦ g ∣[k] γ⁻¹) hγ
    simpa only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one] using he.symm

/-- Modular invariance at some congruence level descends to `Γ₁(N)` once the
two Newman translations fix the function. This does not assume that an
arbitrary eta quotient already has congruence-level invariance. -/
theorem slash_Gamma1_of_congruence_invariance (N : ℕ) (f : ℍ → ℂ) (k : ℤ)
    (hcong : CongruenceSubgroup.IsCongruenceSubgroup (slashStabilizer f k))
    (hT : f ∣[k] ModularGroup.T = f) (hL : f ∣[k] lowerUnipotent N = f)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma1 N) : f ∣[k] γ = f := by
  exact Gamma1_le_of_isCongruenceSubgroup N hcong hT hL hγ

end WeightTwoCusps.EtaQuotient
