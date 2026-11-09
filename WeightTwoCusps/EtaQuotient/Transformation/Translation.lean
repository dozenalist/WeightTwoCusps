module

public import WeightTwoCusps.EtaQuotient.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Translation and the first necessary Newman congruence

This follows Proposition 3.1 and Corollary 3.2 of David Savitt,
*An elementary proof of Newman's eta-quotient theorem* (2025),
<https://math.jhu.edu/~savitt/papers/pdfs/newman.pdf>.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Function Complex
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm Real

namespace WeightTwoCusps.EtaQuotient

/-- The primitive twenty-fourth root character in the transformation law of eta. -/
def translationCharacter : AddChar (ZMod 24) ℂ := ZMod.stdAddChar

@[simp] theorem translationCharacter_eq_one_iff (x : ZMod 24) :
    translationCharacter x = 1 ↔ x = 0 := by
  rw [← (translationCharacter.map_zero_eq_one)]
  exact ZMod.injective_stdAddChar.eq_iff

theorem eta_add_nat (z : ℂ) (n : ℕ) :
    ModularForm.eta (z + n) = translationCharacter n * ModularForm.eta z := by
  have hq : Periodic.qParam 1 (z + n) = Periodic.qParam 1 z := by
    simp only [Periodic.qParam, Complex.ofReal_one, div_one, mul_add]
    rw [Complex.exp_add]
    have hn : Complex.exp (2 * (π : ℂ) * I * n) = 1 := by
      rw [mul_comm (2 * (π : ℂ) * I), Complex.exp_nat_mul]
      simp [Complex.exp_two_pi_mul_I]
    rw [hn, mul_one]
  have hp : Periodic.qParam 24 (z + n) =
      translationCharacter n * Periodic.qParam 24 z := by
    rw [translationCharacter, show (n : ZMod 24) = ((n : ℤ) : ZMod 24) by simp,
      ZMod.stdAddChar_coe]
    simp only [Periodic.qParam, Complex.ofReal_ofNat, Int.cast_natCast,
      ← Complex.exp_add]
    congr 1
    ring
  simp only [ModularForm.eta, ModularForm.eta_q, hq, hp]
  ring

private theorem character_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 24) :
    translationCharacter (∑ i ∈ s, f i) = ∏ i ∈ s, translationCharacter (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, AddChar.map_add_eq_mul, ih]

/-- The full eta quotient is an eigenfunction of translation. -/
theorem transform_T (N : ℕ) (r : Fin N → ℤ) (z : ℍ) :
    etaQuotient N r (ModularGroup.T • z) =
      translationCharacter (infinitySum N r) * etaQuotient N r z := by
  simp only [etaQuotient, modular_T_smul, UpperHalfPlane.coe_vadd, Complex.ofReal_one]
  simp only [mul_add, mul_one]
  have hfactor (m : ℕ) : ModularForm.eta ((m : ℂ) + (m : ℂ) * (z : ℂ)) =
      translationCharacter m * ModularForm.eta ((m : ℂ) * (z : ℂ)) := by
    rw [add_comm, eta_add_nat]
  simp_rw [hfactor, mul_zpow]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [infinitySum, Int.cast_sum, character_sum]
  apply Finset.prod_congr rfl
  intro m hm
  rw [← AddChar.map_zsmul_eq_zpow]
  congr 1
  simp [zsmul_eq_mul, mul_comm]

theorem slash_T (N : ℕ) (r : Fin N → ℤ) (k : ℤ) :
    etaQuotient N r ∣[k] ModularGroup.T =
      translationCharacter (infinitySum N r) • etaQuotient N r := by
  ext z
  rw [ModularForm.SL_slash_apply, transform_T]
  simp [ModularGroup.denom_apply, ModularGroup.T]

/-- The first Newman congruence is necessary and sufficient for `T`-invariance. -/
theorem slash_T_eq_self_iff (N : ℕ) (r : Fin N → ℤ) (k : ℤ) :
    etaQuotient N r ∣[k] ModularGroup.T = etaQuotient N r ↔
      (24 : ℤ) ∣ infinitySum N r := by
  rw [slash_T]
  constructor
  · intro h
    have he := congrFun h UpperHalfPlane.I
    simp only [Pi.smul_apply, smul_eq_mul] at he
    have hx : translationCharacter (infinitySum N r) = 1 :=
      (mul_eq_right₀ (ne_zero N r UpperHalfPlane.I)).mp he
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 24).mp
      ((translationCharacter_eq_one_iff _).mp hx)
  · intro h
    have hx := (ZMod.intCast_zmod_eq_zero_iff_dvd (infinitySum N r) 24).mpr h
    rw [hx, AddChar.map_zero_eq_one, one_smul]

/-- Any genuine modular form equal to this eta quotient satisfies the first congruence. -/
theorem infinitySum_dvd_of_modularForm {N : ℕ} {r : Fin N → ℤ} {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (hf : (f : ℍ → ℂ) = etaQuotient N r) : (24 : ℤ) ∣ infinitySum N r := by
  apply (slash_T_eq_self_iff N r k).mp
  rw [← hf]
  exact SlashInvariantForm.slash_action_eqn f _
    (Subgroup.mem_map_of_mem _ (show ModularGroup.T ∈ CongruenceSubgroup.Gamma0 N by
      simp [CongruenceSubgroup.Gamma0_mem, ModularGroup.T]))

end WeightTwoCusps.EtaQuotient
