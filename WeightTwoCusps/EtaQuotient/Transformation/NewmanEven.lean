module

public import WeightTwoCusps.EtaQuotient.Transformation.CoprimeLevel

/-!
# Newman's transformation criterion for even exponents

The eta-square character suffices when every exponent is even. This proves
the transformation part at arbitrary positive level. As in the classical
proof, translate a matrix until its upper-left entry is prime to six, then
evaluate its multiplier from the two weighted sums.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped MatrixGroups ModularForm
open UpperHalfPlane

namespace WeightTwoCusps.EtaQuotient

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- This is a finite kernel check of the eta-square formula modulo twelve.
private theorem residue_unit_formula : ∀ a b c d : ZMod 12,
    IsUnit a → a * d - b * c = 1 →
      Eta.etaExponentResidue a b c d = a * (b - c) + 3 * (a - 1) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the constant term at each unit modulo twelve.
private theorem residue_even_constant : ∀ a t : ZMod 12,
    IsUnit a → 3 * (a - 1) * (t + t) = 0 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exhaust the finite residue matrices to find an admissible translation.
private theorem exists_unit_shift : ∀ a b c d : ZMod 12,
    a * d - b * c = 1 → ∃ t : ZMod 12, IsUnit (a + t * c) := by
  decide +kernel

private theorem det_mod_twelve (γ : SL(2, ℤ)) :
    (γ 0 0 : ZMod 12) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have hd := congrArg (Int.cast : ℤ → ZMod 12) γ.det_coe
  simpa only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one] using hd

private theorem lower_left_div_factor {N m : ℕ} (hm : m ∈ N.divisors)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    γ 1 0 / (m : ℤ) = (γ 1 0 / (N : ℤ)) * (N / m : ℕ) := by
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hm).ne'
  apply mul_right_cancel₀ hm0
  rw [Eta.lower_left_div_mul m γ (mem_Gamma0_divisor (Nat.dvd_of_mem_divisors hm) γ hγ)]
  have he : ((N / m : ℕ) : ℤ) * m = N := by
    exact_mod_cast Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hm)
  rw [mul_assoc, he, Eta.lower_left_div_mul N γ hγ]

private theorem squareMultiplierExponent_eq_zero_of_unit {N : ℕ} (r : Fin N → ℤ)
    (heven : Even (exponentSum N r))
    (hInfty : (12 : ℤ) ∣ infinitySum N r) (hzero : (12 : ℤ) ∣ zeroSum N r)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    (ha : IsUnit (γ 0 0 : ZMod 12)) : squareMultiplierExponent N r γ hγ = 0 := by
  have hfactor (m : {m // m ∈ N.divisors}) :
      Eta.etaExponent (divisorConjugate N γ hγ m m.property) =
        (γ 0 0 : ZMod 12) * ((m : ℕ) * (γ 0 1 : ZMod 12) -
          (γ 1 0 / N : ℤ) * (N / (m : ℕ) : ℕ)) + 3 * ((γ 0 0 : ZMod 12) - 1) := by
    have hf := residue_unit_formula
      (divisorConjugate N γ hγ m m.property 0 0)
      (divisorConjugate N γ hγ m m.property 0 1)
      (divisorConjugate N γ hγ m m.property 1 0)
      (divisorConjugate N γ hγ m m.property 1 1) ha
      (det_mod_twelve (divisorConjugate N γ hγ m m.property))
    change Eta.etaExponentResidue _ _ _ _ = _
    rw [hf]
    change (γ 0 0 : ZMod 12) * ((((m : ℤ) * γ 0 1 : ℤ) : ZMod 12) -
      ((γ 1 0 / (m : ℤ) : ℤ) : ZMod 12)) + 3 * ((γ 0 0 : ZMod 12) - 1) = _
    rw [lower_left_div_factor m.property γ hγ]
    simp only [Int.cast_mul, Int.cast_natCast]
  have hs : squareMultiplierExponent N r γ hγ =
      ((γ 0 0 : ZMod 12) * γ 0 1) * (infinitySum N r : ZMod 12) -
      ((γ 0 0 : ZMod 12) * (γ 1 0 / N : ℤ)) * (zeroSum N r : ZMod 12) +
      (3 * ((γ 0 0 : ZMod 12) - 1)) * (exponentSum N r : ZMod 12) := by
    rw [squareMultiplierExponent]
    simp_rw [hfactor]
    rw [infinitySum, zeroSum, exponentSum, Int.cast_sum, Int.cast_sum, Int.cast_sum]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    calc _ = ∑ m ∈ N.divisors,
        (exponent r m : ZMod 12) * ((γ 0 0 : ZMod 12) * ((m : ZMod 12) * γ 0 1 -
          (γ 1 0 / N : ℤ) * (N / m : ℕ)) + 3 * ((γ 0 0 : ZMod 12) - 1)) :=
      Finset.sum_attach N.divisors (fun m : ℕ ↦
        (exponent r m : ZMod 12) * ((γ 0 0 : ZMod 12) * ((m : ZMod 12) * γ 0 1 -
          (γ 1 0 / N : ℤ) * (N / m : ℕ)) + 3 * ((γ 0 0 : ZMod 12) - 1)))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro m hm
        simp only [Int.cast_mul, Int.cast_natCast]
        ring
  rw [hs, (ZMod.intCast_zmod_eq_zero_iff_dvd (infinitySum N r) 12).mpr hInfty,
    (ZMod.intCast_zmod_eq_zero_iff_dvd (zeroSum N r) 12).mpr hzero, mul_zero, mul_zero,
    sub_zero, zero_add]
  obtain ⟨t, ht⟩ := heven
  rw [ht, Int.cast_add]
  exact residue_even_constant _ _ ha

/-- The transformation part of Newman for even exponents, at any level.
Both congruences are modulo twelve because the actual exponent function is `double r`. -/
theorem double_slash_Gamma0_of_newman (N : ℕ) (r : Fin N → ℤ)
    (heven : Even (exponentSum N r))
    (hInfty : (12 : ℤ) ∣ infinitySum N r) (hzero : (12 : ℤ) ∣ zeroSum N r)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    etaQuotient N (double r) ∣[exponentSum N r] γ = etaQuotient N (double r) := by
  obtain ⟨t, ht⟩ := exists_unit_shift _ _ _ _ (det_mod_twelve γ)
  let δ : SL(2, ℤ) := ModularGroup.T ^ (t.val : ℤ) * γ
  have hTmem : ModularGroup.T ^ (t.val : ℤ) ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    simp only [ModularGroup.coe_T_zpow]
    norm_num
  have hδ : δ ∈ CongruenceSubgroup.Gamma0 N :=
    (CongruenceSubgroup.Gamma0 N).mul_mem hTmem hγ
  have hδa : IsUnit (δ 0 0 : ZMod 12) := by
    have he : (δ 0 0 : ZMod 12) = (γ 0 0 : ZMod 12) + t * γ 1 0 := by
      simp only [δ, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow,
        Matrix.mul_apply, Fin.sum_univ_two]
      simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, one_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast,
        ZMod.natCast_zmod_val]
    rwa [he]
  have hδinv : etaQuotient N (double r) ∣[exponentSum N r] δ = etaQuotient N (double r) := by
    have heq : etaQuotient N (double r) = fun z ↦ etaQuotient N r z ^ 2 := funext (double_apply N r)
    rw [heq]
    exact (square_slash_eq_self_iff N r δ hδ).mpr
      (squareMultiplierExponent_eq_zero_of_unit r heven hInfty hzero δ hδ hδa)
  have hT : etaQuotient N (double r) ∣[exponentSum N r] ModularGroup.T =
      etaQuotient N (double r) := by
    apply (slash_T_eq_self_iff N (double r) (exponentSum N r)).mpr
    rw [infinitySum_double]
    obtain ⟨v, hv⟩ := hInfty
    exact ⟨v, by omega⟩
  have hpow (n : ℕ) : etaQuotient N (double r) ∣[exponentSum N r] (ModularGroup.T ^ n) =
      etaQuotient N (double r) := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, SlashAction.slash_mul, ih, hT]
  simpa only [δ, SlashAction.slash_mul, zpow_natCast, hpow] using hδinv

end WeightTwoCusps.EtaQuotient
