module

public import WeightTwoCusps.EtaQuotient.Transformation.Basic
public import WeightTwoCusps.EtaQuotient.Transformation.Translation

/-!
# Eta-square multipliers at levels prime to six

For a dilation factor prime to six, conjugating a modular matrix multiplies
its eta-square character exponent by that dilation factor modulo twelve.
Consequently a single Newman congruence proves modular transformation for
eta quotients whose exponents are all even at these levels.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped MatrixGroups ModularForm
open UpperHalfPlane

namespace WeightTwoCusps.EtaQuotient

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks all residue matrices over the three-element ring.
private theorem three_scaling : ∀ u a b c d : ZMod 3,
    u ^ 2 = 1 → a * d - b * c = 1 →
      Eta.exponentThree a (u * b) (u * c) d = u * Eta.exponentThree a b c d := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks all residue matrices over the four-element ring.
private theorem four_scaling : ∀ u a b c d : ZMod 4,
    u ^ 2 = 1 → a * d - b * c = 1 →
      Eta.exponentFour a (u * b) (u * c) d = u * Eta.exponentFour a b c d := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- These finite scalar-compatibility checks cover the two CRT inclusions.
private theorem lift_scaling :
    (∀ (u : ZMod 12) (x : ZMod 3), Eta.liftThree (Eta.reduceThree u * x) = u * Eta.liftThree x) ∧
    (∀ (u : ZMod 12) (x : ZMod 4), Eta.liftFour (Eta.reduceFour u * x) = u * Eta.liftFour x) := by
  decide +kernel

theorem etaExponentResidue_scaling (u a b c d : ZMod 12)
    (hu : u ^ 2 = 1) (hdet : a * d - b * c = 1) :
    Eta.etaExponentResidue a (u * b) (u * c) d = u * Eta.etaExponentResidue a b c d := by
  have hu3 : Eta.reduceThree u ^ 2 = 1 := by simpa using congrArg Eta.reduceThree hu
  have hu4 : Eta.reduceFour u ^ 2 = 1 := by simpa using congrArg Eta.reduceFour hu
  have hd3 : Eta.reduceThree a * Eta.reduceThree d - Eta.reduceThree b * Eta.reduceThree c = 1 := by
    simpa using congrArg Eta.reduceThree hdet
  have hd4 : Eta.reduceFour a * Eta.reduceFour d - Eta.reduceFour b * Eta.reduceFour c = 1 := by
    simpa using congrArg Eta.reduceFour hdet
  simp only [Eta.etaExponentResidue, map_mul, three_scaling _ _ _ _ _ hu3 hd3,
    four_scaling _ _ _ _ _ hu4 hd4, lift_scaling.1, lift_scaling.2, mul_add]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Exhaust the twelve residues and their decidable unit conditions in the kernel.
private theorem unit_square : ∀ x : ZMod 12, IsUnit x → x ^ 2 = 1 := by
  decide +kernel

/-- The character exponent at a divisor coprime to twelve. -/
theorem etaExponent_divisorConjugate {N m : ℕ} (hm : m ∈ N.divisors)
    (hunit : IsUnit (m : ZMod 12)) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    Eta.etaExponent (divisorConjugate N γ hγ m hm) = (m : ZMod 12) * Eta.etaExponent γ := by
  have hs := unit_square (m : ZMod 12) hunit
  have hc : ((γ 1 0 / m : ℤ) : ZMod 12) = (m : ZMod 12) * (γ 1 0 : ZMod 12) := by
    have he := congrArg (Int.cast : ℤ → ZMod 12)
      (Eta.lower_left_div_mul m γ (mem_Gamma0_divisor (Nat.dvd_of_mem_divisors hm) γ hγ))
    push_cast at he
    calc ((γ 1 0 / m : ℤ) : ZMod 12)
        = (m : ZMod 12) ^ 2 * ((γ 1 0 / m : ℤ) : ZMod 12) := by rw [hs, one_mul]
      _ = (m : ZMod 12) * (γ 1 0 : ZMod 12) := by
        rw [pow_two]
        linear_combination (m : ZMod 12) * he
  change Eta.etaExponentResidue (γ 0 0) ((m : ℤ) * γ 0 1 : ℤ) (γ 1 0 / (m : ℤ) : ℤ)
    (γ 1 1) = _
  push_cast
  rw [hc]
  apply etaExponentResidue_scaling _ _ _ _ _ hs
  have hd := congrArg (Int.cast : ℤ → ZMod 12) γ.det_coe
  simpa only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one] using hd

/-- For levels coprime to twelve, the square multiplier depends only on the
weighted exponent sum. -/
theorem squareMultiplierExponent_of_coprime {N : ℕ} (hN : N.Coprime 12) (r : Fin N → ℤ)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    squareMultiplierExponent N r γ hγ = (infinitySum N r : ZMod 12) * Eta.etaExponent γ := by
  rw [squareMultiplierExponent]
  have hfactor (m : {m // m ∈ N.divisors}) :
      Eta.etaExponent (divisorConjugate N γ hγ m m.property) =
        (m : ℕ) * Eta.etaExponent γ := by
    apply etaExponent_divisorConjugate m.property
    apply (ZMod.isUnit_iff_coprime _ _).mpr
    exact hN.of_dvd_left (Nat.dvd_of_mem_divisors m.property)
  simp_rw [hfactor, ← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  rw [infinitySum, Int.cast_sum]
  calc (∑ m ∈ N.divisors.attach, (exponent r m : ZMod 12) * (m : ℕ))
      = ∑ m ∈ N.divisors, (exponent r m : ZMod 12) * m :=
        Finset.sum_attach N.divisors (fun m : ℕ ↦ (exponent r m : ZMod 12) * (m : ZMod 12))
    _ = _ := by apply Finset.sum_congr rfl; intro m hm; push_cast; ring

/-- The sufficient transformation part of Newman for even exponent functions and
levels coprime to six. The function `double r` contains the actual exponents. -/
theorem double_slash_Gamma0 {N : ℕ} (hN : N.Coprime 12) (r : Fin N → ℤ)
    (hcong : (12 : ℤ) ∣ infinitySum N r)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    etaQuotient N (double r) ∣[exponentSum N r] γ = etaQuotient N (double r) := by
  have heq : etaQuotient N (double r) = fun z ↦ etaQuotient N r z ^ 2 :=
    funext (double_apply N r)
  rw [heq]
  apply (square_slash_eq_self_iff N r γ hγ).mpr
  rw [squareMultiplierExponent_of_coprime hN,
    (ZMod.intCast_zmod_eq_zero_iff_dvd (infinitySum N r) 12).mpr hcong, zero_mul]

/-- In this even-exponent case one Newman congruence is also necessary. -/
theorem double_slash_Gamma0_iff {N : ℕ} (hN : N.Coprime 12) (r : Fin N → ℤ) :
    (∀ γ ∈ CongruenceSubgroup.Gamma0 N,
      etaQuotient N (double r) ∣[exponentSum N r] γ = etaQuotient N (double r)) ↔
        (12 : ℤ) ∣ infinitySum N r := by
  refine ⟨fun h ↦ ?_, fun h γ hγ ↦ double_slash_Gamma0 hN r h γ hγ⟩
  have hT := h ModularGroup.T (by
    simp [CongruenceSubgroup.Gamma0_mem, ModularGroup.T])
  have hc := (slash_T_eq_self_iff N (double r) (exponentSum N r)).mp hT
  rw [infinitySum_double] at hc
  obtain ⟨t, ht⟩ := hc
  exact ⟨t, by omega⟩

end WeightTwoCusps.EtaQuotient
