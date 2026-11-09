module

public import WeightTwoCusps.EtaQuotient.Transformation.Generation
public import WeightTwoCusps.Eta.Congruence

/-!
# The arithmetic exponent in the half-weight multiplier

This file proves the polynomial congruences used in Savitt's proof of the
eta multiplier formula on `Γ₀(4)` (Lemma 4.8 and Proposition 4.12). They do
not assume the still-unproved Jacobi-symbol formula for the multiplier.

Reference: D. Savitt, *An elementary proof of Newman's eta-quotient theorem*,
§4, <https://math.jhu.edu/~savitt/papers/pdfs/newman.pdf>.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open scoped MatrixGroups

namespace WeightTwoCusps.EtaQuotient

/-- The polynomial exponent in Savitt's arithmetic eta-multiplier formula.
Its value is read modulo 24 in the exponential. -/
def arithmeticMultiplierExponent {R : Type*} [Ring R] (a b c d : R) : R :=
  a * c * (1 - d ^ 2) + d * (b - c + 3) - 3

/-- The arithmetic exponent attached to an integral modular matrix. -/
def matrixMultiplierExponent (γ : SL(2, ℤ)) : ℤ :=
  arithmeticMultiplierExponent (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)

theorem arithmeticMultiplierExponent_neg (a b c d : ℤ) :
    arithmeticMultiplierExponent (-a) (-b) (-c) (-d) =
      arithmeticMultiplierExponent a b c d - 6 * d := by
  simp only [arithmeticMultiplierExponent]
  ring

theorem arithmeticMultiplierExponent_translation (a b c d : ℤ) :
    arithmeticMultiplierExponent (a + c) (b + d) c d -
      arithmeticMultiplierExponent a b c d = c ^ 2 * (1 - d ^ 2) + d ^ 2 := by
  simp only [arithmeticMultiplierExponent]
  ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- These checks use only 8⁴ and 3⁴ residue tuples, and are kernel reductions.
private theorem translation_residue_eight : ∀ a b t d : ZMod 8,
    a * d - b * (2 * t) = 1 →
      arithmeticMultiplierExponent (a + 2 * t) (b + d) (2 * t) d =
        arithmeticMultiplierExponent a b (2 * t) d + 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks all determinant-one residue matrices modulo three.
private theorem translation_residue_three : ∀ a b c d : ZMod 3,
    a * d - b * c = 1 →
      arithmeticMultiplierExponent (a + c) (b + d) c d =
        arithmeticMultiplierExponent a b c d + 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the lower-translation identity on 8⁴ residue tuples.
private theorem lower_translation_residue_eight : ∀ a b t d : ZMod 8,
    a * d - b * (2 * t) = 1 →
      arithmeticMultiplierExponent a b (2 * t + 4 * a) (d + 4 * b) =
        arithmeticMultiplierExponent a b (2 * t) d - 4 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the lower-translation identity on 3⁴ residue tuples.
private theorem lower_translation_residue_three : ∀ a b c d : ZMod 3,
    a * d - b * c = 1 →
      arithmeticMultiplierExponent a b (c + 4 * a) (d + 4 * b) =
        arithmeticMultiplierExponent a b c d - 4 := by
  decide +kernel

private theorem modeq_twentyFour_of_eight_three {a b : ℤ}
    (h8 : a ≡ b [ZMOD 8]) (h3 : a ≡ b [ZMOD 3]) : a ≡ b [ZMOD 24] := by
  apply Int.modEq_iff_dvd.mpr
  have hc : IsCoprime (8 : ℤ) 3 := ⟨-1, 3, by norm_num⟩
  exact hc.mul_dvd h8.dvd h3.dvd

/-- Left translation increases the arithmetic exponent by one modulo 24.
The weaker assumption that `c` is even already suffices. -/
theorem arithmeticMultiplierExponent_translation_modEq (a b c d : ℤ)
    (hdet : a * d - b * c = 1) (hc : Even c) :
    arithmeticMultiplierExponent (a + c) (b + d) c d ≡
      arithmeticMultiplierExponent a b c d + 1 [ZMOD 24] := by
  obtain ⟨t, rfl⟩ := hc
  apply modeq_twentyFour_of_eight_three
  · apply (ZMod.intCast_eq_intCast_iff _ _ 8).mp
    have hd : (a : ZMod 8) * d - b * ((t : ZMod 8) + t) = 1 := by
      simpa only [Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_one] using
        congrArg (Int.cast : ℤ → ZMod 8) hdet
    simpa [arithmeticMultiplierExponent, two_mul] using
      translation_residue_eight a b t d (by simpa [two_mul] using hd)
  · apply (ZMod.intCast_eq_intCast_iff _ _ 3).mp
    have hd : (a : ZMod 3) * d - b * ((t : ZMod 3) + t) = 1 := by
      simpa only [Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_one] using
        congrArg (Int.cast : ℤ → ZMod 3) hdet
    simpa [arithmeticMultiplierExponent] using
      translation_residue_three a b ((t : ZMod 3) + t) d hd

/-- Left multiplication by `[1,0;4,1]` decreases the arithmetic exponent
by four modulo 24. No sign or positivity hypothesis is needed here. -/
theorem arithmeticMultiplierExponent_lower_translation_modEq (a b c d : ℤ)
    (hdet : a * d - b * c = 1) (hc : Even c) :
    arithmeticMultiplierExponent a b (c + 4 * a) (d + 4 * b) ≡
      arithmeticMultiplierExponent a b c d - 4 [ZMOD 24] := by
  obtain ⟨t, rfl⟩ := hc
  apply modeq_twentyFour_of_eight_three
  · apply (ZMod.intCast_eq_intCast_iff _ _ 8).mp
    have hd : (a : ZMod 8) * d - b * ((t : ZMod 8) + t) = 1 := by
      simpa only [Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_one] using
        congrArg (Int.cast : ℤ → ZMod 8) hdet
    simpa [arithmeticMultiplierExponent, two_mul] using
      lower_translation_residue_eight a b t d (by simpa [two_mul] using hd)
  · apply (ZMod.intCast_eq_intCast_iff _ _ 3).mp
    have hd : (a : ZMod 3) * d - b * ((t : ZMod 3) + t) = 1 := by
      simpa only [Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_one] using
        congrArg (Int.cast : ℤ → ZMod 3) hdet
    simpa [arithmeticMultiplierExponent] using
      lower_translation_residue_three a b ((t : ZMod 3) + t) d hd

/-- On the subgroup of matrices whose off-diagonal entries are multiples
of 24, the exponent reduces to `3(d - 1)`. -/
theorem arithmeticMultiplierExponent_restricted_modEq (a b c d : ℤ)
    (hb : (24 : ℤ) ∣ b) (hc : (24 : ℤ) ∣ c) :
    arithmeticMultiplierExponent a b c d ≡ 3 * (d - 1) [ZMOD 24] := by
  apply (ZMod.intCast_eq_intCast_iff _ _ 24).mp
  have hb' := (ZMod.intCast_zmod_eq_zero_iff_dvd b 24).mpr hb
  have hc' := (ZMod.intCast_zmod_eq_zero_iff_dvd c 24).mpr hc
  simp only [arithmeticMultiplierExponent, Int.cast_sub, Int.cast_add,
    Int.cast_mul, Int.cast_pow, Int.cast_one, Int.cast_ofNat, hb', hc']
  ring

private theorem even_lower_left_of_mem_Gamma0_four (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 4) : Even (γ 1 0) := by
  apply even_iff_two_dvd.mpr
  exact dvd_trans (by norm_num : (2 : ℤ) ∣ 4) (Eta.level_dvd_lower_left 4 γ hγ)

/-- The exponent recurrence under the first generator of `Γ₀(4)`. -/
theorem matrixMultiplierExponent_T (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 4) :
    matrixMultiplierExponent (ModularGroup.T * γ) ≡
      matrixMultiplierExponent γ + 1 [ZMOD 24] := by
  have hd : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using γ.det_coe
  simpa [matrixMultiplierExponent, Matrix.SpecialLinearGroup.coe_mul,
    ModularGroup.T, Matrix.mul_apply, Fin.sum_univ_two] using
    arithmeticMultiplierExponent_translation_modEq _ _ _ _ hd
      (even_lower_left_of_mem_Gamma0_four γ hγ)

/-- The exponent recurrence under the lower-translation generator of `Γ₀(4)`. -/
theorem matrixMultiplierExponent_lowerTranslation_four (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 4) :
    matrixMultiplierExponent (lowerTranslation 4 * γ) ≡
      matrixMultiplierExponent γ - 4 [ZMOD 24] := by
  have hd : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using γ.det_coe
  simpa [matrixMultiplierExponent, Matrix.SpecialLinearGroup.coe_mul,
    lowerTranslation, Matrix.mul_apply, Fin.sum_univ_two, add_comm] using
    arithmeticMultiplierExponent_lower_translation_modEq _ _ _ _ hd
      (even_lower_left_of_mem_Gamma0_four γ hγ)

/-- Integer congruence modulo 24 is exactly equality of the eta translation
characters. -/
theorem translationCharacter_intCast_eq_iff (a b : ℤ) :
    translationCharacter (a : ZMod 24) = translationCharacter (b : ZMod 24) ↔
      a ≡ b [ZMOD 24] := by
  change ZMod.stdAddChar (a : ZMod 24) = ZMod.stdAddChar (b : ZMod 24) ↔ _
  rw [ZMod.injective_stdAddChar.eq_iff]
  exact ZMod.intCast_eq_intCast_iff a b 24

/-- The exponential factor has the required recurrence under `T`. -/
theorem matrixMultiplierCharacter_T (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 4) :
    translationCharacter (matrixMultiplierExponent (ModularGroup.T * γ)) =
      translationCharacter (matrixMultiplierExponent γ) * translationCharacter 1 := by
  have h := (translationCharacter_intCast_eq_iff _ _).mpr
    (matrixMultiplierExponent_T γ hγ)
  simpa only [Int.cast_add, Int.cast_one, AddChar.map_add_eq_mul] using h

/-- The exponential factor has the required recurrence under `[1,0;4,1]`. -/
theorem matrixMultiplierCharacter_lowerTranslation_four (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 4) :
    translationCharacter (matrixMultiplierExponent (lowerTranslation 4 * γ)) =
      translationCharacter (matrixMultiplierExponent γ) * translationCharacter (-4) := by
  have h := (translationCharacter_intCast_eq_iff _ _).mpr
    (matrixMultiplierExponent_lowerTranslation_four γ hγ)
  simpa only [sub_eq_add_neg, Int.cast_add, Int.cast_neg, Int.cast_ofNat,
    AddChar.map_add_eq_mul] using h

end WeightTwoCusps.EtaQuotient
