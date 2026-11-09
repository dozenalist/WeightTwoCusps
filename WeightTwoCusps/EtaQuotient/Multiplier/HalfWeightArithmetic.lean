module

public import WeightTwoCusps.EtaQuotient.Multiplier.HalfWeight
public import WeightTwoCusps.EtaQuotient.Transformation.GammaZeroFour
public import WeightTwoCusps.EtaQuotient.Multiplier.JacobiSymbol
public import WeightTwoCusps.EtaQuotient.Multiplier.MultiplierExponent

/-!
# The arithmetic candidate for the eta multiplier

The signed Jacobi symbol and the polynomial exponential define a computable
arithmetic candidate. The comparison theorem isolates precisely what remains
to identify it with the analytic multiplier: the cocycle law and the values
on the generators of `Γ₀(4)`. No transformation law is assumed for this
candidate.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Complex UpperHalfPlane
open scoped MatrixGroups

namespace WeightTwoCusps.EtaQuotient

/-- The right side of Savitt's half-weight multiplier formula. -/
def arithmeticHalfMultiplier (γ : SL(2, ℤ)) : ℂ :=
  (extendedJacobi (γ 1 0) (γ 1 1) : ℂ) *
    translationCharacter (matrixMultiplierExponent γ)

@[simp] theorem arithmeticHalfMultiplier_one : arithmeticHalfMultiplier 1 = 1 := by
  norm_num [arithmeticHalfMultiplier, matrixMultiplierExponent, arithmeticMultiplierExponent]

theorem arithmeticHalfMultiplier_T :
    arithmeticHalfMultiplier ModularGroup.T = translationCharacter 1 := by
  norm_num [arithmeticHalfMultiplier, matrixMultiplierExponent,
    arithmeticMultiplierExponent, ModularGroup.T]

theorem arithmeticHalfMultiplier_lowerTranslation_four :
    arithmeticHalfMultiplier (lowerTranslation 4) = translationCharacter (-4) := by
  norm_num [arithmeticHalfMultiplier, matrixMultiplierExponent,
    arithmeticMultiplierExponent, lowerTranslation]

theorem arithmeticHalfMultiplier_neg_one :
    arithmeticHalfMultiplier (-1 : SL(2, ℤ)) = translationCharacter (-6) := by
  norm_num [arithmeticHalfMultiplier, matrixMultiplierExponent, arithmeticMultiplierExponent]

theorem arithmeticHalfMultiplier_ne_zero (γ : SL(2, ℤ)) :
    arithmeticHalfMultiplier γ ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast extendedJacobi.ne_zero
      (Int.isCoprime_iff_gcd_eq_one.mp (Matrix.SpecialLinearGroup.isCoprime_row γ 1))
  · exact (ZMod.toCircle _).coe_ne_zero

/-- The arithmetic candidate has the correct recurrence at the translation
generator. The Jacobi factor is unchanged because the bottom row is unchanged. -/
theorem arithmeticHalfMultiplier_T_mul (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 4) :
    arithmeticHalfMultiplier (ModularGroup.T * γ) =
      arithmeticHalfMultiplier γ * translationCharacter 1 := by
  unfold arithmeticHalfMultiplier
  rw [matrixMultiplierCharacter_T γ hγ]
  have hc : (ModularGroup.T * γ) 1 0 = γ 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.T, Matrix.mul_apply,
      Fin.sum_univ_two]
  have hd : (ModularGroup.T * γ) 1 1 = γ 1 1 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.T, Matrix.mul_apply,
      Fin.sum_univ_two]
  rw [hc, hd, mul_assoc]

/-- Equality on the three generators and the half-weight cocycle law suffice
to identify an arithmetic formula on all of `Γ₀(4)`. This is a reduction
lemma; it supplies no missing arithmetic cocycle identity. -/
theorem eq_halfMultiplier_of_cocycle (e : SL(2, ℤ) → ℂ)
    (h1 : e 1 = 1)
    (hmul : ∀ γ δ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 4 →
      δ ∈ CongruenceSubgroup.Gamma0 4 →
      e (γ * δ) = e γ * e δ * halfCocycle γ δ)
    (hT : e ModularGroup.T = halfMultiplier ModularGroup.T)
    (hL : e (lowerTranslation 4) = halfMultiplier (lowerTranslation 4))
    (hneg : e (-1 : SL(2, ℤ)) = halfMultiplier (-1 : SL(2, ℤ)))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 4) :
    e γ = halfMultiplier γ := by
  let H : Subgroup SL(2, ℤ) := {
    carrier := {δ | δ ∈ CongruenceSubgroup.Gamma0 4 ∧ e δ = halfMultiplier δ}
    one_mem' := ⟨(CongruenceSubgroup.Gamma0 4).one_mem, by simpa using h1⟩
    mul_mem' := by
      rintro δ ε ⟨hδ, heδ⟩ ⟨hε, heε⟩
      exact ⟨(CongruenceSubgroup.Gamma0 4).mul_mem hδ hε, by
        rw [hmul δ ε hδ hε, heδ, heε, halfMultiplier_mul]⟩
    inv_mem' := by
      rintro δ ⟨hδ, heδ⟩
      refine ⟨(CongruenceSubgroup.Gamma0 4).inv_mem hδ, ?_⟩
      have he := hmul δ δ⁻¹ hδ ((CongruenceSubgroup.Gamma0 4).inv_mem hδ)
      have ha := halfMultiplier_mul δ δ⁻¹
      rw [mul_inv_cancel, h1, heδ] at he
      rw [mul_inv_cancel, halfMultiplier_one] at ha
      have hc : halfCocycle δ δ⁻¹ ≠ 0 := by
        intro hz
        have hs := halfCocycle_sq δ δ⁻¹
        simp [hz] at hs
      exact mul_left_cancel₀ (halfMultiplier_ne_zero δ)
        (mul_right_cancel₀ hc (he.symm.trans ha)) }
  apply (Gamma0_four_le_of_generators (H := H) ?_ ?_ ?_ hγ).2
  · exact ⟨by norm_num [CongruenceSubgroup.Gamma0_mem, ModularGroup.T], hT⟩
  · refine ⟨?_, hL⟩
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr
    change (4 : ℤ) ∣ 4
    exact dvd_refl _
  · exact ⟨by norm_num [CongruenceSubgroup.Gamma0_mem], hneg⟩

end WeightTwoCusps.EtaQuotient
