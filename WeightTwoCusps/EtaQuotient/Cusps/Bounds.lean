/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license.

The rational-cusp transport proof below is adapted from
TauCeti/NumberTheory/ModularForms/Cusps/Rat/Basic.lean at
e8758b7b2f82b9b1c3f33b992ab8f499b510240f. The remaining proofs are local.
-/
module

public import WeightTwoCusps.EtaQuotient.Basic

/-!
# Cusp bounds for eta products

The modular discriminant transports through rational dilations and vanishes
at every rational cusp. Taking a twelfth root proves the corresponding
analytic fact for eta squared, without asserting that eta squared itself
has trivial character. Nonnegative products then give boundedness at all
cusps at arbitrary positive levels.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Complex Filter OnePoint
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm Topology Pointwise

namespace WeightTwoCusps.EtaQuotient

private theorem cusp_smul_rat {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ)
    (g : GL (Fin 2) ℚ) : IsCusp (g.map (Rat.castHom ℝ) • c) 𝒮ℒ := by
  have : (ConjAct.toConjAct (g.map (Rat.castHom ℝ)) • 𝒮ℒ).IsArithmetic :=
    Subgroup.IsArithmetic.conj 𝒮ℒ g
  exact (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp (hc.smul _)

/-- The rational matrix for positive integral dilation. -/
def dilationRat (m : ℕ) (hm : 0 < m) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(m : ℚ), 0; 0, 1] (by
    simpa [Matrix.det_fin_two] using (show (m : ℚ) ≠ 0 by exact_mod_cast hm.ne'))

private def dilationGL (m : ℕ) (hm : 0 < m) : GL (Fin 2) ℝ :=
  (dilationRat m hm).map (Rat.castHom ℝ)

private theorem dilationGL_coe (m : ℕ) (hm : 0 < m) :
    (dilationGL m hm : Matrix (Fin 2) (Fin 2) ℝ) = !![(m : ℝ), 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dilationGL, dilationRat]

private theorem dilationGL_det (m : ℕ) (hm : 0 < m) :
    (dilationGL m hm).det.val = m := by
  change Matrix.det (dilationGL m hm : Matrix (Fin 2) (Fin 2) ℝ) = m
  rw [dilationGL_coe]
  simp [Matrix.det_fin_two]

private theorem dilationGL_smul (m : ℕ) (hm : 0 < m) (z : ℍ) :
    ((dilationGL m hm • z : ℍ) : ℂ) = (m : ℂ) * (z : ℂ) := by
  rw [coe_smul_of_det_pos (by rw [dilationGL_det]; exact_mod_cast hm)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, dilationGL_coe]

private theorem discriminant_dilate_eq_slash (m : ℕ) (hm : 0 < m) :
    (fun z : ℍ ↦ ModularForm.discriminant ((Eta.dilate m (by exact_mod_cast hm) z))) =
      ((m : ℂ) ^ (11 : ℤ))⁻¹ • (ModularForm.discriminant ∣[(12 : ℤ)] dilationGL m hm) := by
  ext z
  have hpos : 0 < (dilationGL m hm).det.val := by rw [dilationGL_det]; exact_mod_cast hm
  have hd : denom (dilationGL m hm) z = 1 := by
    simp [UpperHalfPlane.denom, dilationGL_coe]
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [Pi.smul_apply, smul_eq_mul, ModularForm.slash_apply, UpperHalfPlane.σ,
    dilationGL_det, (show (0 : ℝ) < m by exact_mod_cast hm), ↓reduceIte,
    ContinuousAlgEquiv.refl_apply, abs_of_pos (show (0 : ℝ) < m by exact_mod_cast hm),
    Int.reduceSub, hd, one_zpow, mul_one]
  have he : dilationGL m hm • z = Eta.dilate m (by exact_mod_cast hm) z := by
    apply UpperHalfPlane.ext
    simpa using dilationGL_smul m hm z
  rw [he]
  simp only [Complex.ofReal_natCast]
  field_simp [hm0]

private theorem discriminant_dilate_zero {m : ℕ} (hm : 0 < m) (γ : SL(2, ℤ)) :
    IsZeroAtImInfty ((fun z : ℍ ↦ ModularForm.discriminant
      (Eta.dilate m (by exact_mod_cast hm) z)) ∣[(12 : ℤ)] γ) := by
  let g := dilationGL m hm
  have hc : IsCusp (Matrix.SpecialLinearGroup.mapGL ℝ γ • (∞ : OnePoint ℝ)) 𝒮ℒ := by
    rw [isCusp_SL2Z_iff']
    exact ⟨γ, rfl⟩
  have hz := CuspForm.discriminant.zero_at_cusps' (cusp_smul_rat hc (dilationRat m hm))
  have hs : (Matrix.SpecialLinearGroup.mapGL ℝ γ • (∞ : OnePoint ℝ)).IsZeroAt
      (ModularForm.discriminant ∣[(12 : ℤ)] g) 12 := by
    apply OnePoint.IsZeroAt.smul_iff.mp
    exact hz
  have hi : IsZeroAtImInfty ((ModularForm.discriminant ∣[(12 : ℤ)] g) ∣[(12 : ℤ)] γ) := by
    exact (OnePoint.isZeroAt_iff (g := Matrix.SpecialLinearGroup.mapGL ℝ γ) rfl).mp hs
  rw [discriminant_dilate_eq_slash m hm, ModularForm.SL_smul_slash]
  exact hi.smul _

/-- Every integral dilation of eta squared, slashed in weight one, tends to
zero at every rational cusp. This is an analytic statement, independent of its character. -/
theorem etaSq_dilate_slash_isZero {m : ℕ} (hm : 0 < m) (γ : SL(2, ℤ)) :
    IsZeroAtImInfty ((fun z : ℍ ↦ ModularForm.eta ((m : ℂ) * (z : ℂ)) ^ 2) ∣[(1 : ℤ)] γ) := by
  let f : ℍ → ℂ := (fun z : ℍ ↦ ModularForm.eta ((m : ℂ) * (z : ℂ)) ^ 2) ∣[(1 : ℤ)] γ
  have heq : (f ^ 12) = (fun z : ℍ ↦ ModularForm.discriminant
      (Eta.dilate m (by exact_mod_cast hm) z)) ∣[(12 : ℤ)] γ := by
    ext z
    simp only [f, Pi.pow_apply, ModularForm.SL_slash_apply, mul_pow, ← pow_mul,
      ModularForm.discriminant, Eta.coe_dilate, Complex.ofReal_natCast]
    congr 1
    simp [Int.reduceNeg, zpow_neg, zpow_ofNat, inv_pow]
  have hz := discriminant_dilate_zero hm γ
  change Tendsto f atImInfty (𝓝 0)
  rw [← Asymptotics.isLittleO_one_iff (F := ℝ)]
  change f =o[atImInfty] (1 : ℍ → ℝ)
  apply Asymptotics.IsLittleO.of_pow (n := 12) ?_ (by norm_num)
  rw [heq, one_pow]
  exact (Asymptotics.isLittleO_one_iff (F := ℝ)).mpr hz

end WeightTwoCusps.EtaQuotient
