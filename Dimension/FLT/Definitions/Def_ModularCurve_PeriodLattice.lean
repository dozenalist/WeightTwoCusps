/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache 2.0 license.
Copied from anthropics/fermats-last-theorem, revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_ModularCurve_PeriodLattice.lean.
Adapted for this project: local imports, modules, unused code, and shared proofs.
See Dimension/FLT/LICENSE, NOTICE, and ATTRIBUTION_UPSTREAM.md.
-/
module

public import Dimension.FLT.AnalysisImports

@[expose] public section

set_option autoImplicit false

noncomputable section

open UpperHalfPlane

open scoped MatrixGroups

namespace ModularCurve

section Period

def clamp01 (t : ℝ) : ℝ := max 0 (min t 1)

theorem clamp01_nonneg (t : ℝ) : 0 ≤ clamp01 t := le_max_left _ _

theorem clamp01_le_one (t : ℝ) : clamp01 t ≤ 1 := max_le zero_le_one (min_le_right _ _)

theorem continuous_clamp01 : Continuous clamp01 :=
  continuous_const.max (continuous_id.min continuous_const)

theorem clamp01_of_mem {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : clamp01 t = t := by
  rw [clamp01, min_eq_left ht.2, max_eq_right ht.1]

def segmentPoint (τ₀ τ₁ : ℍ) (t : ℝ) : ℂ :=
  (1 - clamp01 t) • (τ₀ : ℂ) + clamp01 t • (τ₁ : ℂ)

theorem segmentPoint_im_pos (τ₀ τ₁ : ℍ) (t : ℝ) : 0 < (segmentPoint τ₀ τ₁ t).im := by
  have h0 := clamp01_nonneg t
  have h1 := clamp01_le_one t
  simp only [segmentPoint, Complex.add_im, Complex.smul_im, smul_eq_mul]
  rcases eq_or_lt_of_le h1 with h | h
  · rw [h]; simpa using τ₁.im_pos
  · exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) τ₀.im_pos)
      (mul_nonneg h0 τ₁.im_pos.le)

theorem continuous_segmentPoint (τ₀ τ₁ : ℍ) : Continuous (segmentPoint τ₀ τ₁) :=
  ((continuous_const.sub continuous_clamp01).smul continuous_const).add
    (continuous_clamp01.smul continuous_const)

def segmentPath (τ₀ τ₁ : ℍ) (t : ℝ) : ℍ :=
  UpperHalfPlane.mk (segmentPoint τ₀ τ₁ t) (segmentPoint_im_pos τ₀ τ₁ t)

@[simp] theorem coe_segmentPath (τ₀ τ₁ : ℍ) (t : ℝ) :
    ((segmentPath τ₀ τ₁ t : ℍ) : ℂ) = segmentPoint τ₀ τ₁ t := rfl

theorem continuous_segmentPath (τ₀ τ₁ : ℍ) : Continuous (segmentPath τ₀ τ₁) :=
  (continuous_segmentPoint τ₀ τ₁).upperHalfPlaneMk _

end Period

end ModularCurve

end
