module

public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

/-! # Positive dilations of the upper half-plane -/

@[expose] public section

noncomputable section

open Complex UpperHalfPlane Filter

namespace WeightTwoCusps.Eta

/-- Positive dilation on the upper half-plane. -/
def dilate (r : ℝ) (hr : 0 < r) (z : ℍ) : ℍ :=
  ⟨(r : ℂ) * (z : ℂ), by simpa using mul_pos hr z.im_pos⟩

@[simp] theorem coe_dilate (r : ℝ) (hr : 0 < r) (z : ℍ) :
    (dilate r hr z : ℂ) = (r : ℂ) * (z : ℂ) := rfl

/-- Every positive dilation preserves the filter at infinity. -/
theorem tendsto_dilate_atImInfty (r : ℝ) (hr : 0 < r) :
    Tendsto (dilate r hr) atImInfty atImInfty := by
  change Tendsto _ atImInfty (Filter.comap UpperHalfPlane.im Filter.atTop)
  rw [Filter.tendsto_comap_iff]
  simpa [dilate, Function.comp_def] using
    (Filter.tendsto_comap.const_mul_atTop hr :
      Tendsto (fun z : ℍ ↦ r * z.im) atImInfty Filter.atTop)

end WeightTwoCusps.Eta
