module

public import WeightTwoCusps.Basis.Basic

/-! # Normalization by a q-coefficient in a one-dimensional cusp-form space -/

@[expose] public section

noncomputable section

open UpperHalfPlane

namespace WeightTwoCusps

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] {k : ℤ} {h : ℝ}
variable [FiniteDimensional ℂ (CuspForm Γ k)]

/-- In dimension one, a nonzero coefficient of one form determines every form. -/
theorem eq_of_qExpansion_coeff_eq_of_finrank_eq_one
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (hdim : Module.finrank ℂ (CuspForm Γ k) = 1)
    (f : CuspForm Γ k) (n : ℕ) (hf : (qExpansion h f).coeff n ≠ 0)
    (g : CuspForm Γ k) (hg : (qExpansion h g).coeff n = (qExpansion h f).coeff n) :
    g = f := by
  apply (eq_iff_qExpansion_coeff_eq_of_det_ne_zero hh hΓ ![f] ![n] hdim
    (by simpa [qExpansionMatrix, Matrix.det_fin_one] using hf) g f).mpr
  intro j
  have hj : j = 0 := Subsingleton.elim _ _
  simpa [hj] using hg

/-- A normalized form in a one-dimensional space is the unique normalized form.
This applies at any weight and positive strict period. -/
theorem existsUnique_normalized_of_finrank_eq_one
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (hdim : Module.finrank ℂ (CuspForm Γ k) = 1)
    (f : CuspForm Γ k) (n : ℕ) (hf : (qExpansion h f).coeff n = 1) :
    ∃! g : CuspForm Γ k, (qExpansion h g).coeff n = 1 := by
  refine ⟨f, hf, fun g hg ↦ ?_⟩
  exact eq_of_qExpansion_coeff_eq_of_finrank_eq_one hh hΓ hdim f n
    (by rw [hf]; exact one_ne_zero) g (hg.trans hf.symm)

end WeightTwoCusps
