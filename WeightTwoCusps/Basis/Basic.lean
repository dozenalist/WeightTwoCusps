module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Bases of cusp forms from q-expansion coefficients

Rows of `qExpansionMatrix h v c` are the coefficients of the forms `v i`
at the selected indices `c j`. A nonzero determinant proves independence;
equality of the vector length with the dimension then gives a basis.
The period and weight are arbitrary, and the empty vector is supported.
-/

@[expose] public section

noncomputable section

open UpperHalfPlane Module

namespace WeightTwoCusps

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {n : ℕ} {h : ℝ}
variable [Γ.HasDetOne]

/-- Selected q-expansion coefficients, as a complex linear map on cusp forms. -/
def cuspFormCoefficients (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (c : Fin n → ℕ) :
    CuspForm Γ k →ₗ[ℂ] (Fin n → ℂ) where
  toFun f j := (qExpansion h f).coeff (c j)
  map_add' f g := by
    ext j
    simp only [FunLike.coe_add, ModularForm.qExpansion_add hh hΓ,
      map_add, Pi.add_apply]
  map_smul' a f := by
    ext j
    simp only [FunLike.coe_smul, ModularForm.qExpansion_smul hh hΓ,
      PowerSeries.coeff_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

@[simp] theorem cuspFormCoefficients_apply (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (c : Fin n → ℕ) (f : CuspForm Γ k) (j : Fin n) :
    cuspFormCoefficients hh hΓ c f j = (qExpansion h f).coeff (c j) := rfl

/-- The rows are forms and the columns are selected q-expansion indices. -/
def qExpansionMatrix (h : ℝ) (v : Fin n → CuspForm Γ k) (c : Fin n → ℕ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j ↦ (qExpansion h (v i)).coeff (c j)

omit [Γ.HasDetOne] in
@[simp] theorem qExpansionMatrix_apply (v : Fin n → CuspForm Γ k) (c : Fin n → ℕ)
    (i j : Fin n) :
    qExpansionMatrix h v c i j = (qExpansion h (v i)).coeff (c j) := rfl

/-- Any invertible square table of q-coefficients certifies independence. -/
theorem linearIndependent_of_qExpansionMatrix_det_ne_zero
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (v : Fin n → CuspForm Γ k) (c : Fin n → ℕ)
    (hdet : (qExpansionMatrix h v c).det ≠ 0) : LinearIndependent ℂ v :=
  LinearIndependent.of_comp (cuspFormCoefficients hh hΓ c)
    (Matrix.linearIndependent_rows_of_det_ne_zero hdet)

/-- Increasing leading orders give a triangular coefficient certificate. -/
theorem linearIndependent_of_qExpansion_triangular
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (v : Fin n → CuspForm Γ k) (c : Fin n → ℕ)
    (hzero : ∀ i j, j < i → (qExpansion h (v i)).coeff (c j) = 0)
    (hdiag : ∀ i, (qExpansion h (v i)).coeff (c i) ≠ 0) :
    LinearIndependent ℂ v := by
  apply linearIndependent_of_qExpansionMatrix_det_ne_zero hh hΓ v c
  exact (Matrix.IsUpperTriangular.det_ne_zero_iff (fun _ _ hij ↦ hzero _ _ hij)).mpr hdiag

/-- Forms with strictly increasing leading q-indices are independent. -/
theorem linearIndependent_of_qExpansion_leading
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (v : Fin n → CuspForm Γ k) (c : Fin n → ℕ) (hc : StrictMono c)
    (hzero : ∀ i m, m < c i → (qExpansion h (v i)).coeff m = 0)
    (hlead : ∀ i, (qExpansion h (v i)).coeff (c i) ≠ 0) :
    LinearIndependent ℂ v :=
  linearIndependent_of_qExpansion_triangular hh hΓ v c
    (fun i j hij ↦ hzero i (c j) (hc hij)) hlead

/-- Normalized coefficient vectors also certify independence. -/
theorem linearIndependent_of_qExpansionMatrix_eq_one
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (v : Fin n → CuspForm Γ k) (c : Fin n → ℕ)
    (hcoeff : qExpansionMatrix h v c = 1) : LinearIndependent ℂ v := by
  apply linearIndependent_of_qExpansionMatrix_det_ne_zero hh hΓ v c
  rw [hcoeff, Matrix.det_one]
  exact one_ne_zero

/-- A coefficient certificate and the dimension construct a basis consisting
of exactly the supplied forms. Finite dimensionality is required also when `n = 0`. -/
def basisOfQExpansionMatrix [FiniteDimensional ℂ (CuspForm Γ k)]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (v : Fin n → CuspForm Γ k) (c : Fin n → ℕ)
    (hdim : Module.finrank ℂ (CuspForm Γ k) = n)
    (hdet : (qExpansionMatrix h v c).det ≠ 0) : Basis (Fin n) ℂ (CuspForm Γ k) :=
  basisOfLinearIndependentOfCardEqFinrank' v
    (linearIndependent_of_qExpansionMatrix_det_ne_zero hh hΓ v c hdet)
    (by simpa using hdim.symm)

@[simp] theorem basisOfQExpansionMatrix_coe [FiniteDimensional ℂ (CuspForm Γ k)]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (v : Fin n → CuspForm Γ k) (c : Fin n → ℕ) (hdim hdet) :
    ⇑(basisOfQExpansionMatrix hh hΓ v c hdim hdet) = v :=
  coe_basisOfLinearIndependentOfCardEqFinrank' ..

/-- The coefficient and dimension tests prove spanning as well as independence. -/
theorem span_eq_top_of_qExpansionMatrix_det_ne_zero
    [FiniteDimensional ℂ (CuspForm Γ k)]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (v : Fin n → CuspForm Γ k) (c : Fin n → ℕ)
    (hdim : Module.finrank ℂ (CuspForm Γ k) = n)
    (hdet : (qExpansionMatrix h v c).det ≠ 0) :
    Submodule.span ℂ (Set.range v) = ⊤ := by
  exact LinearIndependent.span_eq_top_of_card_eq_finrank'
    (linearIndependent_of_qExpansionMatrix_det_ne_zero hh hΓ v c hdet)
    (by simpa using hdim.symm)

/-- A basis certificate makes the selected coefficient map injective on the
whole cusp-form space, so these finitely many coefficients determine a form. -/
theorem cuspFormCoefficients_injective_of_det_ne_zero
    [FiniteDimensional ℂ (CuspForm Γ k)]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (v : Fin n → CuspForm Γ k) (c : Fin n → ℕ)
    (hdim : Module.finrank ℂ (CuspForm Γ k) = n)
    (hdet : (qExpansionMatrix h v c).det ≠ 0) :
    Function.Injective (cuspFormCoefficients (k := k) hh hΓ c) := by
  have hspan := LinearIndependent.span_eq_top_of_card_eq_finrank'
    (Matrix.linearIndependent_rows_of_det_ne_zero hdet) (by simp)
  have hsurj : Function.Surjective (cuspFormCoefficients (k := k) hh hΓ c) := by
    apply LinearMap.range_eq_top.mp
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨v i, rfl⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simpa using hdim)).mpr hsurj

/-- Comparing the selected coefficients suffices to compare arbitrary cusp
forms once a coefficient basis certificate has been established. -/
theorem eq_iff_qExpansion_coeff_eq_of_det_ne_zero
    [FiniteDimensional ℂ (CuspForm Γ k)]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (v : Fin n → CuspForm Γ k) (c : Fin n → ℕ)
    (hdim : Module.finrank ℂ (CuspForm Γ k) = n)
    (hdet : (qExpansionMatrix h v c).det ≠ 0) (f g : CuspForm Γ k) :
    f = g ↔ ∀ j, (qExpansion h f).coeff (c j) = (qExpansion h g).coeff (c j) := by
  constructor
  · rintro rfl j
    rfl
  · intro hcoeff
    apply cuspFormCoefficients_injective_of_det_ne_zero hh hΓ v c hdim hdet
    exact funext hcoeff

end WeightTwoCusps
