module

public import WeightTwoCusps.Tactic.Basis

/-! # Automatic basis constructors for cusp forms and eta quotients -/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open EtaQuotient Module

/-- Turn a vector of cusp forms into a basis by comparing selected q-coefficients
and the dimension. Omitted proofs use the corresponding specialized tactics. The default
columns are coefficients 1 through `n`; custom indices and symbolic proofs
can be supplied explicitly. Numerical determinant proofs materialize a compact
coefficient table and use `det_ne_zero!`, with project-local persistent witnesses. -/
def cuspFormBasis {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] {k : ℤ} {n : ℕ}
    [FiniteDimensional ℂ (CuspForm Γ k)] (v : Fin n → CuspForm Γ k)
    (c : Fin n → ℕ := fun i ↦ i.val + 1) (h : ℝ := 1)
    (hh : 0 < h := by positivity) (hΓ : h ∈ Γ.strictPeriods := by cusp_basis_period)
    (hdim : Module.finrank ℂ (CuspForm Γ k) = n := by cusp_basis_dimension)
    (hdet : (qExpansionMatrix h v c).det ≠ 0 := by
      first | assumption | (q_expansion_matrix; det_ne_zero! cusp_basis_det_config%)) :
    Basis (Fin n) ℂ (CuspForm Γ k) :=
  basisOfQExpansionMatrix hh hΓ v c hdim hdet

@[simp] theorem cuspFormBasis_coe {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]
    {k : ℤ} {n : ℕ} [FiniteDimensional ℂ (CuspForm Γ k)]
    (v : Fin n → CuspForm Γ k) (c h hh hΓ hdim hdet) :
    ⇑(cuspFormBasis v c h hh hΓ hdim hdet) = v :=
  basisOfQExpansionMatrix_coe ..

@[simp] theorem cuspFormBasis_apply {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]
    {k : ℤ} {n : ℕ} [FiniteDimensional ℂ (CuspForm Γ k)]
    (v : Fin n → CuspForm Γ k) (c h hh hΓ hdim hdet i) :
    ⇑(cuspFormBasis v c h hh hΓ hdim hdet) i = v i :=
  congrFun (cuspFormBasis_coe ..) i

/-- Construct a weight-two `Γ₀(N)` basis from a vector of eta-quotient exponent
vectors. The modularity and cusp conditions default to `decide +kernel`;
the dimension defaults to `cusp_basis_dimension`. The coefficient table is
materialized with `q_expansion_matrix` and certified by `det_ne_zero!`.
Entry `i` of the resulting basis is exactly `etaQuotientCuspForm N (r i)`.
For a vector of already bundled eta quotients, use `cuspFormBasis` directly. -/
def etaQuotientBasis (N : ℕ) [NeZero N] {n : ℕ} (r : Fin n → Fin N → ℤ)
    (h : ∀ i, NewmanLigozatConditions N (r i) 2 := by decide +kernel)
    (hc : ∀ i, VanishingAtCusps N (r i) := by decide +kernel)
    (c : Fin n → ℕ := fun i ↦ i.val + 1)
    (hdim : Module.finrank ℂ (gamma0CuspForms N) = n := by cusp_basis_dimension)
    (hdet : (qExpansionMatrix 1 (fun i ↦ etaQuotientCuspForm N (r i) (h i) (hc i)) c).det ≠ 0 :=
      by first | assumption | (q_expansion_matrix; det_ne_zero! cusp_basis_det_config%)) :
    Basis (Fin n) ℂ (gamma0CuspForms N) :=
  cuspFormBasis (fun i ↦ etaQuotientCuspForm N (r i) (h i) (hc i)) c 1
    one_pos (by simp) hdim hdet

@[simp] theorem etaQuotientBasis_apply (N : ℕ) [NeZero N] {n : ℕ}
    (r : Fin n → Fin N → ℤ) (h hc c hdim hdet) (i : Fin n) :
    etaQuotientBasis N r h hc c hdim hdet i = etaQuotientCuspForm N (r i) (h i) (hc i) := by
  simp [etaQuotientBasis]

end WeightTwoCusps
