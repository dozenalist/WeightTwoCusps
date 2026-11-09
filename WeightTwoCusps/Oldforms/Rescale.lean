module

public import Dimension.Gamma_0.Basic
public import WeightTwoCusps.Eta.Congruence

/-!
# Rescaling weight-two cusp forms

`gamma0Rescale f d hd` is the cusp form `z ↦ f (d * z)` at level `M * d`,
where `f` has level `M` and `hd : 0 < d`. `gamma0RescaleToLevel` places the
same function at any level divisible by `M * d`.

The constructors use Mathlib's translation and restriction operations. The
normalization removes the factor `d` in Mathlib's weight-two slash action.
-/

@[expose] public section

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups Pointwise ModularForm

namespace WeightTwoCusps

/-- Divisibility of levels reverses inclusion of the `Γ₀` subgroups. -/
theorem gamma0_le_of_dvd {M N : ℕ} (h : M ∣ N) :
    CongruenceSubgroup.Gamma0 N ≤ CongruenceSubgroup.Gamma0 M := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact dvd_trans (Int.natCast_dvd_natCast.mpr h) (Eta.level_dvd_lower_left N γ hγ)

/-- Regard a weight-two cusp form at level `M` as a form at a multiple `N`,
without changing its underlying function. This is the dilation-one oldform. -/
def gamma0Restrict {M N : ℕ} (f : gamma0CuspForms M) (h : M ∣ N) :
    gamma0CuspForms N :=
  weightTwoCuspForms_restrict (gamma0_le_of_dvd h) f

@[simp] theorem gamma0Restrict_apply {M N : ℕ} (f : gamma0CuspForms M)
    (h : M ∣ N) (z : ℍ) : gamma0Restrict f h z = f z := rfl

@[simp] theorem gamma0Restrict_self {M : ℕ} (f : gamma0CuspForms M) :
    gamma0Restrict f dvd_rfl = f := by
  ext z
  rfl

namespace Oldforms

/-- The positive diagonal matrix inducing the dilation `z ↦ d * z`. -/
def rescaleMatrix (d : ℕ) (hd : 0 < d) : GL (Fin 2) ℝ :=
  .mkOfDetNeZero !![(d : ℝ), 0; 0, 1] (by simp [Nat.ne_of_gt hd])

/-- The determinant of the dilation matrix. -/
theorem rescaleMatrix_det (d : ℕ) (hd : 0 < d) :
    (rescaleMatrix d hd).det.val = d := by
  simp [rescaleMatrix, Matrix.GeneralLinearGroup.val_det_apply]

/-- The matrix action is positive dilation on the upper half-plane. -/
theorem rescaleMatrix_smul (d : ℕ) (hd : 0 < d) (z : ℍ) :
    rescaleMatrix d hd • z = Eta.dilate d (by exact_mod_cast hd) z := by
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (by
    rw [rescaleMatrix_det]
    exact_mod_cast hd)]
  simp [num, denom, rescaleMatrix, Eta.coe_dilate]

/-- The dilation matrix intertwines integral matrices with their level conjugates. -/
theorem rescaleMatrix_mul (d : ℕ) (hd : 0 < d) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 d) :
    rescaleMatrix d hd * (γ : GL (Fin 2) ℝ) =
      (Eta.levelConjugate d γ hγ : GL (Fin 2) ℝ) * rescaleMatrix d hd := by
  have hcancel : (γ 1 0 : ℝ) = (d : ℝ) * ((γ 1 0 / (d : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast (show γ 1 0 = (d : ℤ) * (γ 1 0 / (d : ℤ)) by
      simpa [mul_comm] using (Eta.lower_left_div_mul d γ hγ).symm)
  apply Units.ext
  change !![(d : ℝ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ) =
    (!![γ 0 0, (d : ℤ) * γ 0 1; γ 1 0 / (d : ℤ), γ 1 1] : Matrix (Fin 2) (Fin 2) ℤ).map
      (Int.castRingHom ℝ) * !![(d : ℝ), 0; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm, hcancel]

/-- Divisibility by `M * d` puts the target subgroup inside the conjugated source. -/
theorem gamma0_le_rescale_conjugate {M N d : ℕ} (hd : 0 < d)
    (h : M * d ∣ N) :
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct (rescaleMatrix d hd)⁻¹ •
        (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)) := by
  rintro _ ⟨γ, hγ, rfl⟩
  have hγd : γ ∈ CongruenceSubgroup.Gamma0 d := by
    rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_trans (Int.natCast_dvd_natCast.mpr
      (dvd_trans (dvd_mul_left d M) h)) (Eta.level_dvd_lower_left N γ hγ)
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, ConjAct.toConjAct_smul]
  change ∃ δ : SL(2, ℤ), δ ∈ CongruenceSubgroup.Gamma0 M ∧
    (δ : GL (Fin 2) ℝ) =
      rescaleMatrix d hd * (γ : GL (Fin 2) ℝ) * (rescaleMatrix d hd)⁻¹
  refine ⟨Eta.levelConjugate d γ hγd, ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    change (M : ℤ) ∣ γ 1 0 / (d : ℤ)
    obtain ⟨a, ha⟩ := dvd_trans (Int.natCast_dvd_natCast.mpr h)
      (Eta.level_dvd_lower_left N γ hγ)
    rw [ha]
    push_cast
    rw [mul_right_comm, Int.mul_ediv_cancel _ (by exact_mod_cast hd.ne')]
    exact dvd_mul_right _ _
  · apply (eq_mul_inv_iff_mul_eq).mpr
    exact (rescaleMatrix_mul d hd γ hγd).symm

end Oldforms

open Oldforms

/-- Rescale a weight-two `Γ₀(M)` cusp form by a positive integer `d`, and
regard the result as a form at any level `N` divisible by `M * d`.
The underlying function is exactly `z ↦ f (d * z)`, without a scalar factor. -/
def gamma0RescaleToLevel {M N : ℕ} (f : gamma0CuspForms M) (d : ℕ)
    (h : M * d ∣ N) (hd : 0 < d := by positivity) : gamma0CuspForms N :=
  (d : ℂ)⁻¹ • CuspForm.restrict (gamma0_le_rescale_conjugate hd h)
    (CuspForm.translate f (rescaleMatrix d hd))

@[simp] theorem gamma0RescaleToLevel_apply {M N : ℕ} (f : gamma0CuspForms M)
    (d : ℕ) (h : M * d ∣ N) (hd : 0 < d) (z : ℍ) :
    gamma0RescaleToLevel f d h hd z = f (Eta.dilate d (by exact_mod_cast hd) z) := by
  have hdℂ : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  change (d : ℂ)⁻¹ * ((f : ℍ → ℂ) ∣[(2 : ℤ)] rescaleMatrix d hd) z = _
  rw [ModularForm.slash_apply, rescaleMatrix_smul]
  simp [σ, denom, rescaleMatrix, hd, mul_comm, mul_left_comm, hdℂ]

@[simp] theorem gamma0RescaleToLevel_coe {M N : ℕ} (f : gamma0CuspForms M)
    (d : ℕ) (h : M * d ∣ N) (hd : 0 < d) :
    (gamma0RescaleToLevel f d h hd : ℍ → ℂ) =
      fun z ↦ f (Eta.dilate d (by exact_mod_cast hd) z) :=
  funext (gamma0RescaleToLevel_apply f d h hd)

/-- The degeneracy lift `z ↦ f (d * z)` from level `M` to level `M * d`.
The positivity proof is automatic for positive numeral dilation factors. -/
def gamma0Rescale {M : ℕ} (f : gamma0CuspForms M) (d : ℕ)
    (hd : 0 < d := by positivity) : gamma0CuspForms (M * d) :=
  gamma0RescaleToLevel f d dvd_rfl hd

@[simp] theorem gamma0Rescale_apply {M : ℕ} (f : gamma0CuspForms M)
    (d : ℕ) (hd : 0 < d) (z : ℍ) :
    gamma0Rescale f d hd z = f (Eta.dilate d (by exact_mod_cast hd) z) :=
  gamma0RescaleToLevel_apply f d dvd_rfl hd z

@[simp] theorem gamma0Rescale_coe {M : ℕ} (f : gamma0CuspForms M)
    (d : ℕ) (hd : 0 < d) :
    (gamma0Rescale f d hd : ℍ → ℂ) = fun z ↦ f (Eta.dilate d (by exact_mod_cast hd) z) :=
  funext (gamma0Rescale_apply f d hd)

@[simp] theorem gamma0RescaleToLevel_one {M N : ℕ} (f : gamma0CuspForms M)
    (h : M ∣ N) :
    gamma0RescaleToLevel f 1 (by simpa using h) = gamma0Restrict f h := by
  ext z
  simp [Eta.dilate]

/-- Rescaling by one preserves the underlying function; its bundled target
level is written `M * 1`. -/
@[simp] theorem gamma0Rescale_one {M : ℕ} (f : gamma0CuspForms M) :
    (gamma0Rescale f 1 : ℍ → ℂ) = f := by
  ext z
  simp [Eta.dilate]

@[simp] theorem gamma0RescaleToLevel_zero {M N : ℕ} (d : ℕ)
    (h : M * d ∣ N) (hd : 0 < d) : gamma0RescaleToLevel (0 : gamma0CuspForms M) d h hd = 0 := by
  ext z
  simp

@[simp] theorem gamma0RescaleToLevel_add {M N : ℕ} (f g : gamma0CuspForms M)
    (d : ℕ) (h : M * d ∣ N) (hd : 0 < d) :
    gamma0RescaleToLevel (f + g) d h hd =
      gamma0RescaleToLevel f d h hd + gamma0RescaleToLevel g d h hd := by
  ext z
  simp

@[simp] theorem gamma0RescaleToLevel_smul {M N : ℕ} (c : ℂ) (f : gamma0CuspForms M)
    (d : ℕ) (h : M * d ∣ N) (hd : 0 < d) :
    gamma0RescaleToLevel (c • f) d h hd = c • gamma0RescaleToLevel f d h hd := by
  ext z
  simp

@[simp] theorem gamma0Rescale_zero {M : ℕ} (d : ℕ) (hd : 0 < d) :
    gamma0Rescale (0 : gamma0CuspForms M) d hd = 0 :=
  gamma0RescaleToLevel_zero d dvd_rfl hd

@[simp] theorem gamma0Rescale_add {M : ℕ} (f g : gamma0CuspForms M)
    (d : ℕ) (hd : 0 < d) :
    gamma0Rescale (f + g) d hd = gamma0Rescale f d hd + gamma0Rescale g d hd :=
  gamma0RescaleToLevel_add f g d dvd_rfl hd

@[simp] theorem gamma0Rescale_smul {M : ℕ} (c : ℂ) (f : gamma0CuspForms M)
    (d : ℕ) (hd : 0 < d) :
    gamma0Rescale (c • f) d hd = c • gamma0Rescale f d hd :=
  gamma0RescaleToLevel_smul c f d dvd_rfl hd

/-- Rescaling into an ambient level, bundled as a complex linear map. -/
def gamma0RescaleToLevelₗ {M N : ℕ} (d : ℕ) (h : M * d ∣ N)
    (hd : 0 < d := by positivity) : gamma0CuspForms M →ₗ[ℂ] gamma0CuspForms N where
  toFun f := gamma0RescaleToLevel f d h hd
  map_add' f g := gamma0RescaleToLevel_add f g d h hd
  map_smul' c f := gamma0RescaleToLevel_smul c f d h hd

@[simp] theorem gamma0RescaleToLevelₗ_apply {M N : ℕ} (d : ℕ)
    (h : M * d ∣ N) (hd : 0 < d) (f : gamma0CuspForms M) :
    gamma0RescaleToLevelₗ d h hd f = gamma0RescaleToLevel f d h hd := rfl

/-- The complex linear degeneracy map from level `M` to level `M * d`. -/
def gamma0Rescaleₗ {M : ℕ} (d : ℕ) (hd : 0 < d := by positivity) :
    gamma0CuspForms M →ₗ[ℂ] gamma0CuspForms (M * d) :=
  gamma0RescaleToLevelₗ d dvd_rfl hd

@[simp] theorem gamma0Rescaleₗ_apply {M : ℕ} (d : ℕ) (hd : 0 < d)
    (f : gamma0CuspForms M) : gamma0Rescaleₗ d hd f = gamma0Rescale f d hd := rfl

/-- Restricting a rescaled form to a larger ambient level preserves the lift. -/
@[simp] theorem gamma0Restrict_rescaleToLevel {M N P : ℕ} (f : gamma0CuspForms M)
    (d : ℕ) (h : M * d ∣ N) (hd : 0 < d) (hNP : N ∣ P) :
    gamma0Restrict (gamma0RescaleToLevel f d h hd) hNP =
      gamma0RescaleToLevel f d (dvd_trans h hNP) hd := by
  ext z
  simp

/-- Iterated degeneracy lifts multiply their dilation factors. -/
theorem gamma0RescaleToLevel_trans {M N P : ℕ} (f : gamma0CuspForms M)
    (d e : ℕ) (h : M * d ∣ N) (h' : N * e ∣ P) (hd : 0 < d) (he : 0 < e) :
    gamma0RescaleToLevel (gamma0RescaleToLevel f d h hd) e h' he =
      gamma0RescaleToLevel f (d * e)
        (by simpa [Nat.mul_assoc] using dvd_trans (Nat.mul_dvd_mul_right h e) h')
        (Nat.mul_pos hd he) := by
  ext z
  simp only [gamma0RescaleToLevel_apply]
  congr 1
  apply UpperHalfPlane.ext
  simp [Eta.coe_dilate, Nat.cast_mul, mul_assoc]

/-- Positive dilation is injective on cusp forms, also at an ambient level. -/
theorem gamma0RescaleToLevel_injective {M N : ℕ} (d : ℕ)
    (h : M * d ∣ N) (hd : 0 < d) :
    Function.Injective (fun f : gamma0CuspForms M ↦ gamma0RescaleToLevel f d h hd) := by
  intro f g hfg
  ext z
  have hz := congrArg (fun F : gamma0CuspForms N ↦
    F (Eta.dilate (d : ℝ)⁻¹ (inv_pos.mpr (by exact_mod_cast hd)) z)) hfg
  simp only [gamma0RescaleToLevel_apply] at hz
  have hcancel : Eta.dilate d (by exact_mod_cast hd)
      (Eta.dilate (d : ℝ)⁻¹ (inv_pos.mpr (by exact_mod_cast hd)) z) = z := by
    apply UpperHalfPlane.ext
    simp [Eta.coe_dilate, Nat.ne_of_gt hd]
  simpa only [hcancel] using hz

theorem gamma0Rescale_injective {M : ℕ} (d : ℕ) (hd : 0 < d) :
    Function.Injective (fun f : gamma0CuspForms M ↦ gamma0Rescale f d hd) :=
  gamma0RescaleToLevel_injective d dvd_rfl hd

@[simp] theorem gamma0RescaleToLevel_eq_zero_iff {M N : ℕ} (f : gamma0CuspForms M)
    (d : ℕ) (h : M * d ∣ N) (hd : 0 < d) :
    gamma0RescaleToLevel f d h hd = 0 ↔ f = 0 :=
  (gamma0RescaleToLevel_injective d h hd).eq_iff' (gamma0RescaleToLevel_zero d h hd)

@[simp] theorem gamma0Rescale_eq_zero_iff {M : ℕ} (f : gamma0CuspForms M)
    (d : ℕ) (hd : 0 < d) : gamma0Rescale f d hd = 0 ↔ f = 0 :=
  gamma0RescaleToLevel_eq_zero_iff f d dvd_rfl hd

end WeightTwoCusps
