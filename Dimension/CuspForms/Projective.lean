module

public import Dimension.CuspForms.Restriction
public import Dimension.GroupTheory.ProjectiveSubgroup

@[expose] public section

/-! # Adjoining `-I` does not change weight-two cusp forms -/

open scoped MatrixGroups ModularForm
open UpperHalfPlane

noncomputable section

namespace WeightTwoCusps

/-- At even weight two the slash action is insensitive to the sign of a matrix. -/
lemma slash_neg_weightTwo (f : ℍ → ℂ) (g : SL(2, ℤ)) :
    f ∣[(2 : ℤ)] (-g) = f ∣[(2 : ℤ)] g := by
  have heq : ((-g : SL(2, ℤ)) : GL (Fin 2) ℝ) = -(g : GL (Fin 2) ℝ) := by
    ext i j
    simp
  ext z
  simp only [ModularForm.SL_slash_apply]
  rw [heq]
  simp

/-- A weight-two cusp form extends to the projective closure with the same values. -/
def weightTwoCuspForms_projective (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (f : CuspForm Γ 2) : CuspForm (projectiveClosure Γ) 2 where
  toFun := f
  slash_action_eq' g hg := by
    obtain ⟨γ, hγ, rfl⟩ := hg
    change (f : ℍ → ℂ) ∣[(2 : ℤ)] γ = f
    rcases (mem_projectiveClosure_iff Γ γ).mp hγ with h | h
    · exact SlashInvariantFormClass.slash_action_eq f _ ⟨γ, h, rfl⟩
    · have hf := SlashInvariantFormClass.slash_action_eq f _ ⟨-γ, h, rfl⟩
      change (f : ℍ → ℂ) ∣[(2 : ℤ)] (-γ) = f at hf
      simpa only [slash_neg_weightTwo] using hf
  holo' := f.holo'
  zero_at_cusps' hc := by
    apply f.zero_at_cusps'
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
    exact hc

/-- The analytic spaces before and after adjoining `-I` are canonically isomorphic. -/
def weightTwoCuspForms_projectiveEquiv (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    CuspForm Γ 2 ≃ₗ[ℂ] CuspForm (projectiveClosure Γ) 2 where
  toFun := weightTwoCuspForms_projective Γ
  invFun := weightTwoCuspForms_restrict le_sup_left
  left_inv _ := DFunLike.ext _ _ fun _ => rfl
  right_inv _ := DFunLike.ext _ _ fun _ => rfl
  map_add' _ _ := DFunLike.ext _ _ fun _ => rfl
  map_smul' _ _ := DFunLike.ext _ _ fun _ => rfl

theorem weightTwoCuspForms_finrank_projectiveClosure (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    Module.finrank ℂ (CuspForm Γ 2) =
      Module.finrank ℂ (CuspForm (projectiveClosure Γ) 2) :=
  (weightTwoCuspForms_projectiveEquiv Γ).finrank_eq

end WeightTwoCusps
