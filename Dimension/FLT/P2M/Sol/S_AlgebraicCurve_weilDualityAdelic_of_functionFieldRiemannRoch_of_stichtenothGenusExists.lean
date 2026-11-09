/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache 2.0 license.
Copied from anthropics/fermats-last-theorem, revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists.lean.
Adapted for this project: local imports, modules, unused code, and shared proofs.
See Dimension/FLT/LICENSE, NOTICE, and ATTRIBUTION_UPSTREAM.md.
-/
module

public import Dimension.FLT.MathlibImports
public import Dimension.FLT.Definitions.Def_AlgebraicCurve_AdelicIndex
public import Dimension.FLT.Definitions.Def_AlgebraicCurve_RiemannRochRows
public import Dimension.FLT.P2M.Sol.S_AlgebraicCurve_indexOfSpecialty_eq_of_genusReached
public import Dimension.FLT.P2M.Sol.S_AlgebraicCurve_ell_eq_zero_of_degree_neg
public import Dimension.FLT.P2M.Util

public import Dimension.FLT.EndScopes

@[expose] public section
namespace P2MW.S_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (hRR : AlgebraicCurve.FunctionFieldRiemannRoch K F)
    (hSG : AlgebraicCurve.StichtenothGenusExists K F) :
    AlgebraicCurve.WeilDualityAdelic K F := by
  intro _instCurve _instCan _instDC ω hω D
  obtain ⟨⟨v⟩, hfd, γ, D₀, hγ⟩ := hSG
  haveI : Nonempty (Place K F) := ⟨v⟩
  haveI : FiniteDimensional K ↥(LSpace (0 : Divisor K F)) := hfd

  have hi : ∀ D' : Divisor K F,
      (indexOfSpecialty D' : ℤ) = (ell D' : ℤ) - (Divisor.degree D' + 1 - γ) :=
    fun D' => (indexOfSpecialty_eq_of_genusReached hγ D').2

  have hdegv : 0 < (v.deg : ℤ) := by
    haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank K v.ResidueField)

  have hγle : γ ≤ (genus K F : ℤ) := by
    have h₁ := hRR hω D₀
    have h₂ := hγ.eq
    have h₃ : (0 : ℤ) ≤ (ell (canonicalDivisorOf hω - D₀) : ℤ) := Nat.cast_nonneg _
    linarith

  have hgeγ : (genus K F : ℤ) ≤ γ := by
    set D₁ : Divisor K F := canonicalDivisorOf hω + Finsupp.single v 1 with hD₁
    have hKD : canonicalDivisorOf hω - D₁ = -Finsupp.single v 1 := by
      rw [hD₁]; abel
    have hneg : Divisor.degree (canonicalDivisorOf hω - D₁) < 0 := by
      rw [hKD, map_neg, Divisor.degree_single]
      linarith
    have hℓ : ell (canonicalDivisorOf hω - D₁) = 0 := ell_eq_zero_of_degree_neg hneg
    have h₁ := hRR hω D₁
    have h₂ := hγ.isMax D₁
    rw [hℓ] at h₁
    push_cast at h₁
    linarith
  have hγg : γ = (genus K F : ℤ) := le_antisymm hγle hgeγ
  have h₁ := hi D
  have h₂ := hRR hω D
  rw [hγg] at h₁
  linarith


flt_end_scopes

/- Public statement copied from Theorems/Thm_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists.lean. -/
@[expose] public section

theorem AlgebraicCurve.weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (hRR : AlgebraicCurve.FunctionFieldRiemannRoch K F)
    (hSG : AlgebraicCurve.StichtenothGenusExists K F) :
    AlgebraicCurve.WeilDualityAdelic K F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists.solution

