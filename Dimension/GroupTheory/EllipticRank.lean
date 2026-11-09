module

public import Dimension.GroupTheory.BassSerreRank
public import Dimension.GroupTheory.HomTransport
public import Dimension.GroupTheory.ParabolicRank

/-! # Rational homomorphism rank in the presence of elliptic stabilizers -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups
open Monoid
open P2MW.S_Monoid_CoprodI_nonempty_freeGroupBasis_fin_kuroshRank.GroupTheory
open P2MW.S_Matrix_SpecialLinearGroup_nonempty_freeGroupBasis_map_quotient_center_of_forall_trace_ne.ModularCurve.FreeTransport
open scoped P2MW.S_Monoid_CoprodI_nonempty_freeGroupBasis_fin_kuroshRank.GroupTheory.BassSerre

namespace WeightTwoCusps

private theorem range_G23_eq_zpowers (i : Fin 2) :
    (CoprodI.of (M := G23) (i := i)).range =
      Subgroup.zpowers (CoprodI.of (M := G23) (i := i) (Multiplicative.ofAdd 1)) := by
  have hz : Subgroup.zpowers (Multiplicative.ofAdd 1 : G23 i) = ⊤ := by
    rw [eq_top_iff]
    intro a _
    apply Subgroup.mem_zpowers_iff.mpr
    refine ⟨(a.toAdd.val : ℤ), ?_⟩
    rw [← ofAdd_zsmul]
    simp only [zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_zmod_val, mul_one, ofAdd_toAdd]
  rw [← MonoidHom.map_zpowers, hz, Subgroup.map_top]

/-- The Bass--Serre graph identity for every finite-index modular subgroup
containing `-I`, with no trace exclusions. -/
theorem finrank_rationalHom_add_elliptic_orbits (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : SL(2, ℤ)) ∈ Γ) :
    Module.finrank ℚ (Additive Γ →+ ℚ) +
      Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.S) (SL(2, ℤ) ⧸ Γ)) +
      Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers (ModularGroup.S * ModularGroup.T))
        (SL(2, ℤ) ⧸ Γ)) = 1 + Γ.index := by
  let : (pulledBack Γ).FiniteIndex := ⟨by
    rw [index_pulledBack Γ hneg]
    exact Subgroup.FiniteIndex.index_ne_zero⟩
  obtain ⟨D, _, hD⟩ := BassSerre.exists_transversal (pulledBack Γ) (BassSerre.Vertex.mk 0 1)
  have h := BassSerreHoms.finrank_hom_add_card_vertex_orbits hD
  let ep : pulledBack Γ ≃* bar Γ :=
    (e.subgroupMap (pulledBack Γ)).trans (MulEquiv.subgroupCongr (map_pulledBack Γ))
  have hrp : Module.finrank ℚ (Additive (bar Γ) →+ ℚ) =
      Module.finrank ℚ (Additive (pulledBack Γ) →+ ℚ) :=
    finrank_rationalHom_of_surjective ep.toMonoidHom ep.surjective (by
      intro x hx
      have hx1 : x = 1 := ep.injective (hx.trans ep.map_one.symm)
      rw [hx1]
      exact isOfFinOrder_iff_pow_eq_one.mpr ⟨1, by decide, one_pow _⟩)
  let q := QuotientGroup.mk' (Subgroup.center SL(2, ℤ))
  have hqker : q.ker ≤ Γ := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    rcases (mem_center_iff_eq x).mp hx with rfl | rfl
    · exact Γ.one_mem
    · exact hneg
  have hcomap : (bar Γ).comap q = Γ := Subgroup.comap_map_eq_self hqker
  have hrΓ : Module.finrank ℚ (Additive (bar Γ) →+ ℚ) =
      Module.finrank ℚ (Additive Γ →+ ℚ) := by
    apply finrank_rationalHom_of_surjective (q.subgroupMap Γ) (q.subgroupMap_surjective Γ)
    intro x hx
    rcases
      P2MW.S_Matrix_SpecialLinearGroup_finrank_addMonoidHom_eq_of_forall_trace_ne.ModularCurve.FreeModNegOne.eq_one_or_eq_neg_of_toBar_eq_one
        Γ hneg hx with rfl | rfl
    · exact isOfFinOrder_iff_pow_eq_one.mpr ⟨1, by decide, one_pow _⟩
    · apply isOfFinOrder_iff_pow_eq_one.mpr
      refine ⟨2, by decide, Subtype.ext ?_⟩
      simp [pow_two]
  have hcomp (i : Fin 2) :
      Nat.card (FreeActionTree.ComponentOrbits (pulledBack Γ) i) =
        Nat.card (MulAction.orbitRel.Quotient
          (Subgroup.zpowers (CoprodI.of (M := G23) (i := i) (Multiplicative.ofAdd 1)))
          (CoprodI G23 ⧸ pulledBack Γ)) := by
    rw [← range_G23_eq_zpowers]
    exact
      P2MW.S_Subgroup_card_orbitRelQuotient_mul_card_eq_index.GroupTheory.FreeDoubleCoset.card_orbitRel_quotient_eq
        (pulledBack Γ) _
  let : ∀ i : Fin 2, Finite (FreeActionTree.ComponentOrbits (pulledBack Γ) i) := fun i =>
    Finite.of_equiv
      (MulAction.orbitRel.Quotient (CoprodI.of (M := G23) (i := i)).range
        (CoprodI G23 ⧸ pulledBack Γ))
      (P2MW.S_Subgroup_card_orbitRelQuotient_mul_card_eq_index.GroupTheory.FreeDoubleCoset.orbitQuotientEquiv
        (pulledBack Γ) (CoprodI.of (M := G23) (i := i)).range).symm
  rw [Nat.card_congr (FreeActionTree.vertexOrbitEquivSigma (pulledBack Γ)), Nat.card_sigma,
    Fin.sum_univ_two, hcomp 0, hcomp 1, ← hrp, hrΓ, index_pulledBack Γ hneg] at h
  have hS := card_comap_cyclic_orbits e.toMonoidHom e.surjective (bar Γ)
    (CoprodI.of (M := G23) (i := 0) (Multiplicative.ofAdd 1))
  have hST := card_comap_cyclic_orbits e.toMonoidHom e.surjective (bar Γ)
    (CoprodI.of (M := G23) (i := 1) (Multiplicative.ofAdd 1))
  rw [MulEquiv.coe_toMonoidHom, e_of_zero] at hS
  rw [MulEquiv.coe_toMonoidHom, e_of_one] at hST
  have hS' := card_comap_cyclic_orbits q (QuotientGroup.mk'_surjective _) (bar Γ) ModularGroup.S
  have hST' := card_comap_cyclic_orbits q (QuotientGroup.mk'_surjective _) (bar Γ)
    (ModularGroup.S * ModularGroup.T)
  rw [hcomap] at hS' hST'
  change Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.S) (SL(2, ℤ) ⧸ Γ)) =
    Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers (QuotientGroup.mk ModularGroup.S))
      (PSL ⧸ bar Γ)) at hS'
  change Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers (ModularGroup.S * ModularGroup.T))
    (SL(2, ℤ) ⧸ Γ)) =
    Nat.card (MulAction.orbitRel.Quotient
      (Subgroup.zpowers (QuotientGroup.mk (ModularGroup.S * ModularGroup.T))) (PSL ⧸ bar Γ)) at hST'
  erw [hS, hST, ← hS', ← hST'] at h
  omega

end WeightTwoCusps
