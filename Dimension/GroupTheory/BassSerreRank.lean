/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache 2.0 license.
The transversal-edge equivalence adapts the attributed local Kurosh module
from anthropics/fermats-last-theorem, revision 6e837e75355538c7f80bab5b956861e86c4eacc2.
See Dimension/FLT/LICENSE, NOTICE, and ATTRIBUTION_UPSTREAM.md.
-/
module

public import Dimension.GroupTheory.BassSerreCochains
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Rational homomorphism rank for finite-index subgroups of a free product

The transversal-edge equivalence adapts the corresponding construction in
the attributed FLT Kurosh module, replacing its free vertex action hypothesis
by uniqueness of the two endpoints of an edge.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open P2MW.S_Monoid_CoprodI_nonempty_freeGroupBasis_fin_kuroshRank.GroupTheory
open Monoid
open scoped P2MW.S_Monoid_CoprodI_nonempty_freeGroupBasis_fin_kuroshRank.GroupTheory.BassSerre

namespace WeightTwoCusps.BassSerreHoms

open BassSerre GraphTransversal

variable {G : Fin 2 → Type*} [∀ i, Group (G i)] [∀ i, Finite (G i)]
  {H : Subgroup (CoprodI G)} {D : Set (Vertex G)}

abbrev TransversalEdges (D : Set (Vertex G)) :=
  {g : CoprodI G // Vertex.mk 0 g ∈ D ∧ Vertex.mk 1 g ∈ D}

def treeEdgeCosets (_hD : IsConnectedTransversal (graph G) H D) : Set (CoprodI G ⧸ H) :=
  {q | ∃ g : CoprodI G, Vertex.mk 0 g ∈ D ∧ Vertex.mk 1 g ∈ D ∧
    ((g⁻¹ : CoprodI G) : CoprodI G ⧸ H) = q}

variable (hD : IsConnectedTransversal (graph G) H D)

def transversalEdgesEquivCosets : TransversalEdges D ≃ treeEdgeCosets hD :=
  Equiv.ofBijective (fun g => ⟨((g.val⁻¹ : CoprodI G) : CoprodI G ⧸ H),
    g.val, g.property.1, g.property.2, rfl⟩) (by
    constructor
    · intro g k hgk
      have heq := congrArg Subtype.val hgk
      have hm : g.val * k.val⁻¹ ∈ H := by
        simpa only [inv_inv] using QuotientGroup.eq.mp heq
      let η : H := ⟨g.val * k.val⁻¹, hm⟩
      have hmk (i : Fin 2) : Vertex.mk i g.val = Vertex.mk i k.val := by
        have hg : Vertex.mk i g.val ∈ D := by
          fin_cases i
          · exact g.property.1
          · exact g.property.2
        have hk : Vertex.mk i k.val ∈ D := by
          fin_cases i
          · exact k.property.1
          · exact k.property.2
        apply hD.eq_of_mem_orbit _ hg _ hk
        refine ⟨η, ?_⟩
        change Vertex.mk i ((g.val * k.val⁻¹) * k.val) = Vertex.mk i g.val
        rw [mul_assoc, inv_mul_cancel, mul_one]
      exact Subtype.ext (eq_of_mk_eq_mk (by decide : (0 : Fin 2) ≠ 1) (hmk 0) (hmk 1))
    · rintro ⟨q, g, h₀, h₁, rfl⟩
      exact ⟨⟨g, h₀, h₁⟩, rfl⟩)

def transversalEdgesEquivEdgeSet : TransversalEdges D ≃ ((graph G).induce D).edgeSet :=
  Equiv.ofBijective (fun g =>
    ⟨s((⟨Vertex.mk 0 g.val, g.property.1⟩ : D), (⟨Vertex.mk 1 g.val, g.property.2⟩ : D)),
      adj_mk (by decide : (0 : Fin 2) ≠ 1) g.val⟩) (by
    constructor
    · intro g k hgk
      rw [Subtype.mk.injEq, Sym2.eq_iff] at hgk
      rcases hgk with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
      · exact Subtype.ext (eq_of_mk_eq_mk (by decide : (0 : Fin 2) ≠ 1)
          (congrArg Subtype.val h₀) (congrArg Subtype.val h₁))
      · exact (by decide : (0 : Fin 2) ≠ 1) (congrArg (fun v : D => v.val.1) h₀) |>.elim
    · rintro ⟨e, he⟩
      revert he
      induction e using Sym2.ind with
      | _ v w =>
        intro he
        obtain ⟨hne, g, hv, hw⟩ := (he : ((graph G).induce D).Adj v w)
        have hcases := (by decide : ∀ i j : Fin 2, i ≠ j →
          i = 0 ∧ j = 1 ∨ i = 1 ∧ j = 0) _ _ hne
        rcases hcases with ⟨hi, hj⟩ | ⟨hi, hj⟩
        · rw [hi] at hv
          rw [hj] at hw
          refine ⟨⟨g, by rw [hv]; exact v.property, by rw [hw]; exact w.property⟩, ?_⟩
          exact Subtype.ext (Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext hv, Subtype.ext hw⟩))
        · rw [hi] at hv
          rw [hj] at hw
          refine ⟨⟨g, by rw [hw]; exact w.property, by rw [hv]; exact v.property⟩, ?_⟩
          exact Subtype.ext (Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext hw, Subtype.ext hv⟩)))

theorem finite_vertex_orbits [H.FiniteIndex] :
    Finite (MulAction.orbitRel.Quotient H (Vertex G)) := by
  let : ∀ i : Fin 2, Finite (FreeActionTree.ComponentOrbits H i) := fun i =>
    Finite.of_equiv
      (MulAction.orbitRel.Quotient (CoprodI.of (M := G) (i := i)).range (CoprodI G ⧸ H))
      (P2MW.S_Subgroup_card_orbitRelQuotient_mul_card_eq_index.GroupTheory.FreeDoubleCoset.orbitQuotientEquiv
        H (CoprodI.of (M := G) (i := i)).range).symm
  exact Finite.of_equiv _ (FreeActionTree.vertexOrbitEquivSigma H).symm

theorem card_treeEdgeCosets_add_one [H.FiniteIndex] :
    Nat.card (treeEdgeCosets hD) + 1 = Nat.card (MulAction.orbitRel.Quotient H (Vertex G)) := by
  let : Finite (MulAction.orbitRel.Quotient H (Vertex G)) := finite_vertex_orbits
  let : Finite D := Finite.of_equiv _ (transversalEquivOrbits hD).symm
  let : Fintype D := Fintype.ofFinite _
  let : Fintype ((graph G).induce D).edgeSet := Fintype.ofFinite _
  rw [← Nat.card_congr (transversalEdgesEquivCosets hD),
    Nat.card_congr (transversalEdgesEquivEdgeSet (D := D)), ← nat_card_transversal hD]
  have h := SimpleGraph.IsTree.card_edgeFinset
    ⟨connected_induce_transversal hD, isAcyclic_induce_transversal (D := D)⟩
  simpa only [SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card] using h

def treeRestriction : ((CoprodI G ⧸ H) → ℚ) →ₗ[ℚ] (treeEdgeCosets hD → ℚ) where
  toFun c q := c q.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem treeRestriction_surjective : Function.Surjective (treeRestriction hD) := by
  classical
  intro c
  refine ⟨fun q => if h : q ∈ treeEdgeCosets hD then c ⟨q, h⟩ else 0, funext fun q => ?_⟩
  exact dite_eq_left q.property

theorem edgeEvaluation_range_eq_ker :
    LinearMap.range (edgeEvaluation hD) = LinearMap.ker (treeRestriction hD) := by
  apply Submodule.ext
  intro c
  constructor
  · rintro ⟨φ, rfl⟩
    apply LinearMap.mem_ker.mpr
    funext q
    obtain ⟨g, h₀, h₁, hg⟩ := q.property
    change edgeEvaluation hD φ q.val = 0
    rw [← hg]
    change φ (Additive.ofMul (edgeGen hD g⁻¹⁻¹)) = 0
    simpa only [inv_inv] using hom_edgeGen_eq_zero hD φ g h₀ h₁
  · intro hc
    apply LinearMap.mem_range.mpr
    apply edgeEvaluation_exists hD c
    intro g h₀ h₁
    have h := congrFun (LinearMap.mem_ker.mp hc)
      ⟨((g⁻¹ : CoprodI G) : CoprodI G ⧸ H), g, h₀, h₁, rfl⟩
    exact h

include hD in
/-- The finite-stabilizer Bass--Serre rank identity over the rationals. -/
theorem finrank_hom_add_card_vertex_orbits [H.FiniteIndex] :
    Module.finrank ℚ (Additive H →+ ℚ) +
      Nat.card (MulAction.orbitRel.Quotient H (Vertex G)) = 1 + H.index := by
  let : Fintype (CoprodI G ⧸ H) := Fintype.ofFinite _
  let : Fintype (treeEdgeCosets hD) := Fintype.ofFinite _
  have h := (treeRestriction hD).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (treeRestriction_surjective hD), finrank_top,
    ← edgeEvaluation_range_eq_ker hD,
    LinearMap.finrank_range_of_inj (edgeEvaluation_injective hD),
    Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at h
  have htree := card_treeEdgeCosets_add_one hD
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card] at h
  omega

end WeightTwoCusps.BassSerreHoms
