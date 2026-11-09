module

public import Dimension.GroupTheory.BassSerreHoms

/-! # Integration of subgroup-invariant Bass--Serre edge cochains -/

@[expose] public section

noncomputable section

open P2MW.S_Monoid_CoprodI_nonempty_freeGroupBasis_fin_kuroshRank.GroupTheory
open Monoid
open scoped P2MW.S_Monoid_CoprodI_nonempty_freeGroupBasis_fin_kuroshRank.GroupTheory.BassSerre

namespace WeightTwoCusps.BassSerreHoms

open BassSerre GraphTransversal

variable {G : Fin 2 → Type*} [∀ i, Group (G i)] [∀ i, Finite (G i)]
  {H : Subgroup (CoprodI G)} {D : Set (Vertex G)}

def edgeElement {v w : Vertex G} (h : (graph G).Adj v w) : CoprodI G := h.2.choose

theorem edgeElement_spec {v w : Vertex G} (h : (graph G).Adj v w) :
    Vertex.mk v.1 (edgeElement h) = v ∧ Vertex.mk w.1 (edgeElement h) = w :=
  h.2.choose_spec

theorem edgeElement_eq {v w : Vertex G} (h : (graph G).Adj v w) (g : CoprodI G)
    (hv : Vertex.mk v.1 g = v) (hw : Vertex.mk w.1 g = w) : edgeElement h = g :=
  eq_of_mk_eq_mk h.1 ((edgeElement_spec h).1.trans hv.symm)
    ((edgeElement_spec h).2.trans hw.symm)

/-- A function on subgroup edge orbits determines an antisymmetric oriented edge weight. -/
def edgeWeight (c : (CoprodI G ⧸ H) → ℚ) (v w : Vertex G) : ℚ := by
  classical
  exact
  if h : (graph G).Adj v w then
    if v.1 = 0 then c ((edgeElement h)⁻¹ : CoprodI G) else -c ((edgeElement h)⁻¹ : CoprodI G)
  else 0

theorem edgeWeight_mk (c : (CoprodI G ⧸ H) → ℚ) (g : CoprodI G) :
    edgeWeight c (Vertex.mk 0 g) (Vertex.mk 1 g) = c (g⁻¹ : CoprodI G) := by
  have hadj := adj_mk (G := G) (by decide : (0 : Fin 2) ≠ 1) g
  simp only [edgeWeight, dite_eq_left hadj]
  rw [edgeElement_eq hadj g rfl rfl]
  simp only [ite_true]

theorem edgeWeight_mk_rev (c : (CoprodI G ⧸ H) → ℚ) (g : CoprodI G) :
    edgeWeight c (Vertex.mk 1 g) (Vertex.mk 0 g) = -c (g⁻¹ : CoprodI G) := by
  have hadj := adj_mk (G := G) (by decide : (1 : Fin 2) ≠ 0) g
  simp only [edgeWeight, dite_eq_left hadj, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
  rw [edgeElement_eq hadj g rfl rfl]

private theorem adj_cases {v w : Vertex G} (h : (graph G).Adj v w) :
    ∃ g : CoprodI G,
      (v = Vertex.mk 0 g ∧ w = Vertex.mk 1 g) ∨
      (v = Vertex.mk 1 g ∧ w = Vertex.mk 0 g) := by
  obtain ⟨hne, g, hv, hw⟩ := h
  refine ⟨g, ?_⟩
  have hcases : v.1 = 0 ∧ w.1 = 1 ∨ v.1 = 1 ∧ w.1 = 0 :=
    (by decide : ∀ i j : Fin 2, i ≠ j →
      i = 0 ∧ j = 1 ∨ i = 1 ∧ j = 0) v.1 w.1 hne
  rcases hcases with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · exact Or.inl ⟨by simpa only [hi] using hv.symm, by simpa only [hj] using hw.symm⟩
  · exact Or.inr ⟨by simpa only [hi] using hv.symm, by simpa only [hj] using hw.symm⟩

theorem edgeWeight_antisymm (c : (CoprodI G ⧸ H) → ℚ) (v w : Vertex G)
    (hadj : (graph G).Adj v w) : edgeWeight c w v = -edgeWeight c v w := by
  obtain ⟨g, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := adj_cases hadj
  · rw [edgeWeight_mk, edgeWeight_mk_rev]
  · rw [edgeWeight_mk, edgeWeight_mk_rev, neg_neg]

theorem edgeWeight_smul (c : (CoprodI G ⧸ H) → ℚ) (η : H) (v w : Vertex G)
    (hadj : (graph G).Adj v w) : edgeWeight c (η • v) (η • w) = edgeWeight c v w := by
  have hcoset (g : CoprodI G) :
      ((((η : CoprodI G) * g)⁻¹ : CoprodI G) : CoprodI G ⧸ H) =
        ((g⁻¹ : CoprodI G) : CoprodI G ⧸ H) := by
    rw [QuotientGroup.eq]
    have heq : (((η : CoprodI G) * g)⁻¹)⁻¹ * g⁻¹ = (η : CoprodI G) := by group
    rw [heq]
    exact η.property
  obtain ⟨g, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := adj_cases hadj
  · change edgeWeight c (Vertex.mk 0 ((η : CoprodI G) * g))
      (Vertex.mk 1 ((η : CoprodI G) * g)) = _
    rw [edgeWeight_mk, edgeWeight_mk, hcoset]
  · change edgeWeight c (Vertex.mk 1 ((η : CoprodI G) * g))
      (Vertex.mk 0 ((η : CoprodI G) * g)) = _
    rw [edgeWeight_mk_rev, edgeWeight_mk_rev, hcoset]

/-- Every edge cochain vanishing on the transversal tree integrates to a rational
homomorphism, without any assumption of free vertex action. -/
theorem edgeEvaluation_exists (hD : IsConnectedTransversal (graph G) H D)
    (c : (CoprodI G ⧸ H) → ℚ)
    (hc : ∀ g : CoprodI G, Vertex.mk 0 g ∈ D → Vertex.mk 1 g ∈ D →
      c (g⁻¹ : CoprodI G) = 0) :
    ∃ φ : Additive H →+ ℚ, edgeEvaluation hD φ = c := by
  classical
  obtain ⟨base, hbase, -⟩ := hD.exists_mem_orbit (Vertex.mk 0 1)
  obtain ⟨F, hF⟩ := TreePotentials.exists_potential BassSerre.isTree_two base
    (edgeWeight c) (edgeWeight_antisymm c)
  have hinv (η : H) (v w : Vertex G) (hadj : (graph G).Adj v w) :
      F (η • w) - F (η • v) = F w - F v := by
    rw [hF _ _ (smul_adj_subgroup η hadj), hF _ _ hadj, edgeWeight_smul c η v w hadj]
  have hconstant (η : H) (v : Vertex G) :
      F (η • v) - F v = F (η • base) - F base :=
    TreePotentials.translated_difference_constant BassSerre.connected.preconnected F hinv η base v
  let φ : Additive H →+ ℚ := TreePotentials.potentialHom base F hconstant
  have hφeval (η : H) (v : Vertex G) :
      φ (Additive.ofMul η) = F (η • v) - F v := (hconstant η v).symm
  have hzero (v w : D) (hadj : ((graph G).induce D).Adj v w) :
      F w.val - F v.val = 0 := by
    have hadj' : (graph G).Adj v.val w.val := hadj
    rw [hF v.val w.val hadj']
    obtain ⟨g, ⟨hv, hw⟩ | ⟨hv, hw⟩⟩ := adj_cases hadj'
    · rw [hv, hw, edgeWeight_mk]
      exact hc g (hv ▸ v.property) (hw ▸ w.property)
    · rw [hv, hw, edgeWeight_mk_rev, hc g (hw ▸ w.property) (hv ▸ v.property), neg_zero]
  have hDconstant (v : Vertex G) (hv : v ∈ D) : F v = F base := by
    have h := TreePotentials.difference_constant
      (connected_induce_transversal hD).preconnected (fun v : D => F v.val) (fun _ => 0)
      (fun v w hadj => by simpa only [sub_self] using hzero v w hadj)
      ⟨base, hbase⟩ ⟨v, hv⟩
    simpa only [sub_zero] using h
  have htrans (v : Vertex G) : φ (Additive.ofMul (transl hD v)) = F v - F base := by
    rw [hφeval (transl hD v) (orbitRepr hD v), transl_smul_orbitRepr,
      hDconstant _ (orbitRepr_mem hD v)]
  have hedge (g : CoprodI G) : φ (Additive.ofMul (edgeGen hD g)) = c (g⁻¹ : CoprodI G) := by
    simp only [edgeGen, ofMul_mul, ofMul_inv, map_add, map_neg, htrans]
    have h := hF _ _ (adj_mk (by decide : (0 : Fin 2) ≠ 1) g)
    rw [edgeWeight_mk] at h
    linarith
  refine ⟨φ, funext fun q => ?_⟩
  induction q using QuotientGroup.induction_on with
  | H g =>
    change φ (Additive.ofMul (edgeGen hD g⁻¹)) = c (g : CoprodI G ⧸ H)
    simpa only [inv_inv] using hedge g⁻¹

end WeightTwoCusps.BassSerreHoms
