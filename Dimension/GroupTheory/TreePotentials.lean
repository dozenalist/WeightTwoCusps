module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Integrating antisymmetric edge weights on a tree -/

@[expose] public section

noncomputable section

namespace WeightTwoCusps.TreePotentials

open SimpleGraph

variable {V : Type*} {T : SimpleGraph V}

/-- The integral of an oriented edge weight along a finite walk. -/
def integral (f : V → V → ℚ) {v w : V} : T.Walk v w → ℚ
  | .nil => 0
  | @SimpleGraph.Walk.cons _ _ a b _ _ p => f a b + integral f p

theorem integral_concat (f : V → V → ℚ) {v w z : V} (p : T.Walk v w) (h : T.Adj w z) :
    integral f (p.concat h) = integral f p + f w z := by
  induction p with
  | nil => simp [SimpleGraph.Walk.concat_nil, integral]
  | cons h' p ih =>
    rw [SimpleGraph.Walk.concat_cons, integral, ih, integral]
    ring

/-- Every antisymmetric edge assignment on a tree is a difference of vertex potentials. -/
theorem exists_potential (hT : T.IsTree) (base : V) (f : V → V → ℚ)
    (hanti : ∀ v w, T.Adj v w → f w v = -f v w) :
    ∃ F : V → ℚ, ∀ v w, T.Adj v w → F w - F v = f v w := by
  classical
  let path (v : V) : T.Walk base v := (hT.existsUnique_path base v).choose
  have hpath (v : V) : (path v).IsPath := (hT.existsUnique_path base v).choose_spec.1
  let F (v : V) := integral f (path v)
  refine ⟨F, fun v w hadj => ?_⟩
  by_cases hv : v ∈ (path w).support
  · have heq := hT.isAcyclic.path_concat (hpath v) (hpath w) hadj hv
    change integral f (path w) - integral f (path v) = f v w
    rw [heq, integral_concat]
    ring
  · have hw := hT.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath
      (hpath v) (hpath w) hadj hv
    have heq := hT.isAcyclic.path_concat (hpath w) (hpath v) hadj.symm hw
    change integral f (path w) - integral f (path v) = f v w
    rw [heq, integral_concat, hanti v w hadj]
    ring

/-- On a connected graph, two vertex functions with equal edge differences
differ by the same constant at every vertex. -/
theorem difference_constant (hT : T.Preconnected) (F K : V → ℚ)
    (h : ∀ v w, T.Adj v w → F w - F v = K w - K v) (base v : V) :
    F v - K v = F base - K base := by
  obtain ⟨p⟩ := hT base v
  induction p with
  | nil => rfl
  | @cons a b c hadj p ih =>
    have hab := h a b hadj
    linarith

/-- An invariant edge difference makes translation of a potential differ by
a constant. This is the basic additive cocycle used for quotient graphs. -/
theorem translated_difference_constant {H : Type*} [Group H] [MulAction H V]
    (hT : T.Preconnected)
    (F : V → ℚ)
    (hinv : ∀ (η : H) v w, T.Adj v w →
      F (η • w) - F (η • v) = F w - F v)
    (η : H) (base v : V) :
    F (η • v) - F v = F (η • base) - F base := by
  exact difference_constant hT (fun w => F (η • w)) F (hinv η) base v

/-- The constants by which a potential changes under a group action form a homomorphism. -/
def potentialHom {H : Type*} [Group H] [MulAction H V] (base : V) (F : V → ℚ)
    (hconstant : ∀ (η : H) v, F (η • v) - F v = F (η • base) - F base) :
    Additive H →+ ℚ where
  toFun η := F (Additive.toMul η • base) - F base
  map_zero' := by simp
  map_add' η δ := by
    change F ((Additive.toMul η * Additive.toMul δ) • base) - F base = _
    rw [mul_smul]
    have h := hconstant (Additive.toMul η) (Additive.toMul δ • base)
    linarith

end WeightTwoCusps.TreePotentials
