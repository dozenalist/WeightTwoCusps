module

public import Dimension.Gamma_0.Formula
public import Dimension.Gamma_0.CuspsPrime

/-! # Explicit dimensions at prime levels with no elliptic points -/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

/-- The dimension at prime level with the two elliptic root obstructions absent.
The assumptions are finite arithmetic tests, rather than dimension hypotheses. -/
theorem gamma0CuspForms_dimension_formula_prime_of_no_roots (p : ℕ) [Fact p.Prime]
    (h₂ : ∀ a : ZMod p, a ^ 2 + 1 ≠ 0)
    (h₃ : ∀ a : ZMod p, a ^ 2 + a + 1 ≠ 0) :
    (Module.finrank ℂ (gamma0CuspForms p) : ℚ) = ((p : ℚ) + 1) / 12 := by
  have hp : p.Prime := Fact.out
  have hr := gamma0CuspForms_geometric_dimension_relation_of_trace_ne p hp.two_le
    (Gamma0_trace_ne_of_no_roots p h₂ h₃)
  rw [gamma0GeometricCuspCount_prime] at hr
  have hq : (12 : ℚ) * Module.finrank ℂ (gamma0CuspForms p) + 12 =
      12 + ((CongruenceSubgroup.Gamma0 p).index : ℚ) := by exact_mod_cast hr
  rw [CongruenceIndex.Gamma0_index', CongruenceIndex.psi, hp.primeFactors,
    Finset.prod_singleton] at hq
  have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  field_simp [hpQ] at hq
  nlinarith

/-- A positive-dimensional `Γ₀(N)` cusp-form space. -/
theorem gamma0CuspForms_finrank_eleven : Module.finrank ℂ (gamma0CuspForms 11) = 1 := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  have h := gamma0CuspForms_dimension_formula_prime_of_no_roots 11 (by decide) (by decide)
  norm_num at h
  exact_mod_cast h

/-- A second positive-dimensional example, obtained from the same uniform proof. -/
theorem gamma0CuspForms_finrank_twentyThree :
    Module.finrank ℂ (gamma0CuspForms 23) = 2 := by
  letI : Fact (Nat.Prime 23) := ⟨by decide⟩
  have h := gamma0CuspForms_dimension_formula_prime_of_no_roots 23 (by decide) (by decide)
  norm_num at h
  exact_mod_cast h

end WeightTwoCusps
