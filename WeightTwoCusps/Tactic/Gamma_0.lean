module

public import Dimension.Gamma_0.FullFormula
public import WeightTwoCusps.Tactic.Basic

/-! # Evaluate weight-two `Γ₀` dimensions at numeral levels

The arithmetic dimension is definitionally computable, so its dsimproc also
works with `dsimp`. The analytic finrank uses the proved dimension formula
and therefore requires `simp` (or `simp only [gamma0CuspForms_finrank_ofNat]`).
-/

public meta section

open Lean Meta Simp Qq

namespace WeightTwoCusps.Tactic

/-- Evaluate the arithmetic `Γ₀` dimension at a numeral, including zero. -/
dsimproc gamma0Dimension_ofNat (gamma0Dimension _) := fun e => do
  let_expr gamma0Dimension n := e | return .continue
  let some N ← getNatValue? n | return .continue
  return .done (toExpr (gamma0Value N))

/-- Evaluate the analytic `Γ₀` finrank at a positive numeral. -/
simproc gamma0CuspForms_finrank_ofNat (Module.finrank ℂ (gamma0CuspForms _)) := fun e => do
  have e : Q(ℕ) := e
  let ~q(Module.finrank ℂ (gamma0CuspForms $n)) := e | return .continue
  let some N ← getNatValue? n | return .continue
  if N == 0 then return .continue
  have n : Q(ℕ) := n
  let value := gamma0Value N
  let cert ← certifyRat q(gamma0Dimension $n) value
  let nz : Q($n ≠ 0) ← mkDecideProof q($n ≠ 0)
  let inst : Q(NeZero $n) := q(⟨$nz⟩)
  let formula := q(@gamma0CuspForms_dimension_formula $n $inst)
  return .done (← certifyFinrank value formula cert.proof?.get!)

end WeightTwoCusps.Tactic
