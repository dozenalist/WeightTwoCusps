module

public import Dimension.Gamma_1.Formula
public import WeightTwoCusps.Tactic.Basic

/-! # Evaluate weight-two `Γ₁` dimensions at numeral levels

These proof-producing simprocs use the proved prime-product dimension formula.
They are registered with `simp`; abstract subgroup indices prevent `dsimp`
from evaluating the original definition at general numeral levels.
-/

public meta section

open Lean Meta Simp Qq

namespace WeightTwoCusps.Tactic

/-- Produce the arithmetic dimension certificate, handling the exceptional levels. -/
def certifyGamma1Dimension (n : Q(ℕ)) (N : Nat) : MetaM Simp.Result := do
  let value := gamma1Value N
  if N ≤ 4 then return ← certifyRat q(gamma1Dimension $n) value
  let hN : Q(5 ≤ $n) ← mkDecideProof q(5 ≤ $n)
  let formula := q(gamma1Dimension_eq_prime_product $n $hN)
  let .app (.app _ _) rhs ← inferType formula | throwError "expected a dimension equality"
  let cert ← certifyRat rhs value
  let proof ← mkEqTrans formula cert.proof?.get!
  return { expr := cert.expr, proof? := some proof }

/-- Evaluate the arithmetic `Γ₁` dimension at a numeral (also at zero). -/
simproc gamma1Dimension_ofNat (gamma1Dimension _) := fun e => do
  let_expr gamma1Dimension n := e | return .continue
  let some N ← getNatValue? n | return .continue
  return .done (← certifyGamma1Dimension n N)

/-- Evaluate the analytic `Γ₁` finrank at a positive numeral. -/
simproc gamma1CuspForms_finrank_ofNat (Module.finrank ℂ (gamma1CuspForms _)) := fun e => do
  have e : Q(ℕ) := e
  let ~q(Module.finrank ℂ (gamma1CuspForms $n)) := e | return .continue
  let some N ← getNatValue? n | return .continue
  if N == 0 then return .continue
  have n : Q(ℕ) := n
  let cert ← certifyGamma1Dimension n N
  let nz : Q($n ≠ 0) ← mkDecideProof q($n ≠ 0)
  let inst : Q(NeZero $n) := q(⟨$nz⟩)
  let formula := q(@gamma1CuspForms_dimension_formula $n $inst)
  return .done (← certifyFinrank (gamma1Value N) formula cert.proof?.get!)

end WeightTwoCusps.Tactic
