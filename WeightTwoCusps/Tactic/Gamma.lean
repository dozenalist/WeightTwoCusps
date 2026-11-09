module

public import Dimension.Gamma.Formula
public import WeightTwoCusps.Tactic.Basic

/-! # Evaluate weight-two principal congruence dimensions at numeral levels

Both simprocs use the analytic dimension theorem to evaluate the abstract
projective index in `gammaDimension`. Use `simp`, or name the simprocs
explicitly in `simp only`.
-/

@[expose] public section

namespace WeightTwoCusps.Tactic

/-- The rational prime-product formula also computes the natural dimension expression. -/
theorem gammaDimension_eq_of_certificate (N n : ℕ) [NeZero N] (hN : 3 ≤ N)
    (h : 1 + (N : ℚ) ^ 2 * ((N : ℚ) - 6) / 24 *
      ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) = (n : ℚ)) :
    gammaDimension N = n := by
  rw [← gammaCuspForms_dimension_formula N]
  exact nat_eq_of_dimension_certificate
    (gammaCuspForms_dimension_formula_prime_product N hN) h

/-- The exceptional positive principal levels have arithmetic dimension zero. -/
theorem gammaDimension_eq_zero_of_small (N : ℕ) [NeZero N] (hN : N ≤ 5) :
    gammaDimension N = 0 := by
  rw [← gammaCuspForms_dimension_formula N]
  exact gammaCuspForms_finrank_eq_zero_of_le_five N hN

end WeightTwoCusps.Tactic

public meta section

open Lean Meta Simp Qq

namespace WeightTwoCusps.Tactic

/-- A checked certificate for the natural principal-level dimension expression. -/
def certifyGammaDimension (n : Q(ℕ)) (N : Nat) : MetaM Simp.Result := do
  let value := gammaValue N
  unless value.den == 1 && value.num ≥ 0 do
    throwError "the principal dimension certificate is not a natural number"
  have lit : Q(ℕ) := mkNatLit value.num.toNat
  if N == 0 then
    let proof ← withTransparency .all <| mkDecideProof q(gammaDimension $n = $lit)
    return { expr := lit, proof? := some proof }
  let nz : Q($n ≠ 0) ← mkDecideProof q($n ≠ 0)
  let inst : Q(NeZero $n) := q(⟨$nz⟩)
  if N ≤ 5 then
    let hN : Q($n ≤ 5) ← mkDecideProof q($n ≤ 5)
    let proof := q(@gammaDimension_eq_zero_of_small $n $inst $hN)
    return { expr := lit, proof? := some proof }
  let hN : Q(3 ≤ $n) ← mkDecideProof q(3 ≤ $n)
  have rhs : Q(ℚ) := q(1 + ($n : ℚ) ^ 2 * (($n : ℚ) - 6) / 24 *
    ∏ p ∈ Nat.primeFactors $n, (1 - 1 / (p : ℚ) ^ 2))
  let cert : Q($rhs = ($lit : ℚ)) ←
    withTransparency .all <| mkDecideProof q($rhs = ($lit : ℚ))
  let proof ← mkAppOptM ``gammaDimension_eq_of_certificate
    #[some n, some lit, some inst, some hN, some cert]
  return { expr := lit, proof? := some proof }

/-- Evaluate the arithmetic principal-level dimension at a numeral. -/
simproc gammaDimension_ofNat (gammaDimension _) := fun e => do
  let_expr gammaDimension n := e | return .continue
  let some N ← getNatValue? n | return .continue
  return .done (← certifyGammaDimension n N)

/-- Evaluate the analytic principal-level finrank at a positive numeral. -/
simproc gammaCuspForms_finrank_ofNat (Module.finrank ℂ (gammaCuspForms _)) := fun e => do
  have e : Q(ℕ) := e
  let ~q(Module.finrank ℂ (gammaCuspForms $n)) := e | return .continue
  let some N ← getNatValue? n | return .continue
  if N == 0 then return .continue
  have n : Q(ℕ) := n
  let cert ← certifyGammaDimension n N
  let nz : Q($n ≠ 0) ← mkDecideProof q($n ≠ 0)
  let inst : Q(NeZero $n) := q(⟨$nz⟩)
  let formula := q(@gammaCuspForms_dimension_formula $n $inst)
  let proof ← mkEqTrans formula cert.proof?.get!
  return .done { expr := cert.expr, proof? := some proof }

end WeightTwoCusps.Tactic
