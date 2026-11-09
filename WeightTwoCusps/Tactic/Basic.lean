module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Rat.Cast.Defs
public meta import Mathlib.Data.Nat.Totient
public meta import Mathlib.Data.Nat.PrimeFin
public meta import Mathlib.Util.Qq
public meta import Lean.Elab.Tactic.Simproc

/-! # Shared arithmetic and certificates for numeral dimension simprocs -/

@[expose] public section

namespace WeightTwoCusps.Tactic

/-- Convert a certified rational dimension to its natural value. -/
theorem nat_eq_of_dimension_certificate {d n : ℕ} {q : ℚ}
    (h : (d : ℚ) = q) (hq : q = (n : ℚ)) : d = n :=
  Rat.natCast_injective (h.trans hq)

end WeightTwoCusps.Tactic

public meta section

open Lean Meta Qq

namespace WeightTwoCusps.Tactic

/-- Distinct prime divisors, used only to propose a value for a checked certificate. -/
def primeDivisors (n : Nat) : List Nat := n.primeFactorsList.eraseDups

/-- The prime product common to the principal and `Γ₁` formulas. -/
def indexProduct (n : Nat) : Rat :=
  ((primeDivisors n).map fun p => 1 - 1 / (p : Rat) ^ 2).prod

/-- Positive divisors (the empty list at zero, as for `Nat.divisors`). -/
def divisors (n : Nat) : List Nat :=
  if n = 0 then [] else (List.range (n + 1)).filter fun d => n % d == 0

/-- Compute the arithmetic `Γ₀` expression without evaluating analytic objects. -/
def gamma0Value (n : Nat) : Rat :=
  let psi := (n : Rat) * ((primeDivisors n).map fun p => 1 + 1 / (p : Rat)).prod
  let e₂ := ((List.range n).filter fun a => (a ^ 2 + 1) % n == 0).length
  let e₃ := ((List.range n).filter fun a => (a ^ 2 + a + 1) % n == 0).length
  let c := ((divisors n).map fun d => Nat.totient (Nat.gcd d (n / d))).sum
  1 + psi / 12 - (e₂ : Rat) / 4 - (e₃ : Rat) / 3 - (c : Rat) / 2

/-- Compute the exceptional-small-level and prime-product `Γ₁` expression. -/
def gamma1Value (n : Nat) : Rat :=
  if n ≤ 4 then 0 else
    let c := ((divisors n).map fun d => Nat.totient d * Nat.totient (n / d)).sum
    1 + (n : Rat) ^ 2 / 24 * indexProduct n - (c : Rat) / 4

/-- Compute the principal-level expression, including the small positive levels. -/
def gammaValue (n : Nat) : Rat :=
  if n ≤ 5 then 0 else
    1 + (n : Rat) ^ 2 * ((n : Rat) - 6) / 24 * indexProduct n

/-- Build a closed rational equality certificate using kernel reduction. -/
def certifyRat (e : Expr) (value : Rat) : MetaM Simp.Result := do
  let lit := toExpr value
  let proof ← withTransparency .all <| mkDecideProof (← mkEq e lit)
  return { expr := lit, proof? := some proof }

/-- Convert the rational formula and its closed certificate into a finrank result. -/
def certifyFinrank (value : Rat) (formula certificate : Expr) : MetaM Simp.Result := do
  unless value.den == 1 && value.num ≥ 0 do
    throwError "the dimension certificate is not a natural number"
  let proof ← mkAppM ``nat_eq_of_dimension_certificate #[formula, certificate]
  return { expr := mkNatLit value.num.toNat, proof? := some proof }

end WeightTwoCusps.Tactic

end

namespace WeightTwoCusps.Tactic

open Lean

/-- A vector with the given entries and zero at all unspecified indices. -/
syntax "sparse![" num ";" (num " => " term),* "]" : term

macro_rules
  | `(sparse![$n:num; $[$idxs:num => $vals:term],*]) => do
      let index ← `(i)
      let mut body ← `(0)
      for k in [:idxs.size] do
        let i := idxs[k]!.getNat
        if i ≥ n.getNat then
          Macro.throwError "sparse vector index out of bounds"
        -- Later entries retain the existing last-write-wins semantics.
        let idx : TSyntax `term := ⟨idxs[k]!.raw⟩
        body ← `(if ($index : Fin $n).val = $idx then $(vals[k]!) else $body)
      `(fun $index : Fin $n => $body)

def exampleTuple : Fin 10 → ℤ :=
  sparse![10; 0 => 2, 9 => 12]

example :
    exampleTuple = ![2, 0, 0, 0, 0, 0, 0, 0, 0, 12] := by decide +kernel

example : exampleTuple 9 = 12 := rfl
example : exampleTuple 5 = 0 := rfl

end WeightTwoCusps.Tactic
