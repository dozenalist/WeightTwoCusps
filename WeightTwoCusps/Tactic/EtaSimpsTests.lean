module

public import WeightTwoCusps.Tactic.EtaSimps
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.Basis.Basic

/-! # Regression checks for generated coefficient and basis entry lemmas -/

@[expose] public noncomputable section

open UpperHalfPlane

namespace WeightTwoCusps.EtaSimpsTests

@[eta_simps] theorem signed (f : ℍ → ℂ)
    (h : first_coeffs 3 f = [0, 1, -2]) : first_coeffs 3 f = [0, 1, -2] := h

example (f : ℍ → ℂ) (h : first_coeffs 3 f = [0, 1, -2]) :
    (qExpansion 1 f).coeff 0 = 0 := signed_coeff_0 f h

example (f : ℍ → ℂ) (h : first_coeffs 3 f = [0, 1, -2]) :
    (qExpansion 1 f).coeff 2 = -2 := by simp only [signed_coeff_2 f h]

def namedCoefficients : List ℂ := [2, -3]

@[eta_simps] theorem named (f : ℍ → ℂ)
    (h : first_coeffs 2 f = namedCoefficients) : first_coeffs 2 f = namedCoefficients := h

example (f : ℍ → ℂ) (h : first_coeffs 2 f = namedCoefficients) :
    (qExpansion 1 f).coeff 1 = -3 := named_coeff_1 f h

@[eta_simps] theorem hundred (f : ℍ → ℂ)
    (h : first_coeffs 100 f = List.replicate 100 0) :
    first_coeffs 100 f = List.replicate 100 0 := h

example (f : ℍ → ℂ) (h : first_coeffs 100 f = List.replicate 100 0) :
    (qExpansion 1 f).coeff 99 = 0 := hundred_coeff_99 f h

@[eta_simps] theorem empty (f : ℍ → ℂ) : first_coeffs 0 f = [] := rfl

@[eta_simps] def pairBasis : Module.Basis (Fin 2) ℂ (Fin 2 → ℂ) := Pi.basisFun ℂ (Fin 2)

example : pairBasis 0 = Pi.single 0 1 := pairBasis_0
example : pairBasis 1 = Pi.single 1 1 := by simp only [pairBasis_1]

@[eta_simps] def emptyBasis : Module.Basis (Fin 0) ℂ (Fin 0 → ℂ) :=
  Pi.basisFun ℂ (Fin 0)

def namedVector {M : Type*} (v : Fin 3 → M) : Fin 3 → M := ![v 0, v 1, v 2]

/-- Keep named entries and all constructor parameters without normalizing the vector. -/
@[eta_simps] def vectorBasis {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (v : Fin 3 → M) (hli : LinearIndependent R (namedVector v))
    (hsp : ⊤ ≤ Submodule.span R (Set.range (namedVector v))) : Module.Basis (Fin 3) R M :=
  Module.Basis.mk hli hsp

example {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (v : Fin 3 → M) (hli : LinearIndependent R (namedVector v))
    (hsp : ⊤ ≤ Submodule.span R (Set.range (namedVector v))) :
    vectorBasis v hli hsp 0 = v 0 := vectorBasis_0 v hli hsp

example {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (v : Fin 3 → M) (hli : LinearIndependent R (namedVector v))
    (hsp : ⊤ ≤ Submodule.span R (Set.range (namedVector v))) :
    vectorBasis v hli hsp 2 = v 2 := by simp only [vectorBasis_2]

@[eta_simps] def functionBasis {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (v : Fin 2 → M) (hli : LinearIndependent R v)
    (hsp : ⊤ ≤ Submodule.span R (Set.range v)) : Module.Basis (Fin 2) R M :=
  Module.Basis.mk hli hsp

example {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (v : Fin 2 → M) (hli : LinearIndependent R v)
    (hsp : ⊤ ≤ Submodule.span R (Set.range v)) :
    functionBasis v hli hsp 1 = v 1 := functionBasis_1 v hli hsp

/-- error: eta_simps: expected a coefficient-prefix theorem or a `Module.Basis (Fin n) R M` definition -/
#guard_msgs in
@[eta_simps] theorem unsupported : True := trivial

#print axioms signed_coeff_2
#print axioms hundred_coeff_99
#print axioms pairBasis_1
#print axioms vectorBasis_2

end WeightTwoCusps.EtaSimpsTests
