module

public import Dimension.GroupTheory.EllipticOrbits
public import Dimension.Gamma_0.CuspCoordinates
public import Dimension.Gamma_0.Formula

/-! # The two elliptic orbit corrections for `Γ₀(N)` -/

@[expose] public section

noncomputable section

open scoped MatrixGroups

namespace WeightTwoCusps

abbrev gamma0SOrbitCount (N : ℕ) : ℕ :=
  Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.S)
    (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N))

abbrev gamma0STOrbitCount (N : ℕ) : ℕ :=
  Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers (ModularGroup.S * ModularGroup.T))
    (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N))

/-- The order-two vertex orbits include one singleton for each elliptic fixed coset. -/
theorem two_mul_gamma0SOrbitCount (N : ℕ) [NeZero N] :
    2 * gamma0SOrbitCount N = (CongruenceSubgroup.Gamma0 N).index +
      gamma0EllipticTwoCount N := by
  have hper (x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
      ModularGroup.S ^ 2 • x = x := by
    have hS : ModularGroup.S ^ 2 = (-1 : SL(2, ℤ)) := by
      apply Subtype.ext
      simpa [sq] using ModularGroup.S_mul_S_eq
    rw [hS]
    exact neg_one_smul_coset _ (neg_one_mem_Gamma0 N) x
  simpa only [gamma0_card_fixedBy_S, Nat.reduceSub, one_mul] using
    prime_mul_card_cyclic_orbits SL(2, ℤ) (CongruenceSubgroup.Gamma0 N)
      ModularGroup.S 2 hper

/-- The order-three vertex orbits include one singleton for each elliptic fixed coset. -/
theorem three_mul_gamma0STOrbitCount (N : ℕ) [NeZero N] :
    3 * gamma0STOrbitCount N = (CongruenceSubgroup.Gamma0 N).index +
      2 * gamma0EllipticThreeCount N := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hper (x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
      (ModularGroup.S * ModularGroup.T) ^ 3 • x = x := by
    rw [P2MW.S_ModularCurve_six_mul_level_mul_finrank_parabolicHoms_Gamma_add_eq.BettiPrincipal.ST_pow_three]
    exact neg_one_smul_coset _ (neg_one_mem_Gamma0 N) x
  simpa only [gamma0_card_fixedBy_ST, Nat.reduceSub] using
    prime_mul_card_cyclic_orbits SL(2, ℤ) (CongruenceSubgroup.Gamma0 N)
      (ModularGroup.S * ModularGroup.T) 3 hper

/-- The elliptic correction is now a consequence of the single graph rank identity. -/
theorem gamma0_hom_rank_relation_of_orbit_rank (N : ℕ) [NeZero N]
    (h : Module.finrank ℚ (Additive (CongruenceSubgroup.Gamma0 N) →+ ℚ) +
      gamma0SOrbitCount N + gamma0STOrbitCount N = 1 + (CongruenceSubgroup.Gamma0 N).index) :
    6 * Module.finrank ℚ (Additive (CongruenceSubgroup.Gamma0 N) →+ ℚ) +
      3 * gamma0EllipticTwoCount N + 4 * gamma0EllipticThreeCount N =
        6 + (CongruenceSubgroup.Gamma0 N).index := by
  have h₂ := two_mul_gamma0SOrbitCount N
  have h₃ := three_mul_gamma0STOrbitCount N
  omega

/-- All arithmetic and analytic inputs are discharged once the finite-stabilizer
graph rank identity is available. -/
theorem gamma0CuspForms_dimension_formula_of_orbit_rank (N : ℕ) (hN : 2 ≤ N)
    (h : Module.finrank ℚ (Additive (CongruenceSubgroup.Gamma0 N) →+ ℚ) +
      gamma0SOrbitCount N + gamma0STOrbitCount N = 1 + (CongruenceSubgroup.Gamma0 N).index) :
    (Module.finrank ℂ (gamma0CuspForms N) : ℚ) = gamma0Dimension N := by
  let : NeZero N := ⟨by omega⟩
  exact gamma0CuspForms_dimension_formula_of_hom_rank N hN
    (gamma0_hom_rank_relation_of_orbit_rank N h)

end WeightTwoCusps
