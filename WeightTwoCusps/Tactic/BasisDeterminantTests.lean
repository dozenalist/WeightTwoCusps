module

public import WeightTwoCusps.Basis
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«42».Old.«14_2_a_a_old_42_1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«42».Old.«14_2_a_a_old_42_3»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«42».New.«42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«42».New.«42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4»
public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«42».New.«42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1»
public import Mathlib.Data.ZMod.Basic

/-! # General finite-matrix regressions for `cusp_basis` -/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

open UpperHalfPlane

namespace WeightTwoCusps.BasisDeterminantTests

example : Module.finrank ℂ (gamma0CuspForms 42) = 5 := by
  cusp_basis_dimension

example : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 42).strictPeriods := by
  cusp_basis_period

theorem specialized_integer_det : (!![(1 : ℤ), 1; 1, 31]).det ≠ 0 := by
  matrix_det

theorem integral_entries_over_field {K : Type*} [Field K] [CharZero K] :
    (!![(0 : K), 1, 0, 0, 0;
        1, 2, 0, 0, 0;
        1, 1, -3, 0, 0;
        0, 0, 1, 2, 0;
        0, 1, 0, -1, 7]).det ≠ 0 := by
  matrix_det

example : True := by
  let a : ℚ := 1 / 2
  have : (!![(0 : ℚ), a, 0, 0, 0;
      -3, 2 / 3, 0, 0, 0;
      1, 1, -2 / 5, 0, 0;
      0, 0, 1, 3, 0;
      0, 1, 0, -1, 7]).det ≠ 0 := by matrix_det
  trivial

-- The structural proof works for symbolic size, entries, and coefficient ring.
example {K : Type*} [CommRing K] [IsDomain K] {n : ℕ} (d : Fin n → K)
    (hd : ∀ i, d i ≠ 0) : (Matrix.diagonal d).det ≠ 0 := by
  matrix_det_triangular

-- Every constructor obligation can also come from an abstract hypothesis.
-- In particular, positivity and period membership are not restricted to 1.
example {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] {k : ℤ} {n : ℕ}
    [FiniteDimensional ℂ (CuspForm Γ k)] (v : Fin n → CuspForm Γ k)
    (c : Fin n → ℕ) (h : ℝ) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (hdim : Module.finrank ℂ (CuspForm Γ k) = n)
    (hdet : (qExpansionMatrix h v c).det ≠ 0) :
    Module.Basis (Fin n) ℂ (CuspForm Γ k) :=
  cuspFormBasis v c h

-- The mathematical bridge has no numeral-size or index-type restriction.
example {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) (h : A.rank = Fintype.card ι) : A.det ≠ 0 :=
  matrix_det_ne_zero_of_rank_eq_card A h

theorem empty_det : (Matrix.of ![] : Matrix (Fin 0) (Fin 0) ℚ).det ≠ 0 := by
  cusp_basis

theorem singleton_det : (!![(-3 / 7 : ℚ)]).det ≠ 0 := by
  cusp_basis

-- A zero first pivot forces a row swap. Nonintegral entries require scaling.
-- The field is a local parameter, so this also exercises open type contexts.
theorem pivoted_rational_det {K : Type*} [Field K] [CharZero K] :
    (!![(0 : K), 1 / 2, 0, 0, 0;
        -3, 2 / 3, 0, 0, 0;
        1, 1, -2 / 5, 0, 0;
        0, 0, 1, 3, 0;
        0, 1, 0, -1, 7]).det ≠ 0 := by
  cusp_basis

-- A named function, rather than a matrix literal, is reflected entrywise.
def denseTwelve : Matrix (Fin 12) (Fin 12) ℚ :=
  fun i j ↦ if i = j then 2 else 1

theorem dense_twelve_det : denseTwelve.det ≠ 0 := by
  cusp_basis

abbrev mappedRows : List (List ℤ) :=
  [[0, 1, 0, 0], [1, 2, 0, 0], [0, 0, -3, 0], [0, 1, 0, 2]]

def mappedListMatrix : Matrix (Fin 4) (Fin 4) ℚ :=
  (Mathlib.Tactic.Matrix.ofLists 4 4 mappedRows).map (Int.castRingHom ℚ)

theorem mapped_list_det : mappedListMatrix.det ≠ 0 := by
  cusp_basis

theorem finite_field_det :
    (!![(0 : ZMod 5), 1, 0, 0, 0;
        1, 2, 0, 0, 0;
        1, 0, 1, 0, 0;
        0, 0, 1, 1, 0;
        0, 1, 0, 2, 1]).det ≠ 0 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  cusp_basis

-- Symbolic dimensions retain the previous simplification fallback.
example (n : ℕ) : (1 : Matrix (Fin n) (Fin n) ℂ).det ≠ 0 := by
  cusp_basis

example (a b c d : ℂ) : (!![a, b; c, d]).det = a * d - b * c := by
  cusp_basis

-- A singular five-by-five matrix must be rejected.
example : True := by
  fail_if_success
    have : (!![(1 : ℚ), 0, 0, 0, 0;
        0, 1, 0, 0, 0;
        0, 0, 1, 0, 0;
        0, 0, 0, 1, 0;
        1, 0, 0, 0, 0]).det ≠ 0 := by cusp_basis
  fail_if_success
    have : (!![(1 : ℚ), 0; 0, 1]).det ≠ 1 := by cusp_basis
  trivial

def forms42 : Fin 5 → gamma0CuspForms 42 :=
  ![cuspForm_14_2_a_a_old_42_1, cuspForm_14_2_a_a_old_42_3,
    cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1,
    cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4,
    cuspForm_42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1]

theorem level42_det : (qExpansionMatrix 1 forms42 (fun i ↦ i.val + 1)).det ≠ 0 := by
  cusp_basis

-- Constructor certification materializes a list table and persists a checked witness.
-- Complete publication before the following cache-only proof starts elaborating.
set_option Elab.async false in
theorem level42_cached_det : (qExpansionMatrix 1 forms42 ![1, 2, 3, 5, 6]).det ≠ 0 := by
  q_expansion_matrix
  det_ne_zero! cusp_basis_det_config%

-- The same table can be certified with the Sage producer disabled.
set_option Elab.async false in
theorem level42_cached_det_replay :
    (qExpansionMatrix 1 forms42 ![1, 2, 3, 5, 6]).det ≠ 0 := by
  q_expansion_matrix
  det_ne_zero! { cusp_basis_det_config% with policy := .cacheOnly, executable := "must-not-launch" }

-- The selected minor extends beyond the dimension, and has determinant -6.
def level42_custom_basis : Module.Basis (Fin 5) ℂ (gamma0CuspForms 42) :=
  cuspFormBasis forms42 (c := ![1, 2, 3, 5, 6])

theorem level42_independent : LinearIndependent ℂ forms42 := by
  cusp_basis using ![1, 2, 3, 5, 6]

example : True := by
  let forms := forms42
  have : (qExpansionMatrix 1 forms ![1, 2, 3, 5, 6]).det ≠ 0 := by cusp_basis
  fail_if_success
    have : (qExpansionMatrix 1 forms ![1, 2, 3, 4, 4]).det ≠ 0 := by cusp_basis
  trivial

abbrev shortPrefixOne : gamma0CuspForms 22 :=
  etaQuotientCuspForm 22 sparse![22; 0 => 2, 10 => 2]

abbrev shortPrefixTwo : gamma0CuspForms 22 :=
  etaQuotientCuspForm 22 sparse![22; 1 => 2, 21 => 2]

theorem shortPrefixOne_first_coeffs : first_coeffs 3 shortPrefixOne = [0, 1, -2] := by
  eta_coeff

theorem shortPrefixTwo_first_coeffs : first_coeffs 3 shortPrefixTwo = [0, 0, 1] := by
  eta_coeff

-- Coefficient four lies outside both stored prefixes, and is certified anew.
def short_prefix_custom_basis : Module.Basis (Fin 2) ℂ (gamma0CuspForms 22) :=
  cuspFormBasis ![shortPrefixOne, shortPrefixTwo] (c := ![1, 4])

#print axioms matrix_det_ne_zero_of_rank_eq_card
#print axioms empty_det
#print axioms specialized_integer_det
#print axioms integral_entries_over_field
#print axioms singleton_det
#print axioms pivoted_rational_det
#print axioms dense_twelve_det
#print axioms mapped_list_det
#print axioms finite_field_det
#print axioms level42_det
#print axioms level42_cached_det
#print axioms level42_cached_det_replay
#print axioms level42_custom_basis
#print axioms level42_independent
#print axioms short_prefix_custom_basis

end WeightTwoCusps.BasisDeterminantTests
