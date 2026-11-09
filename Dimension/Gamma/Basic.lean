module

public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

@[expose] public section

/-!
# Weight-two cusp forms for principal congruence subgroups

The spaces in this file are Mathlib's analytic cusp-form spaces, with their usual
complex vector-space structure. The level-one statements are consequences of
Mathlib's division-by-the-discriminant isomorphism; they require no new axioms.
-/

noncomputable section

namespace WeightTwoCusps

/-- The complex vector space of weight-two cusp forms for `Γ(N)`. -/
abbrev gammaCuspForms (N : ℕ) := CuspForm (CongruenceSubgroup.Gamma N) 2

/-- There are no nonzero weight-two cusp forms of level one. -/
theorem gammaCuspForms_rank_one : Module.rank ℂ (gammaCuspForms 1) = 0 := by
  apply rank_zero_iff_forall_zero.mpr
  intro f
  let g : CuspForm (Matrix.SpecialLinearGroup.mapGL ℝ).range 2 :=
    f.mcast rfl CongruenceSubgroup.Gamma_one_coe_eq_SL.symm
  have hg : g = 0 := rank_zero_iff_forall_zero.mp
    (CuspForm.rank_eq_zero_of_weight_lt_twelve (k := 2) (by norm_num)) g
  exact DFunLike.ext _ _ fun z => DFunLike.congr_fun hg z

/-- Every weight-two cusp form of level one vanishes identically. -/
theorem gammaCuspForms_one_eq_zero (f : gammaCuspForms 1) : f = 0 :=
  rank_zero_iff_forall_zero.mp gammaCuspForms_rank_one f

instance : FiniteDimensional ℂ (gammaCuspForms 1) :=
  FiniteDimensional.of_rank_eq_zero gammaCuspForms_rank_one

/-- The dimension of the space of weight-two cusp forms of level one is zero. -/
theorem gammaCuspForms_finrank_one : Module.finrank ℂ (gammaCuspForms 1) = 0 :=
  finrank_zero_iff_forall_zero.mpr gammaCuspForms_one_eq_zero

end WeightTwoCusps
