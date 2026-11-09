/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache 2.0 license.
Copied from anthropics/fermats-last-theorem, revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_AlgebraicCurve_indexOfSpecialty_eq_of_genusReached.lean.
Adapted for this project: local imports, modules, unused code, and shared proofs.
See Dimension/FLT/LICENSE, NOTICE, and ATTRIBUTION_UPSTREAM.md.
-/
module

public import Dimension.FLT.P2M.Sol.S_AlgebraicCurve_RationalFunctionField_ord_X_nonneg_of_ne_placeInfty

public import Dimension.FLT.EndScopes
public import Dimension.FLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import Dimension.FLT.Definitions.Def_AlgebraicCurve_Repartitions
public import Dimension.FLT.Definitions.Def_AlgebraicCurve_IsCurveOver
public import Dimension.FLT.Definitions.Def_AlgebraicCurve_AdelicIndex
public import Dimension.FLT.P2M.Util

@[expose] public section
namespace P2MW.S_AlgebraicCurve_indexOfSpecialty_eq_of_genusReached

open _root_.AlgebraicCurve in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] [Nonempty (Place K F)] [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (D : Divisor K F) :
    Module.Finite K (↥(adeleSpace K F) ⧸ adeleBddPrincipal K F D) ∧
      (indexOfSpecialty D : ℤ) = (ell D : ℤ) - (Divisor.degree D + 1 - γ) :=
  _root_.P2MW.S_AlgebraicCurve_RationalFunctionField_ord_X_nonneg_of_ne_placeInfty.AlgebraicCurve.indexOfSpecialty_eq_of_genusReached (K := K) (F := F) (γ := γ) (D₀ := D₀) h D


flt_end_scopes

/- Public statement copied from Theorems/Thm_AlgebraicCurve_indexOfSpecialty_eq_of_genusReached.lean. -/
@[expose] public section

namespace AlgebraicCurve
theorem indexOfSpecialty_eq_of_genusReached {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] [Nonempty (Place K F)] [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (D : Divisor K F) :
    Module.Finite K (↥(adeleSpace K F) ⧸ adeleBddPrincipal K F D) ∧
      (indexOfSpecialty D : ℤ) = (ell D : ℤ) - (Divisor.degree D + 1 - γ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_indexOfSpecialty_eq_of_genusReached.solution
end AlgebraicCurve

