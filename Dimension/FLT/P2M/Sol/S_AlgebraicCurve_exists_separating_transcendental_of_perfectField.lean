/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache 2.0 license.
Copied from anthropics/fermats-last-theorem, revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_AlgebraicCurve_exists_separating_transcendental_of_perfectField.lean.
Adapted for this project: local imports, modules, unused code, and shared proofs.
See Dimension/FLT/LICENSE, NOTICE, and ATTRIBUTION_UPSTREAM.md.
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Algebraic.Basic
public import Dimension.FLT.P2M.Util
public import Dimension.FLT.EndScopes

@[expose] public section
namespace P2MW.S_AlgebraicCurve_exists_separating_transcendental_of_perfectField

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K]
    {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    ∃ t : F, Transcendental K t ∧
      FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F ∧
      Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F := by
  let E := IntermediateField.adjoin K ({x} : Set F)
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  haveI : FiniteDimensional E F := hfd
  haveI : Algebra.IsAlgebraic E F := Algebra.IsAlgebraic.of_finite E F
  exact ⟨x, htr, hfd, Algebra.IsAlgebraic.isSeparable_of_perfectField⟩

flt_end_scopes

/- Public statement copied from Theorems/Thm_AlgebraicCurve_exists_separating_transcendental_of_perfectField.lean. -/
@[expose] public section

theorem AlgebraicCurve.exists_separating_transcendental_of_perfectField
    {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K]
    {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    ∃ t : F, Transcendental K t ∧
      FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F ∧
      Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_separating_transcendental_of_perfectField.solution

