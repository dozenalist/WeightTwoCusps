/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache 2.0 license.
Copied from anthropics/fermats-last-theorem, revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_AlgebraicCurve_isAlgebraic_adjoin_of_transcendental.lean.
Adapted for this project: local imports, modules, unused code, and shared proofs.
See Dimension/FLT/LICENSE, NOTICE, and ATTRIBUTION_UPSTREAM.md.
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Dimension.FLT.P2M.Util

public import Dimension.FLT.EndScopes
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.Algebraic.Defs

@[expose] public section
namespace P2MW.S_AlgebraicCurve_isAlgebraic_adjoin_of_transcendental

open Set Cardinal

namespace AlgebraicCurve
namespace FF2KE3

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem isAlgebraic_adjoin_of_transcendental' (x : F)
    [halg : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    {t : F} (ht : Transcendental K t) :
    Algebra.IsAlgebraic (IntermediateField.adjoin K ({t} : Set F)) F := by

  have hx : Transcendental K x := by
    intro hxalg
    haveI : Algebra.IsAlgebraic K (IntermediateField.adjoin K ({x} : Set F)) :=
      IntermediateField.isAlgebraic_adjoin_simple hxalg.isIntegral
    haveI : Algebra.IsAlgebraic K F :=
      Algebra.IsAlgebraic.trans K (IntermediateField.adjoin K ({x} : Set F)) F
    exact ht (Algebra.IsAlgebraic.isAlgebraic t)

  have hbx : IsTranscendenceBasis K ![x] := by
    rw [isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic]
    refine ⟨algebraicIndependent_iff_transcendental.mpr hx, ?_⟩
    have : Set.range ![x] = {x} := by simp
    rw [this]
    exact (IntermediateField.isAlgebraic_adjoin_iff_top (F := K) (s := ({x} : Set F))).mp halg

  have hind : AlgebraicIndepOn K id ({t} : Set F) := by
    rw [AlgebraicIndepOn, algebraicIndependent_unique_type_iff]
    simpa using ht
  obtain ⟨S, htS, hS⟩ := exists_isTranscendenceBasis_superset hind

  have hcard := hS.lift_cardinalMk_eq hbx
  simp only [Cardinal.mk_fin, Nat.cast_one, Cardinal.lift_one, Cardinal.lift_eq_one] at hcard
  have hS_eq : S = {t} :=
    (Cardinal.mk_le_one_iff_set_subsingleton.mp hcard.le).eq_singleton_of_mem (htS rfl)
  subst hS_eq
  have h := hS.isAlgebraic_field
  rwa [Subtype.range_coe] at h

end AlgebraicCurve.FF2KE3

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] {t : F} (ht : Transcendental K t) :
    Algebra.IsAlgebraic (IntermediateField.adjoin K ({t} : Set F)) F :=
  AlgebraicCurve.FF2KE3.isAlgebraic_adjoin_of_transcendental' x ht


flt_end_scopes

/- Public statement copied from Theorems/Thm_AlgebraicCurve_isAlgebraic_adjoin_of_transcendental.lean. -/
@[expose] public section

theorem AlgebraicCurve.isAlgebraic_adjoin_of_transcendental {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] {t : F} (ht : Transcendental K t) :
    Algebra.IsAlgebraic (IntermediateField.adjoin K ({t} : Set F)) F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_isAlgebraic_adjoin_of_transcendental.solution

