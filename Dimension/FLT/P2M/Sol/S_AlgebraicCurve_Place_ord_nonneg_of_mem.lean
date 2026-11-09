/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache 2.0 license.
Copied from anthropics/fermats-last-theorem, revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_AlgebraicCurve_Place_ord_nonneg_of_mem.lean.
Adapted for this project: local imports, modules, unused code, and shared proofs.
See Dimension/FLT/LICENSE, NOTICE, and ATTRIBUTION_UPSTREAM.md.
-/
module

public import Dimension.FLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import Dimension.FLT.P2M.Util

public import Dimension.FLT.EndScopes

@[expose] public section
namespace P2MW.S_AlgebraicCurve_Place_ord_nonneg_of_mem

open IsDedekindDomain WithZero IsLocalRing

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ord ord_unit_smul_zpow toValuationSubring"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem rowMain {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

end Place

end AlgebraicCurve

end

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_ord_nonneg_of_mem.AlgebraicCurve in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f :=
  AlgebraicCurve.Place.rowMain v hf


flt_end_scopes

/- Public statement copied from Theorems/Thm_AlgebraicCurve_Place_ord_nonneg_of_mem.lean. -/
@[expose] public section

open AlgebraicCurve
theorem AlgebraicCurve.Place.ord_nonneg_of_mem {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_ord_nonneg_of_mem.solution

