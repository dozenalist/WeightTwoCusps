/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache 2.0 license.
Copied from anthropics/fermats-last-theorem, revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_AlgebraicCurve_SemilinearAut_ord_algebraMap_smul.lean.
Adapted for this project: local imports, modules, unused code, and shared proofs.
See Dimension/FLT/LICENSE, NOTICE, and ATTRIBUTION_UPSTREAM.md.
-/
module

public import Dimension.FLT.Definitions.Def_AlgebraicCurve_Correspondence
public import Dimension.FLT.P2M.Util

public import Dimension.FLT.EndScopes

@[expose] public section
namespace P2MW.S_AlgebraicCurve_SemilinearAut_ord_algebraMap_smul

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} (hgg' : IntertwinesAlong (algebraMap F F') g g') (w : Place K F') (f : F) : (g' • w).ord (algebraMap F F' f) = w.ord (algebraMap F F' (g⁻¹ • f)) := by
  have hrw : algebraMap F F' f = g' • (algebraMap F F' (g⁻¹ • f)) := by
    rw [hgg' (g⁻¹ • f), smul_inv_smul]
  rw [hrw]
  exact ord_smul g' w _

end


flt_end_scopes

/- Public statement copied from Theorems/Thm_AlgebraicCurve_SemilinearAut_ord_algebraMap_smul.lean. -/
@[expose] public section

open AlgebraicCurve AlgebraicCurve.SemilinearAut
theorem AlgebraicCurve.SemilinearAut.ord_algebraMap_smul {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} (hgg' : IntertwinesAlong (algebraMap F F') g g') (w : Place K F') (f : F) : (g' • w).ord (algebraMap F F' f) = w.ord (algebraMap F F' (g⁻¹ • f)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_SemilinearAut_ord_algebraMap_smul.solution

