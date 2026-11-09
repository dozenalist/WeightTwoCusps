/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache 2.0 license.
Copied from anthropics/fermats-last-theorem, revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_AlgebraicCurve_RiemannRochRows.lean.
Adapted for this project: local imports, modules, unused code, and shared proofs.
See Dimension/FLT/LICENSE, NOTICE, and ATTRIBUTION_UPSTREAM.md.
-/
module

public import Dimension.FLT.MathlibImports
public import Dimension.FLT.Definitions.Def_AlgebraicCurve_AdelicIndex
public import Dimension.FLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
public import Dimension.FLT.Definitions.Def_AlgebraicCurve_IsCurveOver

@[expose] public section

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def RiemannInequality : Prop :=
  ∀ [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)],
    ∀ D : Divisor K F, Divisor.degree D + 1 - (genus K F : ℤ) ≤ (ell D : ℤ)

def RiemannIndexFormula : Prop :=
  ∀ [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)],
    ∀ D : Divisor K F,
      (indexOfSpecialty D : ℤ) = (ell D : ℤ) - (Divisor.degree D + 1 - (genus K F : ℤ))

def WeilDualityAdelic : Prop :=
  ∀ [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : Place K F, v.DCoordGenerates],
    ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0) (D : Divisor K F),
      (indexOfSpecialty D : ℤ) = (ell (canonicalDivisorOf hω - D) : ℤ)

def WeilDuality : Prop :=
  ∀ [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : Place K F, v.DCoordGenerates],
    ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0) (D : Divisor K F),
      (ell D : ℤ) - (Divisor.degree D + 1 - (genus K F : ℤ))
        = (ell (canonicalDivisorOf hω - D) : ℤ)

def WeilOmegaEllAgrees : Prop :=
  ∀ [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : Place K F, v.DCoordGenerates],
    ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0) (D : Divisor K F),
      (Module.finrank K ↥(omegaSpace D) : ℤ) = (ell (canonicalDivisorOf hω - D) : ℤ)

def FunctionFieldRiemannRoch : Prop :=
  ∀ [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : Place K F, v.DCoordGenerates],
    ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0) (D : Divisor K F),
      (ell D : ℤ) - (ell (canonicalDivisorOf hω - D) : ℤ)
        = Divisor.degree D + 1 - (genus K F : ℤ)

theorem functionFieldRiemannRoch_of_riemann_and_duality
    (hWD : WeilDuality K F) : FunctionFieldRiemannRoch K F := by
  intro _ _ _ ω hω D
  linarith [hWD hω D]

theorem weilDuality_of_riemannIndex_of_adelic
    (hRI : RiemannIndexFormula K F) (hWD : WeilDualityAdelic K F) :
    WeilDuality K F := by
  intro _ _ _ ω hω D
  have h1 := hRI D
  have h2 := hWD hω D
  linarith

end AlgebraicCurve

end
