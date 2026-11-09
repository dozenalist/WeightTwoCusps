/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache 2.0 license.
Copied from anthropics/fermats-last-theorem, revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_AlgebraicCurve_CanonicalDivisor.lean.
Adapted for this project: local imports, modules, unused code, and shared proofs.
See Dimension/FLT/LICENSE, NOTICE, and ATTRIBUTION_UPSTREAM.md.
-/
module

public import Dimension.FLT.MathlibImports
public import Dimension.FLT.Definitions.Def_ModularCurve_CanonicalDivisor

@[expose] public section

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

class HasCanonicalDivisor : Prop where
  exists_divisor : ∀ ω : Ω[F⁄K], ω ≠ 0 → ∃ D : Divisor K F,
    ∀ v : Place K F, D v = v.ordDifferential ω

def canonicalDivisorOf [HasCanonicalDivisor (K := K) (F := F)]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) : Divisor K F :=
  (HasCanonicalDivisor.exists_divisor ω hω).choose

theorem canonicalDivisorOf_apply [HasCanonicalDivisor (K := K) (F := F)]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : Place K F) :
    canonicalDivisorOf hω v = v.ordDifferential ω :=
  (HasCanonicalDivisor.exists_divisor ω hω).choose_spec v

def canonicalClass (K F : Type*) [Field K] [Field F] [Algebra K F]
    [HasCanonicalDivisor (K := K) (F := F)] : Pic K F :=
  letI := Classical.propDecidable
  if h : ∃ ω : Ω[F⁄K], ω ≠ 0 then QuotientAddGroup.mk (canonicalDivisorOf h.choose_spec)
  else 0

def genus (K F : Type*) [Field K] [Field F] [Algebra K F]
    [HasCanonicalDivisor (K := K) (F := F)] : ℕ :=
  letI := Classical.propDecidable
  if h : ∃ ω : Ω[F⁄K], ω ≠ 0
  then (Divisor.degree (canonicalDivisorOf h.choose_spec) + 2).toNat / 2
  else 0

end AlgebraicCurve

end
