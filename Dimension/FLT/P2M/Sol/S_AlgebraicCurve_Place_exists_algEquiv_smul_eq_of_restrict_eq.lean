/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache 2.0 license.
Copied from anthropics/fermats-last-theorem, revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_AlgebraicCurve_Place_exists_algEquiv_smul_eq_of_restrict_eq.lean.
Adapted for this project: local imports, modules, unused code, and shared proofs.
See Dimension/FLT/LICENSE, NOTICE, and ATTRIBUTION_UPSTREAM.md.
-/
module

public import Dimension.FLT.Definitions.Def_AlgebraicCurve_PlacesOverDVR
public import Dimension.FLT.Definitions.Def_AlgebraicCurve_BaseChangeGalois
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Invariant.Basic
public import Dimension.FLT.P2M.Util

public import Dimension.FLT.EndScopes
public import Dimension.FLT.Definitions.Def_AlgebraicCurve_DivisorPushPull
public import Mathlib.FieldTheory.Galois.Basic

@[expose] public section
namespace P2MW.S_AlgebraicCurve_Place_exists_algEquiv_smul_eq_of_restrict_eq

set_option autoImplicit false
noncomputable section
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_exists_algEquiv_smul_eq_of_restrict_eq.AlgebraicCurve IsDedekindDomain"
open scoped Pointwise

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext SemilinearAut SemilinearAut.inv_smul_def SemilinearAut.ofAlgAut SemilinearAut.toRingAut_ofAlgAut SemilinearAut.smul_toValuationSubring SemilinearAut.ord_smul"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "integralClosureAt fiberCenter mem_fiberCenter_iff_ord_pos fiberCenter_liesOver eq_of_fiberCenter_eq restrict restrict_toValuationSubring ext ord smul_toValuationSubring ord_smul toValuationSubring"
p2m_open "AlgebraicCurve.Place"

variable {K F' M : Type*} [Field K] [Field F'] [Field M] [Algebra K F'] [Algebra K M]
  [Algebra F' M] [IsScalarTower K F' M]

section Restrict
variable [Algebra.IsIntegral F' M]

private theorem restrict_ofAlgAut_restrictScalars_smul (σ : M ≃ₐ[F'] M) (W : Place K M) :
    (SemilinearAut.ofAlgAut (σ.restrictScalars K) • W).restrict F' = W.restrict F' := by
  refine Place.ext ?_
  ext x
  rw [restrict_toValuationSubring, restrict_toValuationSubring, ValuationSubring.mem_comap,
    ValuationSubring.mem_comap, SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, SemilinearAut.inv_smul_def,
    SemilinearAut.toRingAut_ofAlgAut]
  change ((σ.restrictScalars K : M ≃+* M).symm (algebraMap F' M x)) ∈ _ ↔ _
  have : ((σ.restrictScalars K : M ≃+* M).symm (algebraMap F' M x)) = algebraMap F' M x := by
    rw [RingEquiv.symm_apply_eq]
    exact (σ.commutes x).symm
  rw [this]

private theorem ord_smul_eq (g : SemilinearAut K M) (W : Place K M) (y : M) :
    (g • W).ord y = W.ord (g⁻¹ • y) := by
  conv_lhs => rw [← smul_inv_smul g y]
  exact SemilinearAut.ord_smul g W (g⁻¹ • y)

end Restrict

end Place
end AlgebraicCurve

open _root_.AlgebraicCurve.Place _root_.P2MW.S_AlgebraicCurve_Place_exists_algEquiv_smul_eq_of_restrict_eq.AlgebraicCurve.Place in
theorem solution {K F' M : Type*} [Field K] [Field F'] [Field M]
    [Algebra K F'] [Algebra K M] [Algebra F' M] [IsScalarTower K F' M]
    [FiniteDimensional F' M] [IsGalois F' M] (W W' : Place K M)
    (h : W'.restrict F' = W.restrict F') :
    ∃ σ : M ≃ₐ[F'] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W = W' := by
  set w : Place K F' := W.restrict F'
  have hW : W.restrict F' = w := rfl
  letI := IsIntegralClosure.MulSemiringAction w.toValuationSubring F' M (integralClosureAt M w)
  haveI : IsGaloisGroup Gal(M/F') w.toValuationSubring (integralClosureAt M w) :=
    IsGaloisGroup.of_isFractionRing Gal(M/F') w.toValuationSubring (integralClosureAt M w) F' M
  haveI hp : (fiberCenter M w hW).asIdeal.IsPrime := (fiberCenter M w hW).isPrime
  haveI hp' : (fiberCenter M w h).asIdeal.IsPrime := (fiberCenter M w h).isPrime
  haveI := fiberCenter_liesOver (F' := M) hW
  haveI := fiberCenter_liesOver (F' := M) h
  obtain ⟨σ, hσ'⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
    (IsLocalRing.maximalIdeal w.toValuationSubring) (fiberCenter M w hW).asIdeal
    (fiberCenter M w h).asIdeal Gal(M/F')
  refine ⟨σ, eq_of_fiberCenter_eq (restrict_ofAlgAut_restrictScalars_smul σ W) h ?_⟩
  refine HeightOneSpectrum.ext (Ideal.ext fun c => ?_)
  rw [← hσ', Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  by_cases hc : c = 0
  · simp [hc]
  have hc' : σ⁻¹ • c ≠ 0 := fun h0 => hc (by simpa using congrArg (σ • ·) h0)
  rw [mem_fiberCenter_iff_ord_pos _ hc, mem_fiberCenter_iff_ord_pos _ hc', ord_smul_eq,
    SemilinearAut.inv_smul_def, SemilinearAut.toRingAut_ofAlgAut]
  have key : algebraMap (integralClosureAt M w) M (σ⁻¹ • c)
      = ((σ.restrictScalars K : M ≃+* M)).symm (algebraMap (integralClosureAt M w) M c) := by
    rw [show σ⁻¹ • c = galRestrict w.toValuationSubring F' M (integralClosureAt M w) σ⁻¹ c
      from rfl, algebraMap_galRestrict_apply, AlgEquiv.aut_inv]
    rfl
  rw [key]

end


flt_end_scopes

/- Public statement copied from Theorems/Thm_AlgebraicCurve_Place_exists_algEquiv_smul_eq_of_restrict_eq.lean. -/
@[expose] public section
p2m_erase_attrs «instance» AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
p2m_erase_attrs «simp» AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

open AlgebraicCurve
theorem AlgebraicCurve.Place.exists_algEquiv_smul_eq_of_restrict_eq {K F' M : Type*} [Field K] [Field F'] [Field M]
    [Algebra K F'] [Algebra K M] [Algebra F' M] [IsScalarTower K F' M]
    [FiniteDimensional F' M] [IsGalois F' M] (W W' : Place K M)
    (h : W'.restrict F' = W.restrict F') :
    ∃ σ : M ≃ₐ[F'] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W = W' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_exists_algEquiv_smul_eq_of_restrict_eq.solution

