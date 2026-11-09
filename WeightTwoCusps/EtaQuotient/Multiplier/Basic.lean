module

public import WeightTwoCusps.EtaQuotient.Cusps.Transform
public import WeightTwoCusps.EtaQuotient.Transformation.NewmanEven
public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# The unsquared character of an integral-weight eta quotient

The square transformation law determines the slash ratio up to sign.
Continuity on the connected upper half-plane shows that the ratio is
constant in the variable. This retains the sign, rather than assuming it
away. The arithmetic evaluation used for unrestricted sufficiency is proved
separately in `HalfWeightFormula.lean` and `RestrictedMultiplier.lean`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Complex UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace WeightTwoCusps.EtaQuotient

/-- The actual, unsquared slash multiplier, evaluated at the basepoint `I`. -/
def slashMultiplier (N : ℕ) (r : Fin N → ℤ) (k : ℤ) (γ : SL(2, ℤ)) : ℂ :=
  (etaQuotient N r ∣[k] γ) UpperHalfPlane.I / etaQuotient N r UpperHalfPlane.I

private theorem slashRatio_sq {N : ℕ} {r : Fin N → ℤ} {k : ℤ}
    (hk : HasWeight N r k) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    (z : ℍ) :
    ((etaQuotient N r ∣[k] γ) z / etaQuotient N r z) ^ 2 =
      Eta.etaMultiplier (squareMultiplierExponent N r γ hγ) := by
  rw [div_pow, ModularForm.SL_slash_apply, mul_pow, square_transform N r γ hγ z]
  rw [show exponentSum N r = k * 2 by rw [hk]; ring, zpow_mul, zpow_ofNat]
  simp only [zpow_neg]
  field_simp [ne_zero N r z, denom_ne_zero γ z]

/-- Connectedness removes dependence on `z` while preserving the unknown sign. -/
theorem slashRatio_eq_multiplier {N : ℕ} {r : Fin N → ℤ} {k : ℤ}
    (hk : HasWeight N r k) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    (z : ℍ) :
    (etaQuotient N r ∣[k] γ) z / etaQuotient N r z = slashMultiplier N r k γ := by
  let f : ℍ → ℂ := fun w ↦ (etaQuotient N r ∣[k] γ) w / etaQuotient N r w
  have hf : Continuous f :=
    ((holo N r).slash k (Matrix.SpecialLinearGroup.mapGL ℝ γ)).continuous.div
      (holo N r).continuous (ne_zero N r)
  have hs (w : ℍ) : f w ^ 2 = f UpperHalfPlane.I ^ 2 :=
    (slashRatio_sq hk γ hγ w).trans (slashRatio_sq hk γ hγ UpperHalfPlane.I).symm
  have hm : Set.MapsTo f Set.univ {f UpperHalfPlane.I, -f UpperHalfPlane.I} := by
    intro w _
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      (sq_eq_sq_iff_eq_or_eq_neg.mp (hs w))
  exact isPreconnected_univ.constant_of_mapsTo (Set.toFinite _).isDiscrete hf.continuousOn hm
    (Set.mem_univ z) (Set.mem_univ UpperHalfPlane.I)

/-- The exact scalar transformation law for arbitrary integral-weight eta quotients. -/
theorem slash_eq_multiplier_smul {N : ℕ} {r : Fin N → ℤ} {k : ℤ}
    (hk : HasWeight N r k) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    etaQuotient N r ∣[k] γ = slashMultiplier N r k γ • etaQuotient N r := by
  ext z
  simpa only [Pi.smul_apply, smul_eq_mul] using
    (div_eq_iff (ne_zero N r z)).mp (slashRatio_eq_multiplier hk γ hγ z)

theorem slashMultiplier_sq {N : ℕ} {r : Fin N → ℤ} {k : ℤ}
    (hk : HasWeight N r k) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    slashMultiplier N r k γ ^ 2 =
      Eta.etaMultiplier (squareMultiplierExponent N r γ hγ) :=
  slashRatio_sq hk γ hγ UpperHalfPlane.I

theorem slashMultiplier_ne_zero (N : ℕ) (r : Fin N → ℤ) (k : ℤ) (γ : SL(2, ℤ)) :
    slashMultiplier N r k γ ≠ 0 := by
  rw [slashMultiplier, ModularForm.SL_slash_apply]
  exact div_ne_zero (mul_ne_zero (ne_zero N r (γ • UpperHalfPlane.I))
    (zpow_ne_zero _ (denom_ne_zero γ UpperHalfPlane.I))) (ne_zero N r UpperHalfPlane.I)

@[simp] theorem slashMultiplier_one (N : ℕ) (r : Fin N → ℤ) (k : ℤ) :
    slashMultiplier N r k 1 = 1 := by
  simp [slashMultiplier, ne_zero]

theorem slashMultiplier_mul {N : ℕ} {r : Fin N → ℤ} {k : ℤ}
    (hk : HasWeight N r k) (γ δ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (hδ : δ ∈ CongruenceSubgroup.Gamma0 N) :
    slashMultiplier N r k (γ * δ) = slashMultiplier N r k γ * slashMultiplier N r k δ := by
  rw [slashMultiplier, SlashAction.slash_mul, slash_eq_multiplier_smul hk γ hγ,
    ModularForm.SL_smul_slash, slash_eq_multiplier_smul hk δ hδ]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp [ne_zero N r UpperHalfPlane.I]

/-- The genuine character on `Γ₀(N)`, before its arithmetic identification. -/
def multiplierCharacter {N : ℕ} {r : Fin N → ℤ} {k : ℤ} (hk : HasWeight N r k) :
    CongruenceSubgroup.Gamma0 N →* ℂˣ where
  toFun γ := Units.mk0 (slashMultiplier N r k γ) (slashMultiplier_ne_zero N r k γ)
  map_one' := Units.ext (slashMultiplier_one N r k)
  map_mul' γ δ := Units.ext (slashMultiplier_mul hk γ δ γ.property δ.property)

/-- The Newman congruences force the remaining multiplier to be a sign.
The arithmetic calculation in `RestrictedMultiplier.lean` determines this
sign when the classical trivial-character condition holds. -/
theorem slashMultiplier_eq_one_or_neg_one {N : ℕ} {r : Fin N → ℤ} {k : ℤ}
    (hk : HasWeight N r k) (hi : (24 : ℤ) ∣ infinitySum N r)
    (hz : (24 : ℤ) ∣ zeroSum N r) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    slashMultiplier N r k γ = 1 ∨ slashMultiplier N r k γ = -1 := by
  have heven : Even (exponentSum N r) := ⟨k, by rw [hk]; ring⟩
  have hi' : (12 : ℤ) ∣ infinitySum N r := dvd_trans (by norm_num) hi
  have hz' : (12 : ℤ) ∣ zeroSum N r := dvd_trans (by norm_num) hz
  have hdouble := double_slash_Gamma0_of_newman N r heven hi' hz' γ hγ
  rw [double_slash_eq_square hk γ] at hdouble
  have hs : slashMultiplier N r k γ ^ 2 = 1 := by
    rw [slashMultiplier, div_pow]
    have he := congrFun hdouble UpperHalfPlane.I
    rw [he, double_apply]
    exact div_self (pow_ne_zero 2 (ne_zero N r UpperHalfPlane.I))
  exact sq_eq_one_iff.mp hs

theorem slashMultiplier_T_eq_one {N : ℕ} {r : Fin N → ℤ} {k : ℤ}
    (hi : (24 : ℤ) ∣ infinitySum N r) : slashMultiplier N r k ModularGroup.T = 1 := by
  rw [slashMultiplier, (slash_T_eq_self_iff N r k).mpr hi]
  exact div_self (ne_zero N r UpperHalfPlane.I)

theorem slashMultiplier_lower_eq_one {N : ℕ} {r : Fin N → ℤ} {k : ℤ}
    (hk : HasWeight N r k) (hz : (24 : ℤ) ∣ zeroSum N r) :
    slashMultiplier N r k (lowerUnipotent N) = 1 := by
  rw [slashMultiplier, (slash_lower_eq_self_iff hk).mpr hz]
  exact div_self (ne_zero N r UpperHalfPlane.I)

end WeightTwoCusps.EtaQuotient
