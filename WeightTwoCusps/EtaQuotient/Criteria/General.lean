module

public import WeightTwoCusps.EtaQuotient.Criteria.Weight
public import WeightTwoCusps.EtaQuotient.Criteria.EvenExponents
public import WeightTwoCusps.EtaQuotient.Constructor
public import WeightTwoCusps.EtaQuotient.Cusps.Transform

/-!
# The even-exponent Newman–Ligozat criterion at every positive level

The analytic cusp calculation now allows negative exponents at composite
levels. The even-exponent hypothesis is needed only for the transformation
law in this equivalence. Unrestricted sufficiency is proved separately in
`RestrictedMultiplier.lean` and used by `Constructor.lean`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace WeightTwoCusps.EtaQuotient

/-- Every Ligozat inequality is necessary for a genuine modular eta quotient,
without a parity or sign restriction on the exponents. -/
theorem holomorphicAtCusps_of_modularForm {N : ℕ} (hN : 0 < N)
    {r : Fin N → ℤ} {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (hf : (f : ℍ → ℂ) = etaQuotient N r) : HolomorphicAtCusps N r := by
  have : NeZero N := ⟨hN.ne'⟩
  apply (holomorphicAtCusps_iff_slash_isBounded hN (hasWeight_of_modularForm hN f hf)).mpr
  intro γ
  simpa only [hf] using ModularFormClass.bdd_at_infty_slash f γ

/-- Every strict Ligozat inequality is necessary for a genuine cusp eta quotient. -/
theorem vanishingAtCusps_of_cuspForm {N : ℕ} (hN : 0 < N)
    {r : Fin N → ℤ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (hf : (f : ℍ → ℂ) = etaQuotient N r) : VanishingAtCusps N r := by
  have : NeZero N := ⟨hN.ne'⟩
  have hk := hasWeight_of_modularForm hN
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) hf
  apply (vanishingAtCusps_iff_slash_isZero hN hk).mpr
  intro γ
  simpa only [hf] using CuspFormClass.zero_at_infty_slash f γ

/-- Newman–Ligozat at every positive level for arbitrary even divisor exponents.
Negative exponents and composite levels are allowed. The weight is inferred
from modularity in the forward direction. -/
theorem even_newman_ligozat_iff (N : ℕ) (hN : 0 < N) (r : Fin N → ℤ) (k : ℤ)
    (hr : EvenExponents N r) :
    (∃ f : ModularForm (CongruenceSubgroup.Gamma0 N) k,
      (f : ℍ → ℂ) = etaQuotient N r) ↔ NewmanLigozatConditions N r k := by
  constructor
  · rintro ⟨f, hf⟩
    exact {
      toNewmanConditions := newmanConditions_of_modularForm_autoWeight hN f hf
      trivial_character := ⟨even_weight_of_modularForm f hf,
        characterProduct_isSquare_of_even hr⟩
      holomorphic_cusps := holomorphicAtCusps_of_modularForm hN f hf }
  · exact exists_modularForm_of_newmanLigozat

/-- The strict criterion at every positive level for arbitrary even divisor exponents. -/
theorem even_cuspidal_newman_ligozat_iff (N : ℕ) (hN : 0 < N)
    (r : Fin N → ℤ) (k : ℤ) (hr : EvenExponents N r) :
    (∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) k,
      (f : ℍ → ℂ) = etaQuotient N r) ↔
        NewmanLigozatConditions N r k ∧ VanishingAtCusps N r := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨(even_newman_ligozat_iff N hN r k hr).mp
      ⟨(f : ModularForm (CongruenceSubgroup.Gamma0 N) k), hf⟩,
      vanishingAtCusps_of_cuspForm hN f hf⟩
  · rintro ⟨h, hc⟩
    exact exists_cuspForm_of_newmanLigozat h hc

end WeightTwoCusps.EtaQuotient
