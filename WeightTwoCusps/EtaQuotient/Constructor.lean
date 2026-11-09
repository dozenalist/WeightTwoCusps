module

public import WeightTwoCusps.EtaQuotient.Multiplier.RestrictedMultiplier

/-!
# Modular forms from finite eta-quotient arithmetic

The unrestricted Newman transformation theorem and the analytic cusp bounds
construct a genuine modular form from the classical finite arithmetic data.
Odd and negative divisor exponents are allowed. The weight is inferred from
the proof of `NewmanLigozatConditions` or the expected type, without rounding
a half-integer. Omitted proof arguments are checked by `decide +kernel`.
-/

@[expose] public section

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace WeightTwoCusps

open EtaQuotient

/-- An eta quotient as a modular form on `Γ₀(N)`, from the finite classical
arithmetic conditions. The default discharger `decide +kernel` checks omitted
proofs for concrete inputs. Explicit proofs, including proofs using `norm_num`,
can also be supplied. -/
def etaQuotientMF (N : ℕ) (r : Fin N → ℤ) {k : ℤ}
    (h : NewmanLigozatConditions N r k := by decide +kernel) :
    ModularForm (CongruenceSubgroup.Gamma0 N) k where
  toFun := etaQuotient N r
  slash_action_eq' := by
    intro γ hγ
    obtain ⟨γ, hγ, rfl⟩ := hγ
    exact slash_Gamma0_of_newman_trivialCharacter h.toNewmanConditions h.trivial_character γ hγ
  holo' := holo N r
  bdd_at_cusps' := bounded_at_cusps_of_holomorphicAtCusps h.level_pos h.weight h.holomorphic_cusps

@[simp] theorem etaQuotientMF_coe (N : ℕ) (r : Fin N → ℤ) {k : ℤ}
    (h : NewmanLigozatConditions N r k) :
    (etaQuotientMF N r h : ℍ → ℂ) = etaQuotient N r := rfl

@[simp] theorem etaQuotientMF_apply (N : ℕ) (r : Fin N → ℤ) {k : ℤ}
    (h : NewmanLigozatConditions N r k) (z : ℍ) :
    etaQuotientMF N r h z = etaQuotient N r z := rfl

/-- The strict cusp inequalities construct a cusp form with the same eta
quotient as its underlying function. Both proof arguments default to
`decide +kernel` for concrete inputs. -/
def etaQuotientCuspForm (N : ℕ) (r : Fin N → ℤ) {k : ℤ}
    (h : NewmanLigozatConditions N r k := by decide +kernel)
    (hc : VanishingAtCusps N r := by decide +kernel) :
    CuspForm (CongruenceSubgroup.Gamma0 N) k where
  toSlashInvariantForm := (etaQuotientMF N r h).toSlashInvariantForm
  holo' := (etaQuotientMF N r h).holo'
  zero_at_cusps' := zero_at_cusps_of_vanishingAtCusps h.level_pos h.weight hc

@[simp] theorem etaQuotientCuspForm_coe (N : ℕ) (r : Fin N → ℤ) {k : ℤ}
    (h : NewmanLigozatConditions N r k) (hc : VanishingAtCusps N r) :
    (etaQuotientCuspForm N r h hc : ℍ → ℂ) = etaQuotient N r := rfl

@[simp] theorem etaQuotientCuspForm_apply (N : ℕ) (r : Fin N → ℤ) {k : ℤ}
    (h : NewmanLigozatConditions N r k) (hc : VanishingAtCusps N r) (z : ℍ) :
    etaQuotientCuspForm N r h hc z = etaQuotient N r z := rfl

namespace EtaQuotient

/-- The full sufficient Newman–Ligozat criterion, with no parity restriction
on individual divisor exponents. -/
theorem exists_modularForm_of_newmanLigozat {N : ℕ} {r : Fin N → ℤ} {k : ℤ}
    (h : NewmanLigozatConditions N r k) :
    ∃ f : ModularForm (CongruenceSubgroup.Gamma0 N) k,
      (f : ℍ → ℂ) = etaQuotient N r :=
  ⟨etaQuotientMF N r h, rfl⟩

theorem exists_cuspForm_of_newmanLigozat {N : ℕ} {r : Fin N → ℤ} {k : ℤ}
    (h : NewmanLigozatConditions N r k) (hc : VanishingAtCusps N r) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) k,
      (f : ℍ → ℂ) = etaQuotient N r :=
  ⟨etaQuotientCuspForm N r h hc, rfl⟩

end EtaQuotient
end WeightTwoCusps
