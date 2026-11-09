module

public import WeightTwoCusps.EtaQuotient.Transformation.NewmanEven
public import WeightTwoCusps.EtaQuotient.Criteria

/-!
# Arithmetic and transformation laws for even divisor exponents

Halving the exponents reduces to the eta-square transformation law. The
general constructors accept actual exponents without this parity restriction.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace WeightTwoCusps.EtaQuotient

/-- Every exponent that occurs in the product is even. -/
def EvenExponents (N : ℕ) (r : Fin N → ℤ) : Prop :=
  ∀ m ∈ N.divisors, Even (exponent r m)
deriving Decidable

/-- Divide each entry by two. Used only with `EvenExponents` below. -/
def half {N : ℕ} (r : Fin N → ℤ) : Fin N → ℤ := fun i ↦ r i / 2

@[simp] theorem exponent_half {N : ℕ} (r : Fin N → ℤ) (m : ℕ) :
    exponent (half r) m = exponent r m / 2 := by
  unfold exponent half
  split <;> simp

theorem exponent_double_half {N : ℕ} {r : Fin N → ℤ} (hr : EvenExponents N r)
    {m : ℕ} (hm : m ∈ N.divisors) : exponent (double (half r)) m = exponent r m := by
  rw [exponent_double, exponent_half]
  obtain ⟨t, ht⟩ := hr m hm
  omega

theorem congr_of_exponent_eq {N : ℕ} {r s : Fin N → ℤ}
    (h : ∀ m ∈ N.divisors, exponent r m = exponent s m) : etaQuotient N r = etaQuotient N s := by
  funext z
  apply Finset.prod_congr rfl
  intro m hm
  rw [h m hm]

theorem exponentSum_congr {N : ℕ} {r s : Fin N → ℤ}
    (h : ∀ m ∈ N.divisors, exponent r m = exponent s m) : exponentSum N r = exponentSum N s := by
  exact Finset.sum_congr rfl h

theorem infinitySum_congr {N : ℕ} {r s : Fin N → ℤ}
    (h : ∀ m ∈ N.divisors, exponent r m = exponent s m) : infinitySum N r = infinitySum N s := by
  apply Finset.sum_congr rfl
  intro m hm
  rw [h m hm]

theorem zeroSum_congr {N : ℕ} {r s : Fin N → ℤ}
    (h : ∀ m ∈ N.divisors, exponent r m = exponent s m) : zeroSum N r = zeroSum N s := by
  apply Finset.sum_congr rfl
  intro m hm
  rw [h m hm]

theorem characterProduct_congr {N : ℕ} {r s : Fin N → ℤ}
    (h : ∀ m ∈ N.divisors, exponent r m = exponent s m) :
    characterProduct N r = characterProduct N s := by
  apply Finset.prod_congr rfl
  intro m hm
  rw [h m hm]

theorem half_weight {N : ℕ} {r : Fin N → ℤ} {k : ℤ} (hr : EvenExponents N r)
    (hk : HasWeight N r k) : exponentSum N (half r) = k := by
  have hs := exponentSum_congr (fun m hm ↦ exponent_double_half hr hm)
  rw [exponentSum_double] at hs
  dsimp [HasWeight] at hk
  omega

theorem characterProduct_isSquare_of_even {N : ℕ} {r : Fin N → ℤ} (hr : EvenExponents N r) :
    IsSquare (characterProduct N r) := by
  rw [← characterProduct_congr (fun m hm ↦ exponent_double_half hr hm)]
  exact characterProduct_double_isSquare N (half r)

/-- The transformation part at every level, stated for the actual even exponent function. -/
theorem slash_Gamma0_of_evenExponents {N : ℕ} {r : Fin N → ℤ} {k : ℤ}
    (hr : EvenExponents N r) (hk : HasWeight N r k) (heven : Even k)
    (hInfty : (24 : ℤ) ∣ infinitySum N r) (hzero : (24 : ℤ) ∣ zeroSum N r)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    etaQuotient N r ∣[k] γ = etaQuotient N r := by
  have hw := half_weight hr hk
  have hi : (12 : ℤ) ∣ infinitySum N (half r) := by
    have hs := infinitySum_congr (fun m hm ↦ exponent_double_half hr hm)
    rw [infinitySum_double] at hs
    obtain ⟨t, ht⟩ := hInfty
    exact ⟨t, by omega⟩
  have hz : (12 : ℤ) ∣ zeroSum N (half r) := by
    have hs := zeroSum_congr (fun m hm ↦ exponent_double_half hr hm)
    rw [zeroSum_double] at hs
    obtain ⟨t, ht⟩ := hzero
    exact ⟨t, by omega⟩
  have hf := congr_of_exponent_eq (fun m hm ↦ exponent_double_half hr hm)
  rw [← hf, ← hw]
  exact double_slash_Gamma0_of_newman N (half r) (hw.symm ▸ heven) hi hz γ hγ

end WeightTwoCusps.EtaQuotient
