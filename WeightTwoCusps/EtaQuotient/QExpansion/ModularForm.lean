module

public import WeightTwoCusps.EtaQuotient.Constructor
public import WeightTwoCusps.EtaQuotient.QExpansion.Computable
public import WeightTwoCusps.QExpansion

/-! # Coefficients of the bundled eta-quotient modular forms -/

@[expose] public section

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace WeightTwoCusps

open EtaQuotient

@[simp] theorem etaQuotientMF_qExpansion (N : ℕ) (r : Fin N → ℤ) {k : ℤ}
    (h : NewmanLigozatConditions N r k) :
    qExpansion 1 (etaQuotientMF N r h) = qExpansion 1 (etaQuotient N r) := rfl

@[simp] theorem etaQuotientCuspForm_qExpansion (N : ℕ) (r : Fin N → ℤ) {k : ℤ}
    (h : NewmanLigozatConditions N r k) (hc : VanishingAtCusps N r) :
    qExpansion 1 (etaQuotientCuspForm N r h hc) = qExpansion 1 (etaQuotient N r) := rfl

@[simp] theorem etaQuotientMF_first_coeffs (m N : ℕ) (r : Fin N → ℤ) {k : ℤ}
    (h : NewmanLigozatConditions N r k) :
    first_coeffs m (etaQuotientMF N r h) = first_coeffs m (etaQuotient N r) := rfl

@[simp] theorem etaQuotientCuspForm_first_coeffs (m N : ℕ) (r : Fin N → ℤ) {k : ℤ}
    (h : NewmanLigozatConditions N r k) (hc : VanishingAtCusps N r) :
    first_coeffs m (etaQuotientCuspForm N r h hc) = first_coeffs m (etaQuotient N r) := rfl

/-- The bundled modular form has the same computable integer coefficients. -/
theorem etaQuotientMF_qExpansion_coeff (N : ℕ) (r : Fin N → ℤ) {k : ℤ}
    (h : NewmanLigozatConditions N r k) (n : ℕ) :
    (qExpansion 1 (etaQuotientMF N r h)).coeff n = (coefficient N r n : ℂ) :=
  qExpansion_coeff_eq_coefficient h.infinity_congruence
    (infinitySum_nonneg h.level_pos h.holomorphic_cusps) n

/-- The bundled cusp form has the same computable integer coefficients. -/
theorem etaQuotientCuspForm_qExpansion_coeff (N : ℕ) (r : Fin N → ℤ) {k : ℤ}
    (h : NewmanLigozatConditions N r k) (hc : VanishingAtCusps N r) (n : ℕ) :
    (qExpansion 1 (etaQuotientCuspForm N r h hc)).coeff n = (coefficient N r n : ℂ) :=
  etaQuotientMF_qExpansion_coeff N r h n

theorem etaQuotientMF_qExpansion_order (N : ℕ) (r : Fin N → ℤ) {k : ℤ}
    (h : NewmanLigozatConditions N r k) :
    (qExpansion 1 (etaQuotientMF N r h)).order = infinityOrder N r :=
  qExpansion_order_of_congruence h.infinity_congruence
    (infinitySum_nonneg h.level_pos h.holomorphic_cusps)

theorem etaQuotientCuspForm_qExpansion_order (N : ℕ) (r : Fin N → ℤ) {k : ℤ}
    (h : NewmanLigozatConditions N r k) (hc : VanishingAtCusps N r) :
    (qExpansion 1 (etaQuotientCuspForm N r h hc)).order = infinityOrder N r :=
  etaQuotientMF_qExpansion_order N r h

theorem etaQuotientMF_qExpansion_coeff_leading (N : ℕ) (r : Fin N → ℤ) {k : ℤ}
    (h : NewmanLigozatConditions N r k) :
    (qExpansion 1 (etaQuotientMF N r h)).coeff (infinityOrder N r) = 1 :=
  qExpansion_coeff_leading (infinitySum_eq_twentyFour_mul_order h.infinity_congruence
    (infinitySum_nonneg h.level_pos h.holomorphic_cusps))

/-- A cusp-form constructor has strictly positive infinity order. -/
theorem etaQuotientCuspForm_infinityOrder_pos (N : ℕ) (r : Fin N → ℤ) {k : ℤ}
    (h : NewmanLigozatConditions N r k) (hc : VanishingAtCusps N r) :
    0 < infinityOrder N r := by
  have hp : 0 < infinitySum N r := by
    have hp := hc N (Nat.mem_divisors_self N h.level_pos.ne')
    rw [cuspSum_level] at hp
    exact_mod_cast hp
  have hv := infinitySum_eq_twentyFour_mul_order h.infinity_congruence hp.le
  change 0 < (infinitySum N r / 24).toNat
  omega

@[simp] theorem etaQuotientCuspForm_qExpansion_coeff_zero (N : ℕ) (r : Fin N → ℤ) {k : ℤ}
    (h : NewmanLigozatConditions N r k) (hc : VanishingAtCusps N r) :
    (qExpansion 1 (etaQuotientCuspForm N r h hc)).coeff 0 = 0 := by
  exact qExpansion_coeff_eq_zero_of_lt
    (infinitySum_eq_twentyFour_mul_order h.infinity_congruence
      (infinitySum_nonneg h.level_pos h.holomorphic_cusps))
    (etaQuotientCuspForm_infinityOrder_pos N r h hc)

end WeightTwoCusps
