module

public import WeightTwoCusps.EtaQuotient.Multiplier.HalfWeight
public import WeightTwoCusps.EtaQuotient.Multiplier.JacobiSymbol
public import WeightTwoCusps.EtaQuotient.Multiplier.MultiplierExponent
public import WeightTwoCusps.EtaQuotient.Multiplier.JacobiProduct
public import WeightTwoCusps.EtaQuotient.Multiplier.CharacterDescent
public import WeightTwoCusps.EtaQuotient.Multiplier.HalfWeightFormula

/-!
# Restricted eta multiplier calculations

The subgroup with both off-diagonal entries divisible by 24 has a particularly
simple arithmetic multiplier. These calculations isolate the finite-product
step in Newman's sufficiency theorem.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Complex UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace WeightTwoCusps.EtaQuotient

private theorem odd_lowerRight_of_even_lowerLeft (γ : SL(2, ℤ))
    (hc : Even (γ 1 0)) : Odd (γ 1 1) := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using γ.det_coe
  rcases Int.even_or_odd (γ 1 1) with hd | hd
  · have he : Even (1 : ℤ) := hdet ▸ ((hd.mul_left _).sub (hc.mul_left _))
    norm_num at he
  · exact hd

private theorem mem_Gamma0_four_of_twentyFour (γ : SL(2, ℤ))
    (hc : (24 : ℤ) ∣ γ 1 0) : γ ∈ CongruenceSubgroup.Gamma0 4 := by
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr
    (dvd_trans (by norm_num : (4 : ℤ) ∣ 24) hc)

/-- Multiplicativity with a positive natural first factor also permits a zero
second factor. This handles upper triangular matrices uniformly. -/
theorem extendedJacobi_mul_natCast (m : ℕ) (hm : 0 < m) (a d : ℤ) :
    extendedJacobi ((m : ℤ) * a) d = extendedJacobi m d * extendedJacobi a d := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hsign : ((m : ℤ) * a < 0) ↔ a < 0 := by
    constructor
    · intro h
      by_contra ha
      have hp : 0 ≤ (m : ℤ) * a := mul_nonneg hm'.le (by omega)
      omega
    · exact mul_neg_of_pos_of_neg hm'
  simp only [extendedJacobi, jacobiSym.mul_left, hsign,
    show ¬(m : ℤ) < 0 from by omega, and_false, ↓reduceIte]
  split_ifs <;> ring

/-- Dividing the numerator by a positive divisor multiplies the Jacobi factor
by the symbol of that divisor, when the arguments are coprime. -/
theorem extendedJacobi_div_natCast (m : ℕ) (hm : 0 < m) (c d : ℤ)
    (hmc : (m : ℤ) ∣ c) (hcop : Int.gcd (m : ℤ) d = 1) :
    extendedJacobi (c / m) d = extendedJacobi m d * extendedJacobi c d := by
  have heq : (m : ℤ) * (c / m) = c := Int.mul_ediv_cancel' hmc
  have he := extendedJacobi_mul_natCast m hm (c / m) d
  rw [heq] at he
  have hs := extendedJacobi.sq_eq_one hcop
  calc
    _ = extendedJacobi m d ^ 2 * extendedJacobi (c / m) d := by rw [hs, one_mul]
    _ = extendedJacobi m d *
        (extendedJacobi m d * extendedJacobi (c / m) d) := by ring
    _ = _ := by rw [← he]

section ArithmeticFormula

variable (hformula : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 4 →
  halfMultiplier γ = (extendedJacobi (γ 1 0) (γ 1 1) : ℂ) *
    translationCharacter (matrixMultiplierExponent γ))

include hformula

/-- The restricted version of Savitt's arithmetic multiplier formula. -/
theorem halfMultiplier_restricted_eq (γ : SL(2, ℤ))
    (hb : (24 : ℤ) ∣ γ 0 1) (hc : (24 : ℤ) ∣ γ 1 0) :
    halfMultiplier γ = (extendedJacobi (γ 1 0) (γ 1 1) : ℂ) *
      translationCharacter (3 * (γ 1 1 - 1) : ℤ) := by
  rw [hformula γ (mem_Gamma0_four_of_twentyFour γ hc)]
  congr 1
  apply (translationCharacter_intCast_eq_iff _ _).mpr
  exact arithmeticMultiplierExponent_restricted_modEq _ _ _ _ hb hc

/-- On the restricted subgroup the half-weight multiplier is a fourth root
of unity. Even integral weights therefore kill its common factor. -/
theorem halfMultiplier_restricted_pow_four (γ : SL(2, ℤ))
    (hb : (24 : ℤ) ∣ γ 0 1) (hc : (24 : ℤ) ∣ γ 1 0) :
    halfMultiplier γ ^ 4 = 1 := by
  have hd : Odd (γ 1 1) := odd_lowerRight_of_even_lowerLeft γ
    (even_iff_two_dvd.mpr (dvd_trans (by norm_num : (2 : ℤ) ∣ 24) hc))
  rw [halfMultiplier_restricted_eq hformula γ hb hc, mul_pow]
  have hj : (extendedJacobi (γ 1 0) (γ 1 1) : ℂ) ^ 4 = 1 := by
    have h := extendedJacobi_matrix_sq γ
    have hcplx : (extendedJacobi (γ 1 0) (γ 1 1) : ℂ) ^ 2 = 1 := by exact_mod_cast h
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hcplx, one_pow]
  rw [hj, one_mul, ← AddChar.map_nsmul_eq_pow]
  apply (translationCharacter_eq_one_iff _).mpr
  change (4 : ℤ) • ((3 * (γ 1 1 - 1) : ℤ) : ZMod 24) = 0
  rw [zsmul_eq_mul]
  have hdiv : (24 : ℤ) ∣ 4 * (3 * (γ 1 1 - 1)) := by
    obtain ⟨t, ht⟩ := hd
    exact ⟨t, by omega⟩
  have hcst := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 24).mpr hdiv
  simpa only [Int.cast_mul, Int.cast_ofNat] using hcst

omit hformula in
private theorem quotient_twentyFour_dvd {N m : ℕ} (hm : m ∈ N.divisors)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 (24 * N)) :
    (24 : ℤ) ∣ γ 1 0 / m := by
  have hmN : (m : ℤ) ∣ (N : ℤ) := by exact_mod_cast Nat.dvd_of_mem_divisors hm
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hm).ne'
  have hmc : (m : ℤ) ∣ γ 1 0 := dvd_trans
    (dvd_trans hmN (dvd_mul_left (N : ℤ) 24))
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using Eta.level_dvd_lower_left (24 * N) γ hγ)
  have hdiv : (24 : ℤ) * m ∣ γ 1 0 := dvd_trans (mul_dvd_mul_left 24 hmN)
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using Eta.level_dvd_lower_left (24 * N) γ hγ)
  obtain ⟨t, ht⟩ := hdiv
  refine ⟨t, ?_⟩
  apply mul_left_cancel₀ hm0
  rw [Int.mul_ediv_cancel' hmc, ht]
  ring

/-- The common multiplier separates from the divisor symbol at each
conjugated matrix. Positive divisor numerators handle the case `c = 0`. -/
theorem halfMultiplier_divisorConjugate_restricted {N m : ℕ} (hm : m ∈ N.divisors)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 (24 * N))
    (hb : (24 : ℤ) ∣ γ 0 1) :
    halfMultiplier (divisorConjugate N γ
      (mem_Gamma0_divisor (dvd_mul_left N 24) γ hγ) m hm) =
      (extendedJacobi m (γ 1 1) : ℂ) * halfMultiplier γ := by
  let hγN := mem_Gamma0_divisor (dvd_mul_left N 24) γ hγ
  have hmc : (m : ℤ) ∣ γ 1 0 :=
    Eta.level_dvd_lower_left m γ (mem_Gamma0_divisor (Nat.dvd_of_mem_divisors hm) γ hγN)
  have hcop : Int.gcd (m : ℤ) (γ 1 1) = 1 := Int.isCoprime_iff_gcd_eq_one.mp
    ((Matrix.SpecialLinearGroup.isCoprime_row γ 1).of_isCoprime_of_dvd_left hmc)
  have hc : (24 : ℤ) ∣ γ 1 0 := dvd_trans
    (by exact_mod_cast dvd_mul_right 24 N) (Eta.level_dvd_lower_left (24 * N) γ hγ)
  have hbc : (24 : ℤ) ∣ (divisorConjugate N γ hγN m hm) 0 1 := by
    change (24 : ℤ) ∣ (m : ℤ) * γ 0 1
    exact dvd_mul_of_dvd_right hb _
  have hcc : (24 : ℤ) ∣ (divisorConjugate N γ hγN m hm) 1 0 :=
    quotient_twentyFour_dvd hm γ hγ
  rw [halfMultiplier_restricted_eq hformula _ hbc hcc,
    halfMultiplier_restricted_eq hformula γ hb hc]
  have hdconj : (divisorConjugate N γ hγN m hm) 1 1 = γ 1 1 := rfl
  rw [hdconj]
  change (extendedJacobi (γ 1 0 / m) (γ 1 1) : ℂ) * _ = _
  rw [extendedJacobi_div_natCast m (Nat.pos_of_mem_divisors hm) _ _ hmc hcop,
    Int.cast_mul]
  ring

omit hformula in
private theorem prod_const_zpow {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (a : ℂ) (ha : a ≠ 0) : (∏ i ∈ s, a ^ f i) = a ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, zpow_add₀ ha]

/-- The restricted eta-quotient multiplier is the product of the divisor
symbols once the weight is even. -/
theorem slashMultiplier_restricted_eq_prod {N : ℕ} {r : Fin N → ℤ} {k : ℤ}
    (hk : HasWeight N r k) (heven : Even k)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 (24 * N))
    (hb : (24 : ℤ) ∣ γ 0 1) :
    slashMultiplier N r k γ =
      ∏ m ∈ N.divisors, (extendedJacobi m (γ 1 1) : ℂ) ^ exponent r m := by
  let hγN := mem_Gamma0_divisor (dvd_mul_left N 24) γ hγ
  rw [slashMultiplier_eq_prod_halfMultiplier hk γ hγN]
  have hfactor (m : {m // m ∈ N.divisors}) :=
    halfMultiplier_divisorConjugate_restricted hformula m.property γ hγ hb
  simp_rw [hfactor, mul_zpow]
  rw [Finset.prod_mul_distrib,
    prod_const_zpow _ _ _ (halfMultiplier_ne_zero γ)]
  simp only [Finset.sum_attach]
  change _ * halfMultiplier γ ^ exponentSum N r = _
  have hc : (24 : ℤ) ∣ γ 1 0 := dvd_trans
    (by exact_mod_cast dvd_mul_right 24 N) (Eta.level_dvd_lower_left (24 * N) γ hγ)
  obtain ⟨t, ht⟩ := heven
  have hweight : exponentSum N r = 4 * t := by rw [hk, ht]; ring
  rw [hweight, zpow_mul, zpow_ofNat, halfMultiplier_restricted_pow_four hformula γ hb hc,
    one_zpow, mul_one]
  exact Finset.prod_attach N.divisors
    (fun m ↦ (extendedJacobi m (γ 1 1) : ℂ) ^ exponent r m)

/-- The rational-square condition kills the restricted character for every
signed exponent vector, without a parity condition on individual entries. -/
theorem slash_restricted_of_isSquare {N : ℕ} {r : Fin N → ℤ} {k : ℤ}
    (hk : HasWeight N r k) (heven : Even k) (hs : IsSquare (characterProduct N r))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 (24 * N))
    (hb : (24 : ℤ) ∣ γ 0 1) : etaQuotient N r ∣[k] γ = etaQuotient N r := by
  let hγN := mem_Gamma0_divisor (dvd_mul_left N 24) γ hγ
  have hcop : Int.gcd (N : ℤ) (γ 1 1) = 1 := Int.isCoprime_iff_gcd_eq_one.mp
    ((Matrix.SpecialLinearGroup.isCoprime_row γ 1).of_isCoprime_of_dvd_left
      (Eta.level_dvd_lower_left N γ hγN))
  rw [slash_eq_multiplier_smul hk γ hγN,
    slashMultiplier_restricted_eq_prod hformula hk heven γ hγ hb,
    prod_extendedJacobi_zpow_eq_one_of_isSquare N r (γ 1 1) hcop hs, one_smul]

/-- The full trivial-character Newman transformation law, reduced to the
arithmetic half-multiplier identity on `Γ₀(4)`. -/
theorem slash_Gamma0_of_newman_trivialCharacter_of_formula {N : ℕ} {r : Fin N → ℤ} {k : ℤ}
    (h : NewmanConditions N r k) (ht : TrivialCharacter N r k)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    etaQuotient N r ∣[k] γ = etaQuotient N r := by
  apply slash_Gamma0_of_translations_of_restricted N 24 h.level_pos (by norm_num)
    ((slash_T_eq_self_iff N r k).mpr h.infinity_congruence)
    ((slash_lower_eq_self_iff h.weight).mpr h.zero_congruence) ?_ γ hγ
  intro δ hδ hb
  exact slash_restricted_of_isSquare hformula h.weight ht.1 ht.2 δ hδ hb

end ArithmeticFormula

/-- Newman's transformation theorem with trivial character, for arbitrary
signed exponents at every positive level. -/
theorem slash_Gamma0_of_newman_trivialCharacter {N : ℕ} {r : Fin N → ℤ} {k : ℤ}
    (h : NewmanConditions N r k) (ht : TrivialCharacter N r k)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    etaQuotient N r ∣[k] γ = etaQuotient N r :=
  slash_Gamma0_of_newman_trivialCharacter_of_formula halfMultiplier_eq_extendedJacobi h ht γ hγ

end WeightTwoCusps.EtaQuotient
