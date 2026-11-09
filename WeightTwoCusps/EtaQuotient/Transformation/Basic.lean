module

public import WeightTwoCusps.EtaQuotient.Basic
public import WeightTwoCusps.Eta.Congruence
public import WeightTwoCusps.Eta.Multiplier

/-!
# The eta-square character of a general eta quotient

The repository's twelfth-root eta-square character gives an exact
transformation formula for the square of every eta quotient. This avoids any
restriction on the parity or sign of its individual exponents. For even
exponents the same formula determines the original quotient itself.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Complex
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm

namespace WeightTwoCusps.EtaQuotient

/-- A matrix in `Γ₀(N)` is in `Γ₀(m)` whenever `m ∣ N`. -/
theorem mem_Gamma0_divisor {N m : ℕ} (hm : m ∣ N) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) : γ ∈ CongruenceSubgroup.Gamma0 m := by
  apply CongruenceSubgroup.Gamma0_mem.mpr
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mpr
  exact (by exact_mod_cast hm : (m : ℤ) ∣ N).trans (Eta.level_dvd_lower_left N γ hγ)

/-- The conjugated integral matrix belonging to the divisor `m`. -/
def divisorConjugate (N : ℕ) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    (m : ℕ) (hm : m ∈ N.divisors) : SL(2, ℤ) :=
  Eta.levelConjugate m γ (mem_Gamma0_divisor (Nat.dvd_of_mem_divisors hm) γ hγ)

/-- The exponent of the multiplier of the square of the quotient, modulo twelve. -/
def squareMultiplierExponent (N : ℕ) (r : Fin N → ℤ) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) : ZMod 12 :=
  ∑ m ∈ N.divisors.attach,
    (exponent r m : ZMod 12) * Eta.etaExponent (divisorConjugate N γ hγ m m.property)

theorem eta_sq_dilate_transform {N m : ℕ} (hm : m ∈ N.divisors)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (z : ℍ) :
    ModularForm.eta ((m : ℂ) * (γ • z : ℍ)) ^ 2 =
      Eta.etaMultiplier (Eta.etaExponent (divisorConjugate N γ hγ m hm)) *
        denom γ z * ModularForm.eta ((m : ℂ) * (z : ℂ)) ^ 2 := by
  have hpos := Nat.pos_of_mem_divisors hm
  have hmem := mem_Gamma0_divisor (Nat.dvd_of_mem_divisors hm) γ hγ
  change Eta.etaSq (Eta.dilate m (by exact_mod_cast hpos) (γ • z)) = _
  rw [Eta.dilate_smul m hpos γ hmem, Eta.etaSq_modular_transform,
    Eta.denom_levelConjugate m hpos γ hmem z]
  rfl

private theorem character_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 12) :
    Eta.etaMultiplier (∑ i ∈ s, f i) = ∏ i ∈ s, Eta.etaMultiplier (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, AddChar.map_add_eq_mul, ih]

private theorem zpow_two_comm (a : ℂ) (n : ℤ) : (a ^ n) ^ 2 = (a ^ 2) ^ n := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm n, zpow_mul, zpow_natCast]

private theorem prod_const_zpow {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (a : ℂ) (ha : a ≠ 0) : (∏ i ∈ s, a ^ f i) = a ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, zpow_add₀ ha]

/-- Exact transformation of the square of an arbitrary eta quotient. -/
theorem square_transform (N : ℕ) (r : Fin N → ℤ) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (z : ℍ) :
    etaQuotient N r (γ • z) ^ 2 =
      Eta.etaMultiplier (squareMultiplierExponent N r γ hγ) *
        denom γ z ^ exponentSum N r * etaQuotient N r z ^ 2 := by
  simp only [etaQuotient, ← Finset.prod_pow, zpow_two_comm]
  rw [← Finset.prod_attach N.divisors]
  have hfactor (m : {m // m ∈ N.divisors}) := eta_sq_dilate_transform m.property γ hγ z
  simp_rw [hfactor, mul_zpow]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  rw [squareMultiplierExponent, character_sum]
  have hchar : (∏ m ∈ N.divisors.attach,
      Eta.etaMultiplier (Eta.etaExponent (divisorConjugate N γ hγ m m.property)) ^
        exponent r m) = ∏ m ∈ N.divisors.attach,
          Eta.etaMultiplier ((exponent r m : ZMod 12) *
            Eta.etaExponent (divisorConjugate N γ hγ m m.property)) := by
    apply Finset.prod_congr rfl
    intro m hm
    rw [← AddChar.map_zsmul_eq_zpow, zsmul_eq_mul]
  rw [hchar]
  rw [prod_const_zpow _ _ _ (denom_ne_zero γ z)]
  simp only [Finset.sum_attach, exponentSum]
  congr 1
  exact Finset.prod_attach N.divisors
    (fun m ↦ (ModularForm.eta ((m : ℂ) * (z : ℂ)) ^ 2) ^ exponent r m)

/-- A vanishing character exponent is exactly slash invariance of the square. -/
theorem square_slash_eq_self_iff (N : ℕ) (r : Fin N → ℤ) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    (fun z ↦ etaQuotient N r z ^ 2) ∣[exponentSum N r] γ =
      (fun z ↦ etaQuotient N r z ^ 2) ↔ squareMultiplierExponent N r γ hγ = 0 := by
  have heq : (fun z ↦ etaQuotient N r z ^ 2) ∣[exponentSum N r] γ =
      Eta.etaMultiplier (squareMultiplierExponent N r γ hγ) •
        (fun z ↦ etaQuotient N r z ^ 2) := by
    ext z
    rw [ModularForm.SL_slash_apply, square_transform N r γ hγ z]
    simp only [Pi.smul_apply, smul_eq_mul, zpow_neg]
    field_simp [denom_ne_zero γ z]
  rw [heq]
  constructor
  · intro h
    have hval := congrFun h UpperHalfPlane.I
    simp only [Pi.smul_apply, smul_eq_mul] at hval
    have hx := (mul_eq_right₀ (pow_ne_zero 2 (ne_zero N r UpperHalfPlane.I))).mp hval
    apply ZMod.injective_stdAddChar
    simpa [Eta.etaMultiplier] using hx
  · intro h
    rw [h, AddChar.map_zero_eq_one, one_smul]

end WeightTwoCusps.EtaQuotient
