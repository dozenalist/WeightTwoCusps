module

public import Dimension.Gamma_0.CuspCoordinates
public import Dimension.Gamma_0.Relation

/-! # The divisor-sum cusp count for `Γ₀(N)` -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

namespace WeightTwoCusps

/-- Compatible unit residues for two divisors lift simultaneously to the level.
The moduli need not be coprime. -/
theorem exists_unit_lift_pair (N d m : ℕ) [NeZero N] (hd : d ∣ N) (hm : m ∣ N)
    (a b : (ZMod N)ˣ)
    (hab : ZMod.castHom (dvd_trans (Nat.gcd_dvd_left d m) hd) (ZMod (d.gcd m))
        (a : ZMod N) =
      ZMod.castHom (dvd_trans (Nat.gcd_dvd_right d m) hm) (ZMod (d.gcd m))
        (b : ZMod N)) :
    ∃ u : (ZMod N)ˣ,
      ZMod.unitsMap hd u = ZMod.unitsMap hd a ∧
      ZMod.unitsMap hm u = ZMod.unitsMap hm b := by
  have hcompat : (a : ZMod N).val ≡ (b : ZMod N).val [MOD d.gcd m] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa only [ZMod.castHom_apply, ZMod.cast_eq_val] using hab
  obtain ⟨k, hk, hl⟩ := Nat.chineseRemainder' hcompat
  have hkd : IsUnit (k : ZMod d) := by
    have heq := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hk
    rw [heq]
    simpa only [ZMod.unitsMap_val, ZMod.cast_eq_val] using (ZMod.unitsMap hd a).isUnit
  have hkm : IsUnit (k : ZMod m) := by
    have heq := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hl
    rw [heq]
    simpa only [ZMod.unitsMap_val, ZMod.cast_eq_val] using (ZMod.unitsMap hm b).isUnit
  have hkl : k.Coprime (d.lcm m) :=
    ((ZMod.isUnit_iff_coprime _ _).mp hkd |>.mul_right
      ((ZMod.isUnit_iff_coprime _ _).mp hkm)).of_dvd_right (Nat.lcm_dvd_mul d m)
  let v : (ZMod (d.lcm m))ˣ := ZMod.unitOfCoprime k hkl
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective (Nat.lcm_dvd hd hm) v
  refine ⟨u, Units.ext ?_, Units.ext ?_⟩
  · have h := congrArg (fun w => ((ZMod.unitsMap (Nat.dvd_lcm_left d m) w :
        (ZMod d)ˣ) : ZMod d)) hu
    simp only [← MonoidHom.comp_apply, ZMod.unitsMap_comp] at h
    simp only [ZMod.unitsMap_val, v, ZMod.coe_unitOfCoprime,
      ZMod.cast_natCast (Nat.dvd_lcm_left d m)] at h
    simpa only [ZMod.unitsMap_val, ZMod.cast_eq_val] using
      h.trans ((ZMod.natCast_eq_natCast_iff _ _ _).mpr hk)
  · have h := congrArg (fun w => ((ZMod.unitsMap (Nat.dvd_lcm_right d m) w :
        (ZMod m)ˣ) : ZMod m)) hu
    simp only [← MonoidHom.comp_apply, ZMod.unitsMap_comp] at h
    simp only [ZMod.unitsMap_val, v, ZMod.coe_unitOfCoprime,
      ZMod.cast_natCast (Nat.dvd_lcm_right d m)] at h
    simpa only [ZMod.unitsMap_val, ZMod.cast_eq_val] using
      h.trans ((ZMod.natCast_eq_natCast_iff _ _ _).mpr hl)

/-- Unit scaling does not change the lower-coordinate divisor. -/
theorem columnGcd_unit_mul (N : ℕ) (u : (ZMod N)ˣ) (c : ZMod N) :
    columnGcd N ((u : ZMod N) * c) = columnGcd N c := by
  unfold columnGcd
  rw [ZMod.val_mul, ← Nat.gcd_rec, Nat.gcd_comm N]
  exact (ZMod.val_coe_unit_coprime u).gcd_mul_left_cancel c.val

theorem columnGcd_divisor (N d : ℕ) (hd : d ∣ N) :
    columnGcd N (d : ZMod N) = d := by
  rw [columnGcd, ZMod.val_natCast, ← Nat.gcd_rec, Nat.gcd_eq_right hd]

/-- A unit fixes the lower entry `d` precisely when it is one modulo `N/d`. -/
theorem unit_mul_divisor_eq_iff (N d : ℕ) [NeZero N] (hd : d ∣ N)
    (u : (ZMod N)ˣ) :
    (u : ZMod N) * (d : ZMod N) = d ↔
      ZMod.unitsMap (Nat.div_dvd_of_dvd hd) u = 1 := by
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero (NeZero.ne N) hd
  rw [← Units.val_inj]
  change _ ↔ ZMod.castHom (Nat.div_dvd_of_dvd hd) (ZMod (N / d)) (u : ZMod N) = 1
  rw [← ZMod.natCast_zmod_val (u : ZMod N)]
  simp only [map_natCast]
  rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
  rw [← Nat.cast_mul, ZMod.natCast_eq_natCast_iff]
  constructor
  · intro h
    have h' := (show (u : ZMod N).val * d ≡ 1 * d [MOD N] by simpa using h)
      |>.cancel_right_div_gcd (NeZero.pos N)
    simpa only [Nat.gcd_eq_right hd] using h'
  · intro h
    simpa only [one_mul, Nat.div_mul_cancel hd] using h.mul_right' d

/-- Reduction modulo a divisor detects translation by that divisor. -/
theorem divisorReduction_eq_iff (N d : ℕ) [NeZero N] (hd : d ∣ N) (a b : ZMod N) :
    ZMod.castHom hd (ZMod d) a = ZMod.castHom hd (ZMod d) b ↔
      ∃ j : ℤ, a = b + (j : ZMod N) * d := by
  let R := ZMod.castHom hd (ZMod d)
  constructor
  · intro hab
    have hz : R (a - b) = 0 := by simpa only [map_sub] using sub_eq_zero.mpr hab
    have hv : ((a - b).val : ZMod d) = 0 := by
      simpa only [← map_natCast R, ZMod.natCast_zmod_val] using hz
    obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hv
    refine ⟨(k : ℤ), ?_⟩
    have hdiff : a - b = (k : ZMod N) * d := by
      calc
        a - b = ((a - b).val : ZMod N) := (ZMod.natCast_zmod_val _).symm
        _ = _ := by rw [hk, Nat.cast_mul, mul_comm]
    push_cast
    linear_combination hdiff
  · rintro ⟨j, rfl⟩
    simp only [map_add, map_mul, map_natCast, ZMod.natCast_self, mul_zero, add_zero]

/-- An integral representative with prescribed unit upper entry and lower divisor. -/
def gamma0CuspRep (N : ℕ) [NeZero N] (d : ℕ) (a : (ZMod N)ˣ) : SL(2, ℤ) :=
  Classical.choose (exists_SL2_firstColumn N (a : ZMod N) (d : ZMod N)
    ⟨(a⁻¹ : (ZMod N)ˣ), 0, by simp⟩)

theorem gamma0CuspRep_firstColumn (N : ℕ) [NeZero N] (d : ℕ) (a : (ZMod N)ˣ) :
    (gamma0CuspRep N d a 0 0 : ZMod N) = a ∧
      (gamma0CuspRep N d a 1 0 : ZMod N) = d :=
  Classical.choose_spec (exists_SL2_firstColumn N (a : ZMod N) (d : ZMod N)
    ⟨(a⁻¹ : (ZMod N)ˣ), 0, by simp⟩)

/-- The actual cusp represented by the normalized column `(a,d)`. -/
def gamma0CuspOfUnit (N : ℕ) [NeZero N] (d : ℕ) (a : (ZMod N)ˣ) :
    subgroupCusps (CongruenceSubgroup.Gamma0 N) :=
  ⟦(gamma0CuspRep N d a : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)⟧

/-- Every genuine cusp has a representative with lower entry a divisor of the
level and upper entry a unit modulo the level. -/
theorem gamma0CuspOfUnit_surjective (N : ℕ) [NeZero N]
    (x : subgroupCusps (CongruenceSubgroup.Gamma0 N)) :
    ∃ (d : ℕ) (_ : d ∣ N) (a : (ZMod N)ˣ), gamma0CuspOfUnit N d a = x := by
  induction x using Quotient.inductionOn with
  | h q =>
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨d, hd, u, hu, hc⟩ := ZMod.eq_unit_mul_divisor (g 1 0 : ZMod N)
      obtain ⟨u, rfl⟩ := hu
      let R := ZMod.castHom hd (ZMod d)
      have hcR : R (g 1 0 : ZMod N) = 0 := by
        rw [hc, map_mul, map_natCast, ZMod.natCast_self, mul_zero]
      have hdet := congrArg (Int.cast : ℤ → ZMod N) g.det_coe
      simp only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one] at hdet
      have hdetR := congrArg R hdet
      simp only [map_sub, map_mul, map_one, hcR, mul_zero, sub_zero] at hdetR
      let b : ZMod N := (u⁻¹ : (ZMod N)ˣ) * (g 0 0 : ZMod N)
      have hb : IsUnit (R b) := by
        simpa only [b, R, map_mul, ZMod.castHom_apply, ZMod.unitsMap_val,
          Units.val_mkOfMulEqOne] using
          (ZMod.unitsMap hd u⁻¹).isUnit.mul (Units.mkOfMulEqOne _ _ hdetR).isUnit
      obtain ⟨a, ha⟩ := ZMod.unitsMap_surjective hd hb.unit
      have hba : R b = R (a : ZMod N) := by
        exact hb.unit_spec.symm.trans (congrArg Units.val ha).symm
      obtain ⟨j, hj⟩ := (divisorReduction_eq_iff N d hd b a).mp hba
      refine ⟨d, hd, a, Eq.symm ?_⟩
      apply (gamma0_cusp_eq_iff N g (gamma0CuspRep N d a)).mpr
      rw [(gamma0CuspRep_firstColumn N d a).1, (gamma0CuspRep_firstColumn N d a).2]
      refine ⟨j, u, ?_, hc⟩
      calc
        (g 0 0 : ZMod N) = (u : ZMod N) * b := by simp [b, ← mul_assoc]
        _ = _ := congrArg ((u : ZMod N) * ·) hj

/-- Normalized cusp columns have the same divisor; their remaining invariant is
the upper unit modulo `gcd(d,N/d)`. -/
theorem gamma0CuspOfUnit_eq_iff (N d e : ℕ) [NeZero N] (hd : d ∣ N) (he : e ∣ N)
    (a b : (ZMod N)ˣ) :
    gamma0CuspOfUnit N d a = gamma0CuspOfUnit N e b ↔
      d = e ∧ ZMod.unitsMap (dvd_trans (Nat.gcd_dvd_left d (N / d)) hd) a =
        ZMod.unitsMap (dvd_trans (Nat.gcd_dvd_left d (N / d)) hd) b := by
  rw [gamma0CuspOfUnit, gamma0CuspOfUnit, gamma0_cusp_eq_iff]
  simp only [(gamma0CuspRep_firstColumn N d a).1,
    (gamma0CuspRep_firstColumn N d a).2,
    (gamma0CuspRep_firstColumn N e b).1,
    (gamma0CuspRep_firstColumn N e b).2]
  constructor
  · rintro ⟨j, u, ha, hc⟩
    have hde : d = e := by
      calc
        d = columnGcd N (d : ZMod N) := (columnGcd_divisor N d hd).symm
        _ = columnGcd N ((u : ZMod N) * (e : ZMod N)) := congrArg (columnGcd N) hc
        _ = columnGcd N (e : ZMod N) := columnGcd_unit_mul N u _
        _ = e := columnGcd_divisor N e he
    subst e
    refine ⟨rfl, Units.ext ?_⟩
    have hu := (unit_mul_divisor_eq_iff N d hd u).mp hc.symm
    let R := ZMod.castHom (dvd_trans (Nat.gcd_dvd_left d (N / d)) hd)
      (ZMod (d.gcd (N / d)))
    have huR : R (u : ZMod N) = 1 := by
      have hunit : ZMod.unitsMap (dvd_trans (Nat.gcd_dvd_left d (N / d)) hd) u = 1 := by
        calc
          _ = ZMod.unitsMap (Nat.gcd_dvd_right d (N / d))
              (ZMod.unitsMap (Nat.div_dvd_of_dvd hd) u) := by
            rw [← MonoidHom.comp_apply, ZMod.unitsMap_comp]
          _ = 1 := by rw [hu, map_one]
      exact congrArg Units.val hunit
    have hdR : R (d : ZMod N) = 0 := by
      rw [map_natCast, ZMod.natCast_eq_zero_iff]
      exact Nat.gcd_dvd_left d (N / d)
    have h := congrArg R ha
    simp only [map_mul, map_add, hdR, mul_zero, add_zero, huR, one_mul] at h
    exact h
  · rintro ⟨rfl, hab⟩
    let hg := dvd_trans (Nat.gcd_dvd_left d (N / d)) hd
    have hcompat : ZMod.castHom hg (ZMod (d.gcd (N / d)))
        ((a * b⁻¹ : (ZMod N)ˣ) : ZMod N) =
      ZMod.castHom (dvd_trans (Nat.gcd_dvd_right d (N / d))
        (Nat.div_dvd_of_dvd hd)) (ZMod (d.gcd (N / d))) (1 : ZMod N) := by
      change ((ZMod.unitsMap hg (a * b⁻¹) : (ZMod (d.gcd (N / d)))ˣ) :
        ZMod (d.gcd (N / d))) = _
      rw [map_mul, map_inv, hab, mul_inv_cancel, Units.val_one, map_one]
    obtain ⟨u, hud, hum⟩ := exists_unit_lift_pair N d (N / d) hd
      (Nat.div_dvd_of_dvd hd) (a * b⁻¹) 1 hcompat
    have hc : (u : ZMod N) * (d : ZMod N) = d :=
      (unit_mul_divisor_eq_iff N d hd u).mpr (by simpa only [map_one] using hum)
    have had : ZMod.unitsMap hd a = ZMod.unitsMap hd (u * b) := by
      rw [map_mul, hud, map_mul, map_inv]
      group
    obtain ⟨j, hj⟩ := (divisorReduction_eq_iff N d hd _ _).mp (congrArg Units.val had)
    refine ⟨j, u, ?_, hc.symm⟩
    change (a : ZMod N) = (u : ZMod N) * (b : ZMod N) + (j : ZMod N) * d at hj
    linear_combination hj - (j : ZMod N) * hc

/-- The divisor indexing a normalized cusp. -/
abbrev Gamma0CuspDivisor (N : ℕ) := {d : ℕ // d ∈ N.divisors}

/-- The modulus of the remaining upper-entry invariant. -/
abbrev gamma0CuspModulus (N : ℕ) (d : Gamma0CuspDivisor N) : ℕ :=
  d.val.gcd (N / d.val)

instance gamma0CuspModulus_neZero (N : ℕ) [NeZero N] (d : Gamma0CuspDivisor N) :
    NeZero (gamma0CuspModulus N d) :=
  ⟨Nat.gcd_ne_zero_left (ne_zero_of_dvd_ne_zero (NeZero.ne N)
    (Nat.mem_divisors.mp d.property).1)⟩

theorem gamma0CuspModulus_dvd (N : ℕ) (d : Gamma0CuspDivisor N) :
    gamma0CuspModulus N d ∣ N :=
  dvd_trans (Nat.gcd_dvd_left _ _) (Nat.mem_divisors.mp d.property).1

/-- Arithmetic cusp labels: a divisor and a unit modulo `gcd(d,N/d)`. -/
abbrev Gamma0CuspData (N : ℕ) :=
  Σ d : Gamma0CuspDivisor N, (ZMod (gamma0CuspModulus N d))ˣ

/-- Choose a unit lift for an arithmetic cusp label. Its choice disappears in
the cusp quotient. -/
def gamma0CuspDataLift (N : ℕ) [NeZero N] (x : Gamma0CuspData N) : (ZMod N)ˣ :=
  Classical.choose (ZMod.unitsMap_surjective (gamma0CuspModulus_dvd N x.1) x.2)

theorem gamma0CuspDataLift_spec (N : ℕ) [NeZero N] (x : Gamma0CuspData N) :
    ZMod.unitsMap (gamma0CuspModulus_dvd N x.1) (gamma0CuspDataLift N x) = x.2 :=
  Classical.choose_spec (ZMod.unitsMap_surjective (gamma0CuspModulus_dvd N x.1) x.2)

/-- From the classical finite labels to the genuine analytic group's cusp set. -/
def gamma0CuspDataMap (N : ℕ) [NeZero N] (x : Gamma0CuspData N) :
    subgroupCusps (CongruenceSubgroup.Gamma0 N) :=
  gamma0CuspOfUnit N x.1.val (gamma0CuspDataLift N x)

theorem gamma0CuspDataMap_bijective (N : ℕ) [NeZero N] :
    Function.Bijective (gamma0CuspDataMap N) := by
  constructor
  · rintro ⟨d, a⟩ ⟨e, b⟩ hab
    obtain ⟨hde, hu⟩ := (gamma0CuspOfUnit_eq_iff N d.val e.val
      (Nat.mem_divisors.mp d.property).1 (Nat.mem_divisors.mp e.property).1 _ _).mp hab
    have hde' : d = e := Subtype.ext hde
    subst e
    have hab' : a = b := by
      change ZMod.unitsMap (gamma0CuspModulus_dvd N d) (gamma0CuspDataLift N ⟨d, a⟩) =
        ZMod.unitsMap (gamma0CuspModulus_dvd N d) (gamma0CuspDataLift N ⟨d, b⟩) at hu
      exact (gamma0CuspDataLift_spec N ⟨d, a⟩).symm.trans
        (hu.trans (gamma0CuspDataLift_spec N ⟨d, b⟩))
    subst b
    rfl
  · intro x
    obtain ⟨d, hd, a, ha⟩ := gamma0CuspOfUnit_surjective N x
    let D : Gamma0CuspDivisor N := ⟨d, Nat.mem_divisors.mpr ⟨hd, NeZero.ne N⟩⟩
    let y : Gamma0CuspData N := ⟨D, ZMod.unitsMap (gamma0CuspModulus_dvd N D) a⟩
    refine ⟨y, Eq.trans ?_ ha⟩
    apply (gamma0CuspOfUnit_eq_iff N d d hd hd _ _).mpr
    exact ⟨rfl, gamma0CuspDataLift_spec N y⟩

/-- The arithmetic divisor sum counts the actual `Γ₀(N)` cusps at every positive level. -/
theorem gamma0GeometricCuspCount_eq_cuspCount (N : ℕ) [NeZero N] :
    gamma0GeometricCuspCount N = gamma0CuspCount N := by
  rw [gamma0GeometricCuspCount,
    ← Nat.card_eq_of_bijective _ (gamma0CuspDataMap_bijective N),
    Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [ZMod.card_units_eq_totient, gamma0CuspModulus, gamma0CuspCount]
  exact Finset.sum_attach N.divisors (fun d : ℕ => (d.gcd (N / d)).totient)

end WeightTwoCusps
