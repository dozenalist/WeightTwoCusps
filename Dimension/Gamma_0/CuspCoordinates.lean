module

public import Dimension.Gamma_1.CuspModel

/-! # First-column arithmetic for Γ₀(N) cosets and cusps -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

namespace WeightTwoCusps

/-- A useful affine chart of the congruence coset space. -/
def gamma0AffineRep (N : ℕ) (x : ZMod N) : SL(2, ℤ) :=
  ModularGroup.T ^ (x.val : ℤ) * ModularGroup.S

theorem gamma0AffineRep_firstColumn (N : ℕ) [NeZero N] (x : ZMod N) :
    (gamma0AffineRep N x 0 0 : ZMod N) = x ∧
      (gamma0AffineRep N x 1 0 : ZMod N) = 1 := by
  simpa only [gamma0AffineRep, ModularGroup.coe_S, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Int.cast_zero, Int.cast_one, zero_add, mul_one, Int.cast_natCast,
    ZMod.natCast_zmod_val] using T_zpow_mul_firstColumn N (x.val : ℤ) ModularGroup.S

/-- `Γ₀(N)` cosets are first columns up to a common unit modulo the level. -/
theorem gamma0_coset_eq_iff (N : ℕ) (g h : SL(2, ℤ)) :
    (g : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) = h ↔
      ∃ u : (ZMod N)ˣ, (g 0 0 : ZMod N) = u * (h 0 0 : ZMod N) ∧
        (g 1 0 : ZMod N) = u * (h 1 0 : ZMod N) := by
  constructor
  · intro heq
    have hk : h⁻¹ * g ∈ CongruenceSubgroup.Gamma0 N := QuotientGroup.eq.mp heq.symm
    have hc := CongruenceSubgroup.Gamma0_mem.mp hk
    have hd := congrArg (Int.cast : ℤ → ZMod N) (h⁻¹ * g).det_coe
    simp only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one,
      hc, mul_zero, sub_zero] at hd
    let u : (ZMod N)ˣ := Units.mkOfMulEqOne
      ((h⁻¹ * g) 0 0 : ZMod N) ((h⁻¹ * g) 1 1 : ZMod N) hd
    have hh : h * (h⁻¹ * g) = g := by group
    have hf (i : Fin 2) := firstColumn_mul N h (h⁻¹ * g) i
    simp only [hh, hc, mul_zero, add_zero] at hf
    exact ⟨u, by simpa only [u, Units.val_mkOfMulEqOne, mul_comm] using hf 0,
      by simpa only [u, Units.val_mkOfMulEqOne, mul_comm] using hf 1⟩
  · rintro ⟨u, ha, hc⟩
    rw [QuotientGroup.eq, CongruenceIndex.mem_Gamma0_iff_dvd,
      CongruenceIndex.inv_mul_apply_10, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ha, hc]
    ring

/-- `Γ₀(N)` cusp equivalence is simultaneous unit scaling and translation of columns.
This is a finite arithmetic starting point for the remaining divisor-sum count. -/
theorem gamma0_cusp_eq_iff (N : ℕ) (g h : SL(2, ℤ)) :
    (⟦(g : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)⟧ :
      MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.T)
        (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)) = ⟦(h : SL(2, ℤ) ⧸ _)⟧ ↔
      ∃ (j : ℤ) (u : (ZMod N)ˣ),
        (g 0 0 : ZMod N) = u * ((h 0 0 : ZMod N) + j * (h 1 0 : ZMod N)) ∧
        (g 1 0 : ZMod N) = u * (h 1 0 : ZMod N) := by
  rw [Quotient.eq, MulAction.orbitRel_apply]
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp t.property
    change t.val • (h : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) = _ at ht
    rw [← hj, MulAction.Quotient.smul_coe, smul_eq_mul] at ht
    obtain ⟨u, hu⟩ := (gamma0_coset_eq_iff N g (ModularGroup.T ^ j * h)).mp ht.symm
    rw [(T_zpow_mul_firstColumn N j h).1, (T_zpow_mul_firstColumn N j h).2] at hu
    exact ⟨j, u, hu⟩
  · rintro ⟨j, u, ha, hc⟩
    refine ⟨⟨ModularGroup.T ^ j, Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) j⟩, ?_⟩
    change ModularGroup.T ^ j • (h : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) = _
    rw [MulAction.Quotient.smul_coe, smul_eq_mul]
    apply Eq.symm
    apply (gamma0_coset_eq_iff N g _).mpr
    rw [(T_zpow_mul_firstColumn N j h).1, (T_zpow_mul_firstColumn N j h).2]
    exact ⟨u, ha, hc⟩

/-- Order-two elliptic fixed cosets are exactly roots of `x²+1` in the affine chart. -/
theorem gamma0_S_fixed_affine_iff (N : ℕ) [NeZero N] (g : SL(2, ℤ)) :
    ModularGroup.S • (g : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) = g ↔
      ∃ x : ZMod N, x ^ 2 + 1 = 0 ∧
        (g : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) = gamma0AffineRep N x := by
  rw [MulAction.Quotient.smul_coe, smul_eq_mul, gamma0_coset_eq_iff]
  have hS (i : Fin 2) : ((ModularGroup.S * g) i 0 : ZMod N) =
      if i = 0 then -(g 1 0 : ZMod N) else (g 0 0 : ZMod N) := by
    fin_cases i <;> simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S,
      Matrix.mul_apply, Fin.sum_univ_two]
  simp only [hS, show (1 : Fin 2) ≠ 0 by decide, ite_false, ite_true]
  constructor
  · rintro ⟨u, ha, hc⟩
    have hd := congrArg (Int.cast : ℤ → ZMod N) g.det_coe
    simp only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one] at hd
    have hunit : (g 1 0 : ZMod N) * ((u : ZMod N) * (g 1 1 : ZMod N) -
        (g 0 1 : ZMod N)) = 1 := by linear_combination hd - (g 1 1 : ZMod N) * hc
    let v : (ZMod N)ˣ := Units.mkOfMulEqOne _ _ hunit
    have hz : ((u : ZMod N) ^ 2 + 1) * (g 1 0 : ZMod N) = 0 := by
      linear_combination -ha - (u : ZMod N) * hc
    have hr : (u : ZMod N) ^ 2 + 1 = 0 := by
      calc
        _ = (((u : ZMod N) ^ 2 + 1) * (v : ZMod N)) * (v⁻¹ : (ZMod N)ˣ) := by
          simp only [mul_assoc, Units.mul_inv, mul_one]
        _ = 0 := by change (_ * (g 1 0 : ZMod N)) * _ = 0; rw [hz, zero_mul]
    refine ⟨u, hr, (gamma0_coset_eq_iff N g _).mpr ⟨v, ?_, ?_⟩⟩
    · rw [(gamma0AffineRep_firstColumn N (u : ZMod N)).1]
      exact hc.trans (mul_comm _ _)
    · rw [(gamma0AffineRep_firstColumn N (u : ZMod N)).2, mul_one]
      rfl
  · rintro ⟨x, hx, hrep⟩
    obtain ⟨v, ha, hc⟩ := (gamma0_coset_eq_iff N g (gamma0AffineRep N x)).mp hrep
    rw [(gamma0AffineRep_firstColumn N x).1] at ha
    rw [(gamma0AffineRep_firstColumn N x).2, mul_one] at hc
    have hu : x * (-x) = 1 := by linear_combination -hx
    let u := Units.mkOfMulEqOne x (-x) hu
    refine ⟨u, ?_, ?_⟩
    · change -(g 1 0 : ZMod N) = x * (g 0 0 : ZMod N)
      rw [ha, hc]
      linear_combination -(v : ZMod N) * hx
    · change (g 0 0 : ZMod N) = x * (g 1 0 : ZMod N)
      rw [ha, hc, mul_comm]

/-- The number of fixed cosets of the order-two elliptic generator is the
classical root-count correction, for arbitrary positive level. -/
theorem gamma0_card_fixedBy_S (N : ℕ) [NeZero N] :
    Nat.card (MulAction.fixedBy (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) ModularGroup.S) =
      gamma0EllipticTwoCount N := by
  let f : {x : ZMod N // x ^ 2 + 1 = 0} →
      MulAction.fixedBy (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) ModularGroup.S := fun x =>
    ⟨(gamma0AffineRep N x.val : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N),
      (gamma0_S_fixed_affine_iff N _).mpr ⟨x.val, x.property, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have hq := congrArg Subtype.val hxy
      obtain ⟨u, ha, hc⟩ := (gamma0_coset_eq_iff N (gamma0AffineRep N x.val)
        (gamma0AffineRep N y.val)).mp hq
      rw [(gamma0AffineRep_firstColumn N x.val).1,
        (gamma0AffineRep_firstColumn N y.val).1] at ha
      rw [(gamma0AffineRep_firstColumn N x.val).2,
        (gamma0AffineRep_firstColumn N y.val).2, mul_one] at hc
      exact Subtype.ext (by simpa only [← hc, one_mul] using ha)
    · rintro ⟨q, hq⟩
      induction q using QuotientGroup.induction_on with
      | H g =>
        obtain ⟨x, hx, hrep⟩ := (gamma0_S_fixed_affine_iff N g).mp hq
        exact ⟨⟨x, hx⟩, Subtype.ext hrep.symm⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_subtype,
    gamma0EllipticTwoCount]
  symm
  apply Finset.card_bij (fun (a : ℕ) _ => (a : ZMod N))
  · intro a ha
    obtain ⟨haN, ha⟩ := Finset.mem_filter.mp ha
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [← Nat.cast_pow, ← Nat.cast_one, ← Nat.cast_add, ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_of_mod_eq_zero ha
  · intro a ha b hb hab
    have hav : a < N := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have hbv : b < N := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    have hh := congrArg ZMod.val hab
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hav, Nat.mod_eq_of_lt hbv] using hh
  · intro x hx
    refine ⟨x.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt x), ?_⟩,
      ZMod.natCast_zmod_val x⟩
    have hh := (Finset.mem_filter.mp hx).2
    rw [← ZMod.natCast_zmod_val x, ← Nat.cast_pow, ← Nat.cast_one,
      ← Nat.cast_add, ZMod.natCast_eq_zero_iff] at hh
    exact Nat.mod_eq_zero_of_dvd hh

/-- Order-three elliptic fixed cosets are roots of `x²+x+1` in the same chart. -/
theorem gamma0_ST_fixed_affine_iff (N : ℕ) [NeZero N] (g : SL(2, ℤ)) :
    (ModularGroup.S * ModularGroup.T) • (g : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) = g ↔
      ∃ x : ZMod N, x ^ 2 + x + 1 = 0 ∧
        (g : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) = gamma0AffineRep N x := by
  rw [MulAction.Quotient.smul_coe, smul_eq_mul, gamma0_coset_eq_iff]
  have hST (i : Fin 2) : (((ModularGroup.S * ModularGroup.T) * g) i 0 : ZMod N) =
      if i = 0 then -(g 1 0 : ZMod N) else (g 0 0 : ZMod N) + (g 1 0 : ZMod N) := by
    fin_cases i <;> simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S,
      ModularGroup.coe_T, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [hST, show (1 : Fin 2) ≠ 0 by decide, ite_false, ite_true]
  constructor
  · rintro ⟨u, ha, hc⟩
    have hd := congrArg (Int.cast : ℤ → ZMod N) g.det_coe
    simp only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one] at hd
    have hc' : (g 0 0 : ZMod N) = ((u : ZMod N) - 1) * (g 1 0 : ZMod N) := by
      linear_combination hc
    have hunit : (g 1 0 : ZMod N) * (((u : ZMod N) - 1) * (g 1 1 : ZMod N) -
        (g 0 1 : ZMod N)) = 1 := by linear_combination hd - (g 1 1 : ZMod N) * hc'
    let v : (ZMod N)ˣ := Units.mkOfMulEqOne _ _ hunit
    have hz : (((u : ZMod N) - 1) ^ 2 + ((u : ZMod N) - 1) + 1) *
        (g 1 0 : ZMod N) = 0 := by
      linear_combination -ha - (u : ZMod N) * hc
    have hr : ((u : ZMod N) - 1) ^ 2 + ((u : ZMod N) - 1) + 1 = 0 := by
      calc
        _ = ((((u : ZMod N) - 1) ^ 2 + ((u : ZMod N) - 1) + 1) *
            (v : ZMod N)) * (v⁻¹ : (ZMod N)ˣ) := by
          simp only [mul_assoc, Units.mul_inv, mul_one]
        _ = 0 := by change (_ * (g 1 0 : ZMod N)) * _ = 0; rw [hz, zero_mul]
    refine ⟨(u : ZMod N) - 1, hr, (gamma0_coset_eq_iff N g _).mpr ⟨v, ?_, ?_⟩⟩
    · rw [(gamma0AffineRep_firstColumn N ((u : ZMod N) - 1)).1]
      exact hc'.trans (mul_comm _ _)
    · rw [(gamma0AffineRep_firstColumn N ((u : ZMod N) - 1)).2, mul_one]
      rfl
  · rintro ⟨x, hx, hrep⟩
    obtain ⟨v, ha, hc⟩ := (gamma0_coset_eq_iff N g (gamma0AffineRep N x)).mp hrep
    rw [(gamma0AffineRep_firstColumn N x).1] at ha
    rw [(gamma0AffineRep_firstColumn N x).2, mul_one] at hc
    have hu : (x + 1) * (-x) = 1 := by linear_combination -hx
    let u := Units.mkOfMulEqOne (x + 1) (-x) hu
    refine ⟨u, ?_, ?_⟩
    · change -(g 1 0 : ZMod N) = (x + 1) * (g 0 0 : ZMod N)
      rw [ha, hc]
      linear_combination -(v : ZMod N) * hx
    · change (g 0 0 : ZMod N) + (g 1 0 : ZMod N) = (x + 1) * (g 1 0 : ZMod N)
      rw [ha, hc]
      ring

/-- The number of fixed cosets of the order-three elliptic generator is the
classical root-count correction, for arbitrary positive level. -/
theorem gamma0_card_fixedBy_ST (N : ℕ) [NeZero N] :
    Nat.card (MulAction.fixedBy (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) (ModularGroup.S * ModularGroup.T)) =
      gamma0EllipticThreeCount N := by
  let f : {x : ZMod N // x ^ 2 + x + 1 = 0} →
      MulAction.fixedBy (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
        (ModularGroup.S * ModularGroup.T) := fun x =>
    ⟨(gamma0AffineRep N x.val : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N),
      (gamma0_ST_fixed_affine_iff N _).mpr ⟨x.val, x.property, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have hq := congrArg Subtype.val hxy
      obtain ⟨u, ha, hc⟩ := (gamma0_coset_eq_iff N (gamma0AffineRep N x.val)
        (gamma0AffineRep N y.val)).mp hq
      rw [(gamma0AffineRep_firstColumn N x.val).1,
        (gamma0AffineRep_firstColumn N y.val).1] at ha
      rw [(gamma0AffineRep_firstColumn N x.val).2,
        (gamma0AffineRep_firstColumn N y.val).2, mul_one] at hc
      exact Subtype.ext (by simpa only [← hc, one_mul] using ha)
    · rintro ⟨q, hq⟩
      induction q using QuotientGroup.induction_on with
      | H g =>
        obtain ⟨x, hx, hrep⟩ := (gamma0_ST_fixed_affine_iff N g).mp hq
        exact ⟨⟨x, hx⟩, Subtype.ext hrep.symm⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_subtype,
    gamma0EllipticThreeCount]
  symm
  apply Finset.card_bij (fun (a : ℕ) _ => (a : ZMod N))
  · intro a ha
    obtain ⟨haN, ha⟩ := Finset.mem_filter.mp ha
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [← Nat.cast_pow, ← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_of_mod_eq_zero ha
  · intro a ha b hb hab
    have hav : a < N := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have hbv : b < N := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    have hh := congrArg ZMod.val hab
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hav, Nat.mod_eq_of_lt hbv] using hh
  · intro x hx
    refine ⟨x.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt x), ?_⟩,
      ZMod.natCast_zmod_val x⟩
    have hh := (Finset.mem_filter.mp hx).2
    rw [← ZMod.natCast_zmod_val x, ← Nat.cast_pow, ← Nat.cast_one,
      ← Nat.cast_add, ← Nat.cast_add, ZMod.natCast_eq_zero_iff] at hh
    exact Nat.mod_eq_zero_of_dvd hh

end WeightTwoCusps
