module

public import Dimension.Gamma_1.Arithmetic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.ZMod.QuotientGroup

/-! # The arithmetic cusp count for `Γ₁(N)`

Right cosets of `Γ₁(N)` are detected by the first column modulo `N`.
For the projective closure the column is determined up to a common sign.
Translation orbits are classified by the lower residue `c` and a unit modulo
`gcd(c,N)`. Their cardinal is the totient convolution. Sign acts freely when
`N ≥ 5`, giving the classical projective cusp count. All matrix representatives
are constructed integrally using the existing surjectivity theorem on units.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

namespace WeightTwoCusps

/-- The first column of a product, reduced modulo the level. -/
theorem firstColumn_mul (N : ℕ) (g h : SL(2, ℤ)) (i : Fin 2) :
    ((g * h) i 0 : ZMod N) =
      (g i 0 : ZMod N) * (h 0 0 : ZMod N) +
        (g i 1 : ZMod N) * (h 1 0 : ZMod N) := by
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

/-- Equality of the genuine right cosets is equality of their first columns. -/
theorem gamma1_coset_eq_iff (N : ℕ) (g h : SL(2, ℤ)) :
    (g : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N) = h ↔
      (g 0 0 : ZMod N) = (h 0 0 : ZMod N) ∧
        (g 1 0 : ZMod N) = (h 1 0 : ZMod N) := by
  rw [QuotientGroup.eq]
  constructor
  · intro hm
    obtain ⟨ha, _, hc⟩ := CongruenceSubgroup.Gamma1_mem N (g⁻¹ * h) |>.mp hm
    have heq : g * (g⁻¹ * h) = h := by group
    have hf (i : Fin 2) := firstColumn_mul N g (g⁻¹ * h) i
    simp only [ha, hc, mul_one, mul_zero, add_zero, heq] at hf
    exact ⟨(hf 0).symm, (hf 1).symm⟩
  · rintro ⟨ha, hc⟩
    have hdet := congrArg (Int.cast : ℤ → ZMod N) g.det_coe
    have hdet' := congrArg (Int.cast : ℤ → ZMod N) h.det_coe
    simp only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one] at hdet
    simp only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one, ← ha, ← hc] at hdet'
    rw [CongruenceSubgroup.Gamma1_mem]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one,
      Int.cast_add, Int.cast_mul, Int.cast_neg, ← ha, ← hc]
    constructor
    · linear_combination hdet
    constructor
    · linear_combination hdet'
    · ring

/-- Projective congruence cosets identify exactly a column and its negative. -/
theorem gamma1_projective_coset_eq_iff (N : ℕ) (g h : SL(2, ℤ)) :
    (g : SL(2, ℤ) ⧸ projectiveClosure (CongruenceSubgroup.Gamma1 N)) = h ↔
      ((g 0 0 : ZMod N) = (h 0 0 : ZMod N) ∧
        (g 1 0 : ZMod N) = (h 1 0 : ZMod N)) ∨
      ((g 0 0 : ZMod N) = -(h 0 0 : ZMod N) ∧
        (g 1 0 : ZMod N) = -(h 1 0 : ZMod N)) := by
  rw [QuotientGroup.eq, mem_projectiveClosure_iff]
  have hn : -(g⁻¹ * h) = g⁻¹ * (-h) := by simp
  rw [hn, ← QuotientGroup.eq, ← QuotientGroup.eq,
    gamma1_coset_eq_iff, gamma1_coset_eq_iff]
  simp

/-- The common divisor controlling translation orbits in the upper entry. -/
abbrev columnGcd (N : ℕ) (c : ZMod N) : ℕ := c.val.gcd N

/-- Reduction to the modulus which is unchanged by adding a multiple of `c`. -/
def columnReduction (N : ℕ) (c : ZMod N) : ZMod N →+* ZMod (columnGcd N c) :=
  ZMod.castHom (Nat.gcd_dvd_right c.val N) _

theorem columnReduction_self (N : ℕ) [NeZero N] (c : ZMod N) : columnReduction N c c = 0 := by
  calc
    columnReduction N c c = columnReduction N c (c.val : ZMod N) := by
      rw [ZMod.natCast_zmod_val]
    _ = (c.val : ZMod (columnGcd N c)) := map_natCast _ _
    _ = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.gcd_dvd_left c.val N)

/-- Translation orbits in a fixed lower-entry fiber are congruence classes modulo its gcd. -/
theorem columnReduction_eq_iff (N : ℕ) [NeZero N] (c a b : ZMod N) :
    columnReduction N c a = columnReduction N c b ↔
      ∃ j : ℤ, a = b + (j : ZMod N) * c := by
  constructor
  · intro hab
    have hz : columnReduction N c (a - b) = 0 := by simpa using sub_eq_zero.mpr hab
    have hv : (((a - b).val : ℕ) : ZMod (columnGcd N c)) = 0 := by
      simpa only [← map_natCast (columnReduction N c), ZMod.natCast_zmod_val] using hz
    obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hv
    refine ⟨(((k : ZMod N) * c⁻¹).val : ℤ), ?_⟩
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
    have hd : a - b = (k : ZMod N) * (c * c⁻¹) := by
      rw [ZMod.mul_inv_eq_gcd, ← Nat.cast_mul, mul_comm k, ← hk,
        ZMod.natCast_zmod_val]
    linear_combination hd
  · rintro ⟨j, rfl⟩
    simp [columnReduction_self]

instance columnGcd_neZero (N : ℕ) [NeZero N] (c : ZMod N) : NeZero (columnGcd N c) :=
  ⟨Nat.gcd_ne_zero_right (NeZero.ne N)⟩

/-- The unit in the upper coordinate after reduction modulo the lower-coordinate gcd. -/
def columnUnit (N : ℕ) [NeZero N] (g : SL(2, ℤ)) :
    (ZMod (columnGcd N (g 1 0 : ZMod N)))ˣ :=
  Units.mkOfMulEqOne
    (columnReduction N (g 1 0 : ZMod N) (g 0 0 : ZMod N))
    (columnReduction N (g 1 0 : ZMod N) (g 1 1 : ZMod N)) (by
      have hd := congrArg (Int.cast : ℤ → ZMod N) g.det_coe
      simp only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one] at hd
      have hr := congrArg (columnReduction N (g 1 0 : ZMod N)) hd
      simpa only [map_sub, map_mul, map_one, columnReduction_self, mul_zero,
        sub_zero] using hr)

/-- Arithmetic labels for the translation orbits before dividing by sign. -/
abbrev Gamma1CuspData (N : ℕ) :=
  Σ c : ZMod N, { a : Fin (columnGcd N c) // (columnGcd N c).Coprime a.val }

theorem Gamma1CuspData.ext {N : ℕ} {x y : Gamma1CuspData N}
    (hc : x.1 = y.1) (ha : x.2.val.val = y.2.val.val) : x = y := by
  rcases x with ⟨c, a⟩
  rcases y with ⟨d, b⟩
  dsimp at hc ha
  subst d
  congr 1
  exact Subtype.ext (Fin.ext ha)

/-- A matrix's arithmetic cusp label. -/
def matrixGamma1CuspData (N : ℕ) [NeZero N] (g : SL(2, ℤ)) : Gamma1CuspData N :=
  ⟨(g 1 0 : ZMod N), ⟨⟨(columnUnit N g).val.val, ZMod.val_lt _⟩,
    (ZMod.val_coe_unit_coprime (columnUnit N g)).symm⟩⟩

/-- First columns under an integral translation. -/
theorem T_zpow_mul_firstColumn (N : ℕ) (j : ℤ) (g : SL(2, ℤ)) :
    ((ModularGroup.T ^ j * g) 0 0 : ZMod N) =
      (g 0 0 : ZMod N) + (j : ZMod N) * (g 1 0 : ZMod N) ∧
    ((ModularGroup.T ^ j * g) 1 0 : ZMod N) = (g 1 0 : ZMod N) := by
  simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow,
    Matrix.mul_apply, Fin.sum_univ_two]

/-- Translation orbits on the unprojectivized `Γ₁(N)` cosets. -/
abbrev rawGamma1Cusps (N : ℕ) :=
  MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.T)
    (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N)

/-- The complete arithmetic criterion for equality of unprojectivized cusp representatives. -/
theorem rawGamma1Cusp_eq_iff (N : ℕ) [NeZero N] (g h : SL(2, ℤ)) :
    (⟦(g : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N)⟧ : rawGamma1Cusps N) =
      ⟦(h : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N)⟧ ↔
    (g 1 0 : ZMod N) = (h 1 0 : ZMod N) ∧
      columnReduction N (g 1 0 : ZMod N) (g 0 0 : ZMod N) =
        columnReduction N (g 1 0 : ZMod N) (h 0 0 : ZMod N) := by
  rw [Quotient.eq, MulAction.orbitRel_apply]
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp u.property
    change (u.val • (h : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N)) = _ at hu
    rw [← hj, MulAction.Quotient.smul_coe, smul_eq_mul, gamma1_coset_eq_iff] at hu
    rw [(T_zpow_mul_firstColumn N j h).1, (T_zpow_mul_firstColumn N j h).2] at hu
    refine ⟨hu.2.symm, ?_⟩
    rw [← hu.1, ← hu.2]
    rw [map_add, map_mul, columnReduction_self, mul_zero, add_zero]
  · rintro ⟨hc, ha⟩
    obtain ⟨j, hj⟩ := (columnReduction_eq_iff N (g 1 0 : ZMod N) _ _).mp ha
    refine ⟨⟨ModularGroup.T ^ j, Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) j⟩, ?_⟩
    change ModularGroup.T ^ j • (h : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N) = _
    rw [MulAction.Quotient.smul_coe, smul_eq_mul, gamma1_coset_eq_iff]
    rw [(T_zpow_mul_firstColumn N j h).1, (T_zpow_mul_firstColumn N j h).2]
    exact ⟨by simpa only [hc] using hj.symm, hc.symm⟩

theorem matrixGamma1CuspData_eq_iff (N : ℕ) [NeZero N] (g h : SL(2, ℤ)) :
    matrixGamma1CuspData N g = matrixGamma1CuspData N h ↔
      (⟦(g : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N)⟧ : rawGamma1Cusps N) =
        ⟦(h : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N)⟧ := by
  rw [rawGamma1Cusp_eq_iff]
  constructor
  · intro heq
    have hc := congrArg Sigma.fst heq
    change (g 1 0 : ZMod N) = (h 1 0 : ZMod N) at hc
    have ha := congrArg (fun x : Gamma1CuspData N => x.2.val.val) heq
    refine ⟨hc, ZMod.val_injective _ ?_⟩
    change (columnReduction N (g 1 0 : ZMod N) (g 0 0 : ZMod N)).val =
      (columnReduction N (h 1 0 : ZMod N) (h 0 0 : ZMod N)).val at ha
    exact ha.trans (congrArg
      (fun c => (columnReduction N c (h 0 0 : ZMod N)).val) hc).symm
  · rintro ⟨hc, ha⟩
    apply Gamma1CuspData.ext hc
    exact (congrArg ZMod.val ha).trans (congrArg
      (fun c => (columnReduction N c (h 0 0 : ZMod N)).val) hc)

/-- Every arithmetic label is represented by an integral determinant-one matrix.
The only lifting input is surjectivity on units for a divisor of the level. -/
theorem matrixGamma1CuspData_surjective (N : ℕ) [NeZero N] :
    Function.Surjective (matrixGamma1CuspData N) := by
  rintro ⟨c, a⟩
  let u : (ZMod (columnGcd N c))ˣ := ZMod.unitOfCoprime a.val.val a.property.symm
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective (Nat.gcd_dvd_right c.val N) u
  obtain ⟨D, hD⟩ := CongruenceIndex.diagonalMap_surjective N v⁻¹
  have hDc : ((D : SL(2, ℤ)) 1 0 : ZMod N) = 0 :=
    CongruenceSubgroup.Gamma0_mem.mp D.property
  have hDd : ((D : SL(2, ℤ)) 1 1 : ZMod N) = (v⁻¹ : (ZMod N)ˣ) :=
    congrArg Units.val hD
  have hdet := congrArg (Int.cast : ℤ → ZMod N) (D : SL(2, ℤ)).det_coe
  simp only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one,
    hDc, hDd, mul_zero, sub_zero] at hdet
  have hDa : ((D : SL(2, ℤ)) 0 0 : ZMod N) = (v : ZMod N) := by
    calc
      _ = (((D : SL(2, ℤ)) 0 0 : ZMod N) * (v⁻¹ : (ZMod N)ˣ)) * v := by
        simp only [mul_assoc, Units.inv_mul, mul_one]
      _ = v := by rw [hdet, one_mul]
  let t : ℕ := (c * (v⁻¹ : (ZMod N)ˣ)).val
  let g : SL(2, ℤ) := CongruenceIndex.lowU 1 t * (D : SL(2, ℤ))
  have hga : (g 0 0 : ZMod N) = (v : ZMod N) := by
    simp [g, CongruenceIndex.lowU, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, hDa]
  have hgc : (g 1 0 : ZMod N) = c := by
    simp [g, CongruenceIndex.lowU, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, hDc, hDa, t, mul_assoc]
  refine ⟨g, Gamma1CuspData.ext hgc ?_⟩
  change (columnReduction N (g 1 0 : ZMod N) (g 0 0 : ZMod N)).val = a.val.val
  rw [hgc, hga]
  have hr : columnReduction N c (v : ZMod N) = (a.val.val : ZMod (columnGcd N c)) := by
    have hh := congrArg Units.val hv
    simpa only [columnReduction, ZMod.castHom_apply, ZMod.unitsMap_val,
      u, ZMod.coe_unitOfCoprime] using hh
  rw [hr, ZMod.val_natCast, Nat.mod_eq_of_lt a.val.isLt]

/-- Every unimodular residue column lifts to the first column of an integral
determinant-one matrix. This needs no external matrix-lifting theorem. -/
theorem exists_SL2_firstColumn (N : ℕ) [NeZero N] (a c : ZMod N)
    (hprim : ∃ x y : ZMod N, a * x + c * y = 1) :
    ∃ g : SL(2, ℤ), (g 0 0 : ZMod N) = a ∧ (g 1 0 : ZMod N) = c := by
  obtain ⟨x, y, hxy⟩ := hprim
  have hunit : columnReduction N c a * columnReduction N c x = 1 := by
    have hh := congrArg (columnReduction N c) hxy
    rw [map_add, map_mul, map_mul, map_one, columnReduction_self, zero_mul, add_zero] at hh
    exact hh
  let u := Units.mkOfMulEqOne (columnReduction N c a) (columnReduction N c x) hunit
  let data : Gamma1CuspData N :=
    ⟨c, ⟨⟨u.val.val, ZMod.val_lt _⟩, (ZMod.val_coe_unit_coprime u).symm⟩⟩
  obtain ⟨g, hg⟩ := matrixGamma1CuspData_surjective N data
  have hc : (g 1 0 : ZMod N) = c := congrArg Sigma.fst hg
  have hv := congrArg (fun t : Gamma1CuspData N => t.2.val.val) hg
  change (columnReduction N (g 1 0 : ZMod N) (g 0 0 : ZMod N)).val =
    (columnReduction N c a).val at hv
  have hr : columnReduction N c (g 0 0 : ZMod N) = columnReduction N c a := by
    apply ZMod.val_injective _
    exact (congrArg (fun t => (columnReduction N t (g 0 0 : ZMod N)).val) hc).symm.trans hv
  obtain ⟨j, hj⟩ := (columnReduction_eq_iff N c a (g 0 0 : ZMod N)).mp hr.symm
  refine ⟨ModularGroup.T ^ j * g, ?_, ?_⟩
  · simpa only [(T_zpow_mul_firstColumn N j g).1, hc] using hj.symm
  · exact (T_zpow_mul_firstColumn N j g).2.trans hc

/-- The arithmetic label of a congruence coset. -/
def cosetGamma1CuspData (N : ℕ) [NeZero N] :
    (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N) → Gamma1CuspData N :=
  Quotient.lift (matrixGamma1CuspData N) (by
    intro g h hgh
    apply (matrixGamma1CuspData_eq_iff N g h).mpr
    exact congrArg (fun q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N =>
      (⟦q⟧ : rawGamma1Cusps N)) (Quotient.sound hgh))

/-- The arithmetic label as a function on the actual translation orbits. -/
def rawGamma1CuspData (N : ℕ) [NeZero N] : rawGamma1Cusps N → Gamma1CuspData N :=
  Quotient.lift (cosetGamma1CuspData N) (by
    intro q r hqr
    induction q using QuotientGroup.induction_on with
    | H g =>
      induction r using QuotientGroup.induction_on with
      | H h => exact (matrixGamma1CuspData_eq_iff N g h).mpr (Quotient.sound hqr))

theorem rawGamma1CuspData_bijective (N : ℕ) [NeZero N] :
    Function.Bijective (rawGamma1CuspData N) := by
  constructor
  · intro q r hqr
    induction q using Quotient.inductionOn with
    | h q =>
      induction r using Quotient.inductionOn with
      | h r =>
        induction q using QuotientGroup.induction_on with
        | H g =>
          induction r using QuotientGroup.induction_on with
          | H h => exact (matrixGamma1CuspData_eq_iff N g h).mp hqr
  · intro x
    obtain ⟨g, hg⟩ := matrixGamma1CuspData_surjective N x
    exact ⟨⟦(g : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N)⟧, hg⟩

private theorem card_coprime_fin (d : ℕ) :
    Nat.card {a : Fin d // d.Coprime a.val} = d.totient := by
  let e : {a : Fin d // d.Coprime a.val} ≃ {a : ℕ // a < d ∧ d.Coprime a} :=
    { toFun := fun a => ⟨a.val.val, a.val.isLt, a.property⟩
      invFun := fun a => ⟨⟨a.val, a.property.1⟩, a.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (Nat.totient_eq_card_lt_and_coprime d).symm

/-- The unprojectivized cusp count is a sum over possible lower entries. -/
theorem rawGamma1Cusps_card_eq_sum (N : ℕ) [NeZero N] :
    Nat.card (rawGamma1Cusps N) = ∑ c : ZMod N, (columnGcd N c).totient := by
  rw [Nat.card_eq_of_bijective _ (rawGamma1CuspData_bijective N),
    Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp_rw [← Nat.card_eq_fintype_card, card_coprime_fin]

/-- Grouping lower entries by their gcd gives the classical totient convolution. -/
theorem rawGamma1Cusps_card (N : ℕ) [NeZero N] :
    Nat.card (rawGamma1Cusps N) = gamma1CuspSum N := by
  rw [rawGamma1Cusps_card_eq_sum]
  have hfin : (∑ c : ZMod N, (columnGcd N c).totient) =
      ∑ a ∈ Finset.range N, (N.gcd a).totient := by
    apply Finset.sum_bij (fun c _ => c.val)
    · intro c hc
      exact Finset.mem_range.mpr (ZMod.val_lt c)
    · intro c hc d hd hcd
      exact ZMod.val_injective N hcd
    · intro a ha
      exact ⟨(a : ZMod N), Finset.mem_univ _, by
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ha)]⟩
    · intro c hc
      simp only [columnGcd, Nat.gcd_comm]
  rw [hfin, gamma1CuspSum]
  have hmap : ∀ a ∈ Finset.range N, N.gcd a ∈ N.divisors := by
    intro a ha
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left N a, NeZero.ne N⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_congr rfl
  intro d hd
  have ht := Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd)
  calc
    (∑ a ∈ Finset.filter (fun a => N.gcd a = d) (Finset.range N), (N.gcd a).totient) =
        (Finset.filter (fun a => N.gcd a = d) (Finset.range N)).card * d.totient := by
      simp only [Finset.sum_congr rfl (fun a ha =>
        congrArg Nat.totient (Finset.mem_filter.mp ha).2), Finset.sum_const,
        nsmul_eq_mul, Nat.cast_id]
    _ = d.totient * (N / d).totient := by rw [← ht, mul_comm]

/-- The actual projective cusp quotient, without analytic imports. -/
abbrev projectiveGamma1Cusps (N : ℕ) :=
  MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.T)
    (SL(2, ℤ) ⧸ projectiveClosure (CongruenceSubgroup.Gamma1 N))

/-- The natural map of congruence cosets after adjoining `-I`. -/
def gamma1ProjectiveCosetMap (N : ℕ) :
    (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N) →
      SL(2, ℤ) ⧸ projectiveClosure (CongruenceSubgroup.Gamma1 N) :=
  Quotient.lift (fun g => (g : SL(2, ℤ) ⧸ projectiveClosure (CongruenceSubgroup.Gamma1 N)))
    (by
      intro g h hgh
      exact QuotientGroup.eq.mpr ((show CongruenceSubgroup.Gamma1 N ≤
        projectiveClosure (CongruenceSubgroup.Gamma1 N) from le_sup_left)
        (QuotientGroup.eq.mp (show (g : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N) = h from
          Quotient.sound hgh))))

theorem gamma1ProjectiveCosetMap_smul (N : ℕ) (u : SL(2, ℤ))
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N) :
    gamma1ProjectiveCosetMap N (u • q) = u • gamma1ProjectiveCosetMap N q := by
  induction q using QuotientGroup.induction_on with
  | H g => rfl

/-- The natural map from raw cusp orbits to the genuine projective cusps. -/
def gamma1ProjectiveCuspMap (N : ℕ) : rawGamma1Cusps N → projectiveGamma1Cusps N :=
  Quotient.lift (fun q => (⟦gamma1ProjectiveCosetMap N q⟧ : projectiveGamma1Cusps N)) (by
    intro q r hqr
    apply Quotient.sound
    obtain ⟨u, hu⟩ := MulAction.orbitRel_apply.mp hqr
    apply MulAction.orbitRel_apply.mpr
    refine ⟨u, ?_⟩
    change (u.val • gamma1ProjectiveCosetMap N r) = gamma1ProjectiveCosetMap N q
    rw [← gamma1ProjectiveCosetMap_smul]
    exact congrArg (gamma1ProjectiveCosetMap N) hu)

/-- Adjoining sign merges precisely the two raw cusp classes represented by `h` and `-h`. -/
theorem projectiveGamma1Cusp_eq_iff (N : ℕ) (g h : SL(2, ℤ)) :
    (⟦(g : SL(2, ℤ) ⧸ projectiveClosure (CongruenceSubgroup.Gamma1 N))⟧ :
      projectiveGamma1Cusps N) = ⟦(h : SL(2, ℤ) ⧸ _)⟧ ↔
    (⟦(g : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N)⟧ : rawGamma1Cusps N) = ⟦(h : SL(2, ℤ) ⧸ _)⟧ ∨
    (⟦(g : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N)⟧ : rawGamma1Cusps N) =
      ⟦((-h : SL(2, ℤ)) : SL(2, ℤ) ⧸ _)⟧ := by
  simp only [Quotient.eq, MulAction.orbitRel_apply]
  constructor
  · rintro ⟨u, hu⟩
    change u.val • (h : SL(2, ℤ) ⧸ projectiveClosure (CongruenceSubgroup.Gamma1 N)) = _ at hu
    rw [MulAction.Quotient.smul_coe, smul_eq_mul, gamma1_projective_coset_eq_iff] at hu
    rcases hu with hu | hu
    · left
      refine ⟨u, ?_⟩
      change u.val • (h : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N) = _
      rw [MulAction.Quotient.smul_coe, smul_eq_mul, gamma1_coset_eq_iff]
      exact hu
    · right
      refine ⟨u, ?_⟩
      change u.val • ((-h : SL(2, ℤ)) : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N) = _
      rw [MulAction.Quotient.smul_coe, smul_eq_mul, gamma1_coset_eq_iff]
      simpa [mul_neg] using And.intro (congrArg Neg.neg hu.1) (congrArg Neg.neg hu.2)
  · rintro (⟨u, hu⟩ | ⟨u, hu⟩)
    · refine ⟨u, ?_⟩
      change u.val • (h : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N) = _ at hu
      rw [MulAction.Quotient.smul_coe, smul_eq_mul, gamma1_coset_eq_iff] at hu
      change u.val • (h : SL(2, ℤ) ⧸ projectiveClosure (CongruenceSubgroup.Gamma1 N)) = _
      rw [MulAction.Quotient.smul_coe, smul_eq_mul, gamma1_projective_coset_eq_iff]
      exact Or.inl hu
    · refine ⟨u, ?_⟩
      change u.val • ((-h : SL(2, ℤ)) : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N) = _ at hu
      rw [MulAction.Quotient.smul_coe, smul_eq_mul, gamma1_coset_eq_iff] at hu
      change u.val • (h : SL(2, ℤ) ⧸ projectiveClosure (CongruenceSubgroup.Gamma1 N)) = _
      rw [MulAction.Quotient.smul_coe, smul_eq_mul, gamma1_projective_coset_eq_iff]
      right
      simpa [mul_neg] using And.intro (congrArg Neg.neg hu.1) (congrArg Neg.neg hu.2)

/-- The sign involution has no fixed raw cusp at levels at least five. -/
theorem rawGamma1Cusp_ne_neg (N : ℕ) (hN : 5 ≤ N) (g : SL(2, ℤ)) :
    (⟦(g : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N)⟧ : rawGamma1Cusps N) ≠
      ⟦((-g : SL(2, ℤ)) : SL(2, ℤ) ⧸ _)⟧ := by
  let : NeZero N := ⟨by omega⟩
  intro heq
  obtain ⟨hc, ha⟩ := (rawGamma1Cusp_eq_iff N g (-g)).mp heq
  obtain ⟨j, hj⟩ := (columnReduction_eq_iff N (g 1 0 : ZMod N) _ _).mp ha
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg] at hc hj
  have hc2 : (2 : ZMod N) * (g 1 0 : ZMod N) = 0 := by linear_combination hc
  have ha4 : (4 : ZMod N) * (g 0 0 : ZMod N) = 0 := by
    linear_combination 2 * hj + (j : ZMod N) * hc2
  have hd := congrArg (Int.cast : ℤ → ZMod N) g.det_coe
  simp only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one] at hd
  have hfour : (4 : ZMod N) = 0 := by
    linear_combination (g 1 1 : ZMod N) * ha4 -
      2 * (g 0 1 : ZMod N) * hc2 - 4 * hd
  have hdiv : N ∣ 4 := (ZMod.natCast_eq_zero_iff _ _).mp hfour
  have := Nat.le_of_dvd (by decide : 0 < 4) hdiv
  omega

private theorem gamma1ProjectiveCuspMap_fiber_card (N : ℕ) (hN : 5 ≤ N)
    (y : projectiveGamma1Cusps N) :
    Nat.card {x : rawGamma1Cusps N // gamma1ProjectiveCuspMap N x = y} = 2 := by
  induction y using Quotient.inductionOn with
  | h q =>
    induction q using QuotientGroup.induction_on with
    | H g =>
      let a : rawGamma1Cusps N := ⟦(g : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N)⟧
      let b : rawGamma1Cusps N := ⟦((-g : SL(2, ℤ)) : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N)⟧
      have ha : gamma1ProjectiveCuspMap N a = ⟦(g : SL(2, ℤ) ⧸ _)⟧ := rfl
      have hb : gamma1ProjectiveCuspMap N b = ⟦(g : SL(2, ℤ) ⧸ _)⟧ := by
        exact (projectiveGamma1Cusp_eq_iff N (-g) g).mpr (Or.inr rfl)
      apply Nat.card_eq_two_iff.mpr
      refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_, Set.eq_univ_iff_forall.mpr ?_⟩
      · intro hab
        exact rawGamma1Cusp_ne_neg N hN g (congrArg Subtype.val hab)
      · rintro ⟨x, hx⟩
        have hcases : x = a ∨ x = b := by
          induction x using Quotient.inductionOn with
          | h r =>
            induction r using QuotientGroup.induction_on with
            | H h => exact (projectiveGamma1Cusp_eq_iff N h g).mp hx
        rcases hcases with h | h
        · exact Set.mem_insert_iff.mpr (Or.inl (Subtype.ext h))
        · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr (Subtype.ext h)))

/-- For `N ≥ 5`, passage to the projective cusp quotient divides the cardinality by two. -/
theorem two_mul_projectiveGamma1Cusps_card (N : ℕ) (hN : 5 ≤ N) :
    2 * Nat.card (projectiveGamma1Cusps N) = Nat.card (rawGamma1Cusps N) := by
  let : NeZero N := ⟨by omega⟩
  let : Fintype (projectiveGamma1Cusps N) := Fintype.ofFinite _
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (gamma1ProjectiveCuspMap N)), Nat.card_sigma]
  simp only [gamma1ProjectiveCuspMap_fiber_card N hN, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
  omega

/-- The classical arithmetic cusp count for `Γ₁(N)`, with the sign exception excluded. -/
theorem two_mul_projectiveGamma1Cusps_card_eq_cuspSum (N : ℕ) (hN : 5 ≤ N) :
    2 * Nat.card (projectiveGamma1Cusps N) = gamma1CuspSum N := by
  let : NeZero N := ⟨by omega⟩
  rw [two_mul_projectiveGamma1Cusps_card N hN, rawGamma1Cusps_card]

end WeightTwoCusps
