module

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.Tactic.NormNum.LegendreSymbol

/-!
# The signed Jacobi symbol for eta multipliers

The denominator in the eta multiplier formula is an odd integer, which may
be negative. We use Savitt's Appendix A convention, including `(0 / -1) = 1`.
The definition is computable and agrees with Mathlib's Jacobi symbol at
nonnegative denominators. The arithmetic multiplier formula itself is not
assumed here.

Reference: D. Savitt, *An elementary proof of Newman's eta-quotient theorem*,
Appendix A, <https://math.jhu.edu/~savitt/papers/pdfs/newman.pdf>.
-/

@[expose] public section

open scoped MatrixGroups

namespace WeightTwoCusps.EtaQuotient

/-- Jacobi symbol with signed denominator. Its classical use requires an odd
denominator. Zero numerators have sign `+1` here, giving the convention
`extendedJacobi 0 (-1) = 1`. -/
def extendedJacobi (a d : ℤ) : ℤ :=
  if d < 0 ∧ a < 0 then -jacobiSym a d.natAbs else jacobiSym a d.natAbs

namespace extendedJacobi

@[simp] theorem natCast (a : ℤ) (d : ℕ) :
    extendedJacobi a d = jacobiSym a d := by
  simp [extendedJacobi]

theorem of_nonneg {a d : ℤ} (hd : 0 ≤ d) :
    extendedJacobi a d = jacobiSym a d.natAbs := by
  simp [extendedJacobi, not_lt_of_ge hd]

theorem of_nonneg_left {a d : ℤ} (ha : 0 ≤ a) :
    extendedJacobi a d = jacobiSym a d.natAbs := by
  simp [extendedJacobi, not_lt_of_ge ha]

theorem of_neg {a d : ℤ} (hd : d < 0) (ha : a ≠ 0) :
    extendedJacobi a d = a.sign * jacobiSym a d.natAbs := by
  rcases lt_or_gt_of_ne ha with h | h
  · simp [extendedJacobi, hd, h, Int.sign_eq_neg_one_of_neg h]
  · simp [extendedJacobi, hd, not_lt_of_ge h.le, Int.sign_eq_one_of_pos h]

@[simp] theorem one_right (a : ℤ) : extendedJacobi a 1 = 1 := by
  simp [extendedJacobi]

@[simp] theorem zero_one : extendedJacobi 0 1 = 1 := one_right 0

@[simp] theorem zero_neg_one : extendedJacobi 0 (-1) = 1 := by
  simp [extendedJacobi]

@[simp] theorem one_left (d : ℤ) : extendedJacobi 1 d = 1 := by
  simp [extendedJacobi]

theorem neg_one_right_of_ne_zero {a : ℤ} (ha : a ≠ 0) :
    extendedJacobi a (-1) = a.sign := by
  rw [of_neg (by norm_num) ha]
  simp

theorem eq_one_or_neg_one {a d : ℤ} (h : a.gcd d = 1) :
    extendedJacobi a d = 1 ∨ extendedJacobi a d = -1 := by
  have hj : jacobiSym a d.natAbs = 1 ∨ jacobiSym a d.natAbs = -1 := by
    apply jacobiSym.eq_one_or_neg_one
    simpa only [Int.gcd, Int.natAbs_natCast] using h
  unfold extendedJacobi
  split_ifs <;> rcases hj with hj | hj <;> simp [hj]

theorem sq_eq_one {a d : ℤ} (h : a.gcd d = 1) :
    extendedJacobi a d ^ 2 = 1 := by
  rcases eq_one_or_neg_one h with h | h <;> simp [h]

theorem ne_zero {a d : ℤ} (h : a.gcd d = 1) : extendedJacobi a d ≠ 0 := by
  rcases eq_one_or_neg_one h with h | h <;> simp [h]

/-- Multiplicativity with no zero-numerator exceptions. -/
theorem mul_left {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (d : ℤ) :
    extendedJacobi (a * b) d = extendedJacobi a d * extendedJacobi b d := by
  by_cases hd : d < 0
  · rw [of_neg hd (mul_ne_zero ha hb), of_neg hd ha, of_neg hd hb,
      Int.sign_mul, jacobiSym.mul_left]
    ring
  · simp only [extendedJacobi, hd, false_and, ↓reduceIte, jacobiSym.mul_left]

/-- The numerator may be reduced modulo the denominator when the denominator
is nonnegative, or when the numerator signs agree. This retains the sign
condition needed at negative denominators. -/
theorem congr_left {a b d : ℤ} (hmod : a ≡ b [ZMOD d])
    (hsign : d < 0 → (a < 0 ↔ b < 0)) :
    extendedJacobi a d = extendedJacobi b d := by
  have hj : jacobiSym a d.natAbs = jacobiSym b d.natAbs :=
    jacobiSym.mod_left' (Int.modEq_natAbs.mpr hmod)
  unfold extendedJacobi
  rw [hj]
  by_cases hd : d < 0
  · simp [hd, hsign hd]
  · simp [hd]

theorem at_neg_one {d : ℤ} (hd : Odd d) :
    extendedJacobi (-1) d = ZMod.χ₄ d := by
  have habs : Odd d.natAbs := hd.natAbs
  rw [extendedJacobi, jacobiSym.at_neg_one habs]
  by_cases h : d < 0
  · have he : (d.natAbs : ℤ) = -d := Int.ofNat_natAbs_of_nonpos h.le
    simp only [h, neg_lt_zero, zero_lt_one, and_self, ↓reduceIte]
    rw [show (d.natAbs : ZMod 4) = (-d : ℤ) by
      simpa only [Int.cast_natCast] using congrArg (fun z : ℤ ↦ (z : ZMod 4)) he,
      Int.cast_neg]
    rw [show -(d : ZMod 4) = (-1) * (d : ZMod 4) from (neg_one_mul _).symm,
      map_mul, show ZMod.χ₄ (-1) = -1 from by decide]
    ring
  · have he : (d.natAbs : ℤ) = d := Int.natAbs_of_nonneg (by omega)
    simp only [h, false_and, ↓reduceIte]
    exact congrArg ZMod.χ₄ (by
      simpa only [Int.cast_natCast] using congrArg (fun z : ℤ ↦ (z : ZMod 4)) he)

theorem at_two {d : ℤ} (hd : Odd d) :
    extendedJacobi 2 d = ZMod.χ₈ d := by
  rw [of_nonneg_left (by norm_num), jacobiSym.at_two (hd.natAbs)]
  rcases le_or_gt 0 d with h | h
  · exact congrArg ZMod.χ₈ (by
      simpa only [Int.cast_natCast] using
        congrArg (fun z : ℤ ↦ (z : ZMod 8)) (Int.natAbs_of_nonneg h))
  · have he : (d.natAbs : ℤ) = -d := Int.ofNat_natAbs_of_nonpos h.le
    rw [show (d.natAbs : ZMod 8) = (-d : ℤ) by
      simpa only [Int.cast_natCast] using congrArg (fun z : ℤ ↦ (z : ZMod 8)) he,
      Int.cast_neg]
    rw [show -(d : ZMod 8) = (-1) * (d : ZMod 8) from (neg_one_mul _).symm,
      map_mul, show ZMod.χ₈ (-1) = 1 from by decide, one_mul]

/-- Quadratic reciprocity with positive odd numerator and signed odd
denominator. The sign only depends on the two residues modulo four. -/
theorem quadratic_reciprocity_nat {a : ℕ} (ha : Odd a) {d : ℤ} (hd : Odd d) :
    extendedJacobi a d =
      (if a % 4 = 3 ∧ d % 4 = 3 then -1 else 1) * jacobiSym d a := by
  have habs : Odd d.natAbs := hd.natAbs
  rw [of_nonneg_left (by positivity)]
  have hj := (jacobiSym.quadratic_reciprocity_if (Nat.odd_iff.mp ha)
    (Nat.odd_iff.mp habs)).symm
  by_cases h : 0 ≤ d
  · have he : (d.natAbs : ℤ) = d := Int.natAbs_of_nonneg h
    rw [hj]
    have hm : (d.natAbs % 4 = 3) ↔ d % 4 = 3 := by omega
    simp only [hm, he]
    split_ifs <;> ring
  · have he : d = -(d.natAbs : ℤ) := by omega
    rw [hj]
    have hneg : jacobiSym d a = ZMod.χ₄ a * jacobiSym (d.natAbs : ℤ) a := by
      calc
        jacobiSym d a = jacobiSym (-(d.natAbs : ℤ)) a := congrArg (fun n ↦ jacobiSym n a) he
        _ = _ := jacobiSym.neg _ ha
    rw [hneg, ZMod.χ₄_nat_eq_if_mod_four]
    have ha2 := Nat.odd_iff.mp ha
    have hd2 := Int.odd_iff.mp hd
    have hh : (d.natAbs : ℤ) = -d := Int.ofNat_natAbs_of_nonpos (by omega)
    have ha4 : a % 4 = 1 ∨ a % 4 = 3 := Nat.odd_mod_four_iff.mp ha2
    rcases ha4 with ha4 | ha4
    · simp [ha2, ha4]
    · have hr : (d.natAbs % 4 = 3) ↔ d % 4 = 1 := by omega
      simp only [ha2, ha4, Nat.one_ne_zero, ↓reduceIte, true_and, hr]
      have hd4 : d % 4 = 1 ∨ d % 4 = 3 := by omega
      rcases hd4 with hd4 | hd4 <;> simp [hd4]

/-- Signed denominator periodicity for an odd natural numerator. -/
theorem congr_right_odd_nat {a : ℕ} (ha : Odd a) {d e : ℤ} (hd : Odd d) (he : Odd e)
    (hmod : d ≡ e [ZMOD 4 * a]) : extendedJacobi a d = extendedJacobi a e := by
  rw [quadratic_reciprocity_nat ha hd, quadratic_reciprocity_nat ha he]
  have hm4 : d % 4 = e % 4 := hmod.of_dvd (dvd_mul_right (4 : ℤ) a)
  have hma : d % (a : ℤ) = e % (a : ℤ) := hmod.of_dvd (dvd_mul_left (a : ℤ) 4)
  rw [hm4, jacobiSym.mod_left' hma]

/-- Denominator periodicity for any natural numerator and signed odd
denominators, including a change of denominator sign. -/
theorem congr_right_nat (a : ℕ) {d e : ℤ} (hd : Odd d) (he : Odd e)
    (hmod : d ≡ e [ZMOD 4 * a]) : extendedJacobi a d = extendedJacobi a e := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    by_cases ha0 : a = 0
    · subst a
      have hde : d = e := by simpa [Int.ModEq] using hmod
      rw [hde]
    rcases Nat.even_or_odd a with ha | ha
    · have ha2 := Nat.even_iff.mp ha
      let b := a / 2
      have hab : a = 2 * b := by omega
      have hb0 : b ≠ 0 := by omega
      have hb : (b : ℤ) ≠ 0 := by exact_mod_cast hb0
      have hm8 : d ≡ e [ZMOD 8] := hmod.of_dvd ⟨b, by rw [hab]; push_cast; ring⟩
      have hmb : d ≡ e [ZMOD 4 * b] :=
        hmod.of_dvd ⟨2, by rw [hab]; push_cast; ring⟩
      have hχ : ZMod.χ₈ d = ZMod.χ₈ e := by
        rw [ZMod.χ₈_int_mod_eight d, ZMod.χ₈_int_mod_eight e, hm8]
      have hi := ih b (by omega) hmb
      rw [hab, Nat.cast_mul, Nat.cast_ofNat, extendedJacobi.mul_left (by norm_num) hb,
        extendedJacobi.mul_left (by norm_num) hb, at_two hd, at_two he, hχ, hi]
    · exact congr_right_odd_nat ha hd he hmod

/-- Signed Jacobi symbols depend only on the denominator modulo four times
the absolute value of the numerator. This is Savitt's Proposition A.3(7). -/
theorem congr_right {a d e : ℤ} (hd : Odd d) (he : Odd e)
    (hmod : d ≡ e [ZMOD 4 * a.natAbs]) : extendedJacobi a d = extendedJacobi a e := by
  by_cases ha : 0 ≤ a
  · have heq : (a.natAbs : ℤ) = a := Int.natAbs_of_nonneg ha
    simpa only [heq] using congr_right_nat a.natAbs hd he hmod
  · have heq : a = (-1) * (a.natAbs : ℤ) := by
      rw [neg_one_mul, Int.ofNat_natAbs_of_nonpos (by omega), neg_neg]
    have ha0 : (a.natAbs : ℤ) ≠ 0 := by omega
    have hm4 : d ≡ e [ZMOD 4] := hmod.of_dvd (dvd_mul_right _ _)
    have hχ : ZMod.χ₄ d = ZMod.χ₄ e := by
      rw [ZMod.χ₄_int_mod_four d, ZMod.χ₄_int_mod_four e, hm4]
    have hi := congr_right_nat a.natAbs hd he hmod
    have hleft := extendedJacobi.mul_left (a := -1) (b := (a.natAbs : ℤ)) (by norm_num) ha0
    calc
      extendedJacobi a d = extendedJacobi (-1) d * extendedJacobi a.natAbs d := by
        conv_lhs => rw [heq]
        exact hleft d
      _ = extendedJacobi (-1) e * extendedJacobi a.natAbs e := by
        rw [at_neg_one hd, at_neg_one he, hi, hχ]
      _ = extendedJacobi a e := by
        rw [← hleft]
        congr 1
        exact heq.symm

theorem neg_left {a d : ℤ} (ha : a ≠ 0) (hd : Odd d) :
    extendedJacobi (-a) d = ZMod.χ₄ d * extendedJacobi a d := by
  simpa only [neg_one_mul, at_neg_one hd] using
    mul_left (a := -1) (by norm_num) ha d

theorem neg_right {a d : ℤ} (ha : a ≠ 0) (hd : d ≠ 0) :
    extendedJacobi a (-d) = a.sign * extendedJacobi a d := by
  rcases lt_or_gt_of_ne ha with ha | ha
  · rw [Int.sign_eq_neg_one_of_neg ha]
    rcases lt_or_gt_of_ne hd with hd | hd
    · simp [extendedJacobi, ha, hd, hd.not_gt]
    · simp [extendedJacobi, ha, hd, hd.not_gt]
  · simp [extendedJacobi, ha.not_gt, Int.sign_eq_one_of_pos ha]

/-- The simultaneous-negation identity required for the `-I` generator in
the arithmetic eta multiplier formula. -/
theorem neg_neg {a d : ℤ} (ha : a ≠ 0) (hd : Odd d) :
    extendedJacobi (-a) (-d) = a.sign * ZMod.χ₄ (-d) * extendedJacobi a d := by
  have hd0 : d ≠ 0 := by
    intro h
    subst d
    simp at hd
  rw [neg_right (neg_ne_zero.mpr ha) hd0, neg_left ha hd, Int.sign_neg,
    show -(d : ZMod 4) = (-1) * (d : ZMod 4) from (neg_one_mul _).symm,
    map_mul, show ZMod.χ₄ (-1) = -1 from by decide]
  ring

end extendedJacobi

/-- For a determinant-one matrix with positive upper-left entry and nonzero
upper-right entry, the lower-row symbol can be read from the upper-right
entry. The positivity is exactly what controls numerator signs at negative
denominators in Savitt's Lemma 4.9. -/
theorem extendedJacobi_eq_neg_upperRight {a b c d : ℤ} (ha : 0 < a) (hb : b ≠ 0)
    (hdet : a * d - b * c = 1) : extendedJacobi c d = extendedJacobi (-b) d := by
  by_cases hc : c = 0
  · have hmul : a * d = 1 := by simpa [hc] using hdet
    have hd : d = 1 := by
      rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hmul with h | h <;> omega
    simp [hd]
  have hcop : IsCoprime b d := ⟨-c, a, by nlinarith [hdet]⟩
  have hsq := extendedJacobi.sq_eq_one (Int.isCoprime_iff_gcd_eq_one.mp hcop)
  have he : extendedJacobi (b * c) d = extendedJacobi (-1) d := by
    apply extendedJacobi.congr_left
    · apply Int.modEq_iff_dvd.mpr
      exact ⟨-a, by nlinarith [hdet]⟩
    · intro hd
      have hp : a * d < 0 := mul_neg_of_pos_of_neg ha hd
      constructor <;> intro _ <;> omega
  rw [extendedJacobi.mul_left hb hc] at he
  calc
    extendedJacobi c d = extendedJacobi (-1) d * extendedJacobi b d := by
      calc
        _ = (extendedJacobi b d ^ 2) * extendedJacobi c d := by rw [hsq, one_mul]
        _ = (extendedJacobi b d * extendedJacobi c d) * extendedJacobi b d := by ring
        _ = _ := by rw [he]
    _ = extendedJacobi (-b) d := by
      simpa only [neg_one_mul] using
        (extendedJacobi.mul_left (a := -1) (by norm_num) hb d).symm

/-- Savitt's Lemma 4.9: left multiplication by the lower translation of
length four preserves the Jacobi factor when the upper-left entry is
positive. The odd denominator hypothesis follows from `4 ∣ c` and `det = 1`
when this lemma is applied on `Γ₀(4)`. -/
theorem extendedJacobi_lower_four {a b c d : ℤ} (ha : 0 < a) (hd : Odd d)
    (hdet : a * d - b * c = 1) :
    extendedJacobi (c + 4 * a) (d + 4 * b) = extendedJacobi c d := by
  by_cases hb : b = 0
  · subst b
    have hmul : a * d = 1 := by simpa using hdet
    have hd1 : d = 1 := by
      rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hmul with h | h <;> omega
    simp [hd1]
  have hd' : Odd (d + 4 * b) := hd.add_even ⟨2 * b, by ring⟩
  rw [extendedJacobi_eq_neg_upperRight ha hb (by nlinarith [hdet]),
    extendedJacobi_eq_neg_upperRight ha hb hdet]
  apply extendedJacobi.congr_right hd' hd
  apply Int.modEq_iff_dvd.mpr
  have heq : (b.natAbs : ℤ) = b ∨ (b.natAbs : ℤ) = -b := by
    rcases Int.natAbs_eq b with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by omega)
  rcases heq with heq | heq
  · exact ⟨-1, by simp only [Int.natAbs_neg, heq]; ring⟩
  · exact ⟨1, by simp only [Int.natAbs_neg, heq]; ring⟩

/-- The symbol in the arithmetic eta multiplier is a sign at every modular
matrix, including a vanishing lower-left entry and denominator `-1`. -/
theorem extendedJacobi_matrix_sq (γ : SL(2, ℤ)) :
    extendedJacobi (γ 1 0) (γ 1 1) ^ 2 = 1 :=
  extendedJacobi.sq_eq_one
    (Int.isCoprime_iff_gcd_eq_one.mp (Matrix.SpecialLinearGroup.isCoprime_row γ 1))

end WeightTwoCusps.EtaQuotient

