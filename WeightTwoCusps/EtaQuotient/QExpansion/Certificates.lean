module

public import WeightTwoCusps.EtaQuotient.QExpansion.Computable
public import WeightTwoCusps.QExpansion

/-!
# Finite certificates for coefficient computation

Intermediate coefficient tables keep numeral proofs from repeatedly expanding
nested convolutions. Every table is checked by finite integer equalities;
these lemmas propagate those certificates to the original coefficient formula.
-/

@[expose] public section

namespace WeightTwoCusps.EtaQuotient

/-- Read an integer coefficient table, extending it by zero. -/
def tableCoefficient (t : List ℤ) (n : ℕ) : ℤ := t[n]?.getD 0

/-- Agreement with a coefficient table through the requested finite precision. -/
def IsCoefficientTable (a : ℕ → ℤ) (p : ℕ) (t : List ℤ) : Prop :=
  ∀ n : Fin p, a n = tableCoefficient t n
deriving Decidable

/-- Check a table sequentially, without repeatedly indexing its prefix. -/
def checkCoefficientPrefix (a : ℕ → ℤ) : ℕ → ℕ → List ℤ → Bool
  | _, 0, _ => true
  | k, p + 1, t => a k == t.headD 0 && checkCoefficientPrefix a (k + 1) p t.tail

theorem checkCoefficientPrefix_sound {a : ℕ → ℤ} {k p : ℕ} {t : List ℤ}
    (h : checkCoefficientPrefix a k p t = true) (n : ℕ) (hn : n < p) :
    a (k + n) = tableCoefficient t n := by
  induction p generalizing k t n with
  | zero => omega
  | succ p ih =>
    simp only [checkCoefficientPrefix, Bool.and_eq_true, beq_iff_eq] at h
    cases n with
    | zero => cases t <;> simpa [tableCoefficient] using h.1
    | succ n =>
      have ht (l : List ℤ) : tableCoefficient l.tail n = tableCoefficient l (n + 1) := by
        cases l <;> rfl
      simpa only [Nat.add_assoc, Nat.add_comm 1 n, ht] using ih h.2 n (by omega)

theorem coefficient_table_of_check {a : ℕ → ℤ} {p : ℕ} {t : List ℤ}
    (h : checkCoefficientPrefix a 0 p t = true) : IsCoefficientTable a p t := by
  intro n
  simpa only [Nat.zero_add] using checkCoefficientPrefix_sound h n n.isLt

theorem tableCoefficient_one (n : ℕ) : tableCoefficient [1] n = oneCoefficient n := by
  cases n <;> simp [tableCoefficient, oneCoefficient]

theorem oneCoefficient_table (p : ℕ) : IsCoefficientTable oneCoefficient p [1] :=
  fun n ↦ (tableCoefficient_one n).symm

theorem productCoefficient_table_nil (p : ℕ) :
    IsCoefficientTable (productCoefficient []) p [1] := oneCoefficient_table p

theorem eulerCoefficient_zero : eulerCoefficient 0 = 1 := by decide

theorem dilateCoefficient_table_one_of_le {a : ℕ → ℤ} {m p : ℕ}
    (h0 : a 0 = 1) (hp : p ≤ m) :
    IsCoefficientTable (dilateCoefficient m a) p [1] := by
  intro ⟨n, hn⟩
  cases n with
  | zero => simp [dilateCoefficient, h0, tableCoefficient]
  | succ n =>
    have hnm : n + 1 < m := lt_of_lt_of_le hn hp
    have hnot : ¬m ∣ n + 1 := Nat.not_dvd_of_pos_of_lt (by omega) hnm
    simp [dilateCoefficient, hnot, tableCoefficient]

theorem convolution_one_left (a : ℕ → ℤ) : convolution oneCoefficient a = a := by
  funext n
  simp [convolution, oneCoefficient]

theorem convolution_one_right (a : ℕ → ℤ) : convolution a oneCoefficient = a := by
  funext n
  simp only [convolution, oneCoefficient, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single n]
  · simp
  · intro b hb hbn
    have : b < n := by have := Finset.mem_range.mp hb; omega
    simp [Nat.ne_of_gt (Nat.sub_pos_of_lt this)]
  · simp

theorem convolution_table_one_left_values (p : ℕ) (t : List ℤ) :
    IsCoefficientTable (convolution (tableCoefficient [1]) (tableCoefficient t)) p t := by
  simp only [funext tableCoefficient_one, convolution_one_left]
  exact fun _ ↦ rfl

theorem convolution_table_one_right_values (p : ℕ) (t : List ℤ) :
    IsCoefficientTable (convolution (tableCoefficient t) (tableCoefficient [1])) p t := by
  simp only [funext tableCoefficient_one, convolution_one_right]
  exact fun _ ↦ rfl

theorem powCoefficient_add (a : ℕ → ℤ) (k l : ℕ) :
    powCoefficient a (k + l) = convolution (powCoefficient a k) (powCoefficient a l) := by
  let A : PowerSeries ℂ := PowerSeries.mk fun n ↦ (a n : ℂ)
  have hA : ∀ n, A.coeff n = (a n : ℂ) := fun n ↦ PowerSeries.coeff_mk _ _
  funext n
  apply Int.cast_injective (α := ℂ)
  rw [← powCoefficient_cast hA, ← convolution_cast
    (powCoefficient_cast hA k) (powCoefficient_cast hA l), pow_add]

/-- Finite reciprocal recurrence, containing no recursively defined coefficients. -/
def IsInverseTable (ta ti : List ℤ) (p : ℕ) : Prop :=
  ∀ n : Fin p, tableCoefficient ti n =
    if (n : ℕ) = 0 then 1 else
      - ∑ x ∈ Finset.antidiagonal (n : ℕ),
        if x.2 < (n : ℕ) then tableCoefficient ta x.1 * tableCoefficient ti x.2 else 0
deriving Decidable

theorem convolution_table {a b : ℕ → ℤ} {p : ℕ} {ta tb tc : List ℤ}
    (ha : IsCoefficientTable a p ta) (hb : IsCoefficientTable b p tb)
    (hc : IsCoefficientTable (convolution (tableCoefficient ta) (tableCoefficient tb)) p tc) :
    IsCoefficientTable (convolution a b) p tc := by
  intro n
  refine (convolution_congr ?_ ?_).trans (hc n)
  · intro k hk
    exact ha ⟨k, Nat.lt_of_le_of_lt hk n.isLt⟩
  · intro k hk
    exact hb ⟨k, Nat.lt_of_le_of_lt hk n.isLt⟩

/-- Multiplication by a prefix equal to one requires no arithmetic table. -/
theorem convolution_table_one_left {a b : ℕ → ℤ} {p : ℕ} {tb : List ℤ}
    (ha : IsCoefficientTable a p [1]) (hb : IsCoefficientTable b p tb) :
    IsCoefficientTable (convolution a b) p tb := by
  intro n
  calc
    convolution a b n = convolution oneCoefficient b n := convolution_congr
      (fun k hk ↦ (ha ⟨k, by omega⟩).trans (tableCoefficient_one k)) (fun _ _ ↦ rfl)
    _ = tableCoefficient tb n := by rw [convolution_one_left]; exact hb n

theorem convolution_table_one_right {a b : ℕ → ℤ} {p : ℕ} {ta : List ℤ}
    (ha : IsCoefficientTable a p ta) (hb : IsCoefficientTable b p [1]) :
    IsCoefficientTable (convolution a b) p ta := by
  intro n
  calc
    convolution a b n = convolution a oneCoefficient n := convolution_congr
      (fun _ _ ↦ rfl) (fun k hk ↦ (hb ⟨k, by omega⟩).trans (tableCoefficient_one k))
    _ = tableCoefficient ta n := by rw [convolution_one_right]; exact ha n

/-- Squaring certificates make natural powers logarithmic in the exponent. -/
theorem powCoefficient_table_add {a : ℕ → ℤ} {k l p : ℕ} {ta tb tc : List ℤ}
    (ha : IsCoefficientTable (powCoefficient a k) p ta)
    (hb : IsCoefficientTable (powCoefficient a l) p tb)
    (hc : IsCoefficientTable (convolution (tableCoefficient ta) (tableCoefficient tb)) p tc) :
    IsCoefficientTable (powCoefficient a (k + l)) p tc := by
  rw [powCoefficient_add]
  exact convolution_table ha hb hc

theorem powCoefficient_table_one {a : ℕ → ℤ} {p : ℕ} {t : List ℤ}
    (ha : IsCoefficientTable a p t) : IsCoefficientTable (powCoefficient a 1) p t := by
  simpa only [powCoefficient, convolution_one_right] using ha

theorem powCoefficient_table_succ {a : ℕ → ℤ} {k p : ℕ} {ta tb tc : List ℤ}
    (ha : IsCoefficientTable a p ta) (hb : IsCoefficientTable (powCoefficient a k) p tb)
    (hc : IsCoefficientTable (convolution (tableCoefficient ta) (tableCoefficient tb)) p tc) :
    IsCoefficientTable (powCoefficient a (k + 1)) p tc :=
  convolution_table ha hb hc

theorem productCoefficient_table_cons {a : ℕ → ℤ} {as : List (ℕ → ℤ)} {p : ℕ}
    {ta tb tc : List ℤ} (ha : IsCoefficientTable a p ta)
    (hb : IsCoefficientTable (productCoefficient as) p tb)
    (hc : IsCoefficientTable (convolution (tableCoefficient ta) (tableCoefficient tb)) p tc) :
    IsCoefficientTable (productCoefficient (a :: as)) p tc :=
  convolution_table ha hb hc

/-- A finite reciprocal recurrence determines all reciprocal coefficients in range. -/
theorem inverseCoefficient_table {a : ℕ → ℤ} {p : ℕ} {ta ti : List ℤ}
    (ha : IsCoefficientTable a p ta)
    (hi : IsInverseTable ta ti p) :
    IsCoefficientTable (inverseCoefficient a) p ti := by
  intro ⟨n, hn⟩
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [inverseCoefficient, hi ⟨n, hn⟩]
    split_ifs with hn0
    · rfl
    · congr 1
      apply Finset.sum_congr rfl
      intro x hx
      have hxsum := Finset.mem_antidiagonal.mp hx
      split_ifs with hxlt
      · rw [ha ⟨x.1, by omega⟩, ih x.2 hxlt (by omega)]
      · rfl

/-- Extract one analytic coefficient from a checked finite table of its Euler unit. -/
theorem qExpansion_coeff_add_of_table {N v n p : ℕ} {r : Fin N → ℤ} {t : List ℤ}
    (hv : infinitySum N r = 24 * (v : ℤ)) (hn : n < p)
    (ht : IsCoefficientTable (unitCoefficient N r) p t) :
    (UpperHalfPlane.qExpansion 1 (etaQuotient N r)).coeff (v + n) =
      (tableCoefficient t n : ℂ) := by
  rw [qExpansion_coeff_add hv, ht ⟨n, hn⟩]

/-- One checked Euler-unit table certifies the entire coefficient prefix,
including its initial zeros. Only precision `m - v` is needed. -/
theorem first_coeffs_eq_of_table {N v m : ℕ} {r : Fin N → ℤ} {t : List ℤ}
    (hv : infinitySum N r = 24 * (v : ℤ))
    (ht : IsCoefficientTable (unitCoefficient N r) (m - v) t) :
    first_coeffs m (etaQuotient N r) = (List.range m).map
      (fun n ↦ ((if v ≤ n then tableCoefficient t (n - v) else 0 : ℤ) : ℂ)) := by
  rw [first_coeffs_eq_map_range]
  apply List.map_congr_left
  intro n hn
  have hnm : n < m := List.mem_range.mp hn
  split_ifs with hnv
  · simpa only [Nat.add_sub_of_le hnv] using
      qExpansion_coeff_add_of_table hv (show n - v < m - v by omega) ht
  · exact (qExpansion_coeff_eq_zero_of_lt hv (by omega)).trans Int.cast_zero.symm

/-- Add the initial vanishing coefficients and retain exactly the requested prefix. -/
def shiftTable (v m : ℕ) (t : List ℤ) : List ℤ :=
  ((List.replicate (min v m) 0 ++ t).take m).rightpad m 0

@[simp] theorem length_shiftTable (v m : ℕ) (t : List ℤ) : (shiftTable v m t).length = m := by
  simp [shiftTable]

theorem tableCoefficient_shiftTable (v m : ℕ) (t : List ℤ) (n : ℕ) (hn : n < m) :
    tableCoefficient (shiftTable v m t) n =
      if v ≤ n then tableCoefficient t (n - v) else 0 := by
  have hpad (l : List ℤ) : tableCoefficient ((l.take m).rightpad m 0) n = tableCoefficient l n := by
    change ((l.take m).rightpad m 0).getD n 0 = l.getD n 0
    grind [List.rightpad]
  rw [shiftTable, hpad]
  simp only [tableCoefficient]
  split_ifs with hv
  · rw [Nat.min_eq_left (by omega),
      List.getElem?_append_right (by simpa using hv), List.length_replicate]
  · rw [List.getElem?_append_left (by
      simpa using Nat.lt_min.mpr ⟨Nat.lt_of_not_ge hv, hn⟩)]
    simp

/-- The final prefix can be reduced linearly, without indexing a table at each degree. -/
theorem first_coeffs_eq_of_table_shift {N v m : ℕ} {r : Fin N → ℤ} {t : List ℤ}
    (hv : infinitySum N r = 24 * (v : ℤ))
    (ht : IsCoefficientTable (unitCoefficient N r) (m - v) t) :
    first_coeffs m (etaQuotient N r) = (shiftTable v m t).map (fun z : ℤ ↦ (z : ℂ)) := by
  rw [first_coeffs_eq_of_table hv ht]
  apply List.ext_getElem
  · simp
  · intro n hn₁ hn₂
    have hn : n < m := by simpa only [List.length_map, List.length_range] using hn₁
    simp only [List.getElem_map, List.getElem_range]
    have hbound : n < (shiftTable v m t).length := by simpa using hn
    apply congrArg (fun z : ℤ ↦ (z : ℂ))
    simpa only [tableCoefficient, List.getElem?_eq_getElem hbound, Option.getD_some] using
      (tableCoefficient_shiftTable v m t n hn).symm

def addTables : List ℤ → List ℤ → List ℤ
  | [], b => b
  | a, [] => a
  | a :: as, b :: bs => (a + b) :: addTables as bs

theorem tableCoefficient_addTables (a b : List ℤ) (n : ℕ) :
    tableCoefficient (addTables a b) n = tableCoefficient a n + tableCoefficient b n := by
  induction a generalizing b n with
  | nil => simp [addTables, tableCoefficient]
  | cons a as ih =>
    cases b with
    | nil => simp [addTables, tableCoefficient]
    | cons b bs =>
      cases n with
      | zero => rfl
      | succ n => exact ih bs n

def multiplyTables : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: as, b => addTables (b.map (a * ·)) (0 :: multiplyTables as b)

theorem tableCoefficient_scale (a : ℤ) (b : List ℤ) (n : ℕ) :
    tableCoefficient (b.map (a * ·)) n = a * tableCoefficient b n := by
  simp only [tableCoefficient, List.getElem?_map]
  cases b[n]? <;> simp

theorem tableCoefficient_multiplyTables (a b : List ℤ) (n : ℕ) :
    tableCoefficient (multiplyTables a b) n =
      convolution (tableCoefficient a) (tableCoefficient b) n := by
  induction a generalizing n with
  | nil => simp [multiplyTables, tableCoefficient, convolution]
  | cons a as ih =>
    rw [multiplyTables, tableCoefficient_addTables, tableCoefficient_scale]
    cases n with
    | zero => simp [convolution, tableCoefficient]
    | succ n =>
      change a * tableCoefficient b (n + 1) + tableCoefficient (multiplyTables as b) n = _
      rw [ih]
      symm
      rw [convolution, Finset.sum_range_succ']
      simp only [tableCoefficient, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.getD_some, Nat.add_sub_add_right, Nat.sub_zero, convolution]
      exact add_comm _ _

theorem convolution_table_multiply {ta tb tc : List ℤ} {p : ℕ}
    (h : ((multiplyTables ta tb).take p).rightpad p 0 = (tc.take p).rightpad p 0) :
    IsCoefficientTable (convolution (tableCoefficient ta) (tableCoefficient tb)) p tc := by
  intro n
  rw [← tableCoefficient_multiplyTables]
  have he := congrArg (fun t ↦ tableCoefficient t n.val) h
  have hpad (l : List ℤ) : tableCoefficient ((l.take p).rightpad p 0) n = tableCoefficient l n := by
    change ((l.take p).rightpad p 0).getD n 0 = l.getD n 0
    have hn := n.isLt
    grind [List.rightpad]
  simpa only [hpad] using he

theorem inverseTable_of_product {p : ℕ} {ta ti : List ℤ}
    (h0 : tableCoefficient ta 0 = 1)
    (hc : IsCoefficientTable (convolution (tableCoefficient ta) (tableCoefficient ti)) p [1]) :
    IsInverseTable ta ti p := by
  intro ⟨n, hn⟩
  have h := hc ⟨n, hn⟩
  change convolution (tableCoefficient ta) (tableCoefficient ti) n = tableCoefficient [1] n at h
  cases n with
  | zero =>
    have he : convolution (tableCoefficient ta) (tableCoefficient ti) 0 =
        tableCoefficient ta 0 * tableCoefficient ti 0 := by simp [convolution]
    rw [he, h0, one_mul] at h
    simpa [tableCoefficient] using h
  | succ n =>
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ']
    simp only [Nat.sub_zero, lt_self_iff_false, ↓reduceIte, add_zero]
    have hh (k : ℕ) : n + 1 - (k + 1) < n + 1 :=
      Nat.sub_lt (Nat.succ_pos _) (Nat.succ_pos _)
    simp only [hh, ↓reduceIte]
    unfold convolution at h
    rw [Finset.sum_range_succ'] at h
    simp only [h0, Nat.sub_zero, one_mul] at h
    have hzero : tableCoefficient [1] (n + 1) = 0 := by simp [tableCoefficient]
    rw [hzero] at h
    exact eq_neg_of_add_eq_zero_right h

theorem powCoefficient_table_one_values {a : ℕ → ℤ} {p : ℕ}
    (ha : IsCoefficientTable a p [1]) (k : ℕ) :
    IsCoefficientTable (powCoefficient a k) p [1] := by
  induction k with
  | zero => exact oneCoefficient_table p
  | succ k ih => exact convolution_table_one_left ha ih

theorem zpowCoefficient_table_one_values {a : ℕ → ℤ} {p : ℕ}
    (ha : IsCoefficientTable a p [1]) (k : ℤ) :
    IsCoefficientTable (zpowCoefficient a k) p [1] := by
  cases k with
  | ofNat k => exact powCoefficient_table_one_values ha k
  | negSucc k =>
    have hi : IsCoefficientTable (inverseCoefficient a) p [1] :=
      inverseCoefficient_table ha (inverseTable_of_product rfl
        (convolution_table_one_left_values p [1]))
    exact powCoefficient_table_one_values hi (k + 1)
end WeightTwoCusps.EtaQuotient
