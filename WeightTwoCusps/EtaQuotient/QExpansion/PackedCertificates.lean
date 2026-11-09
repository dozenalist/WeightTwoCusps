module

public import WeightTwoCusps.EtaQuotient.QExpansion.Certificates
public meta import Mathlib.Tactic.Ring

/-!
# Packed integer certificates for coefficient-table products

Evaluating a table at a sufficiently large integer base permits one integer
multiplication to certify a whole coefficient prefix. A norm bound prevents
nonzero small coefficients from being hidden by carries between digits.
-/

@[expose] public section

namespace WeightTwoCusps.EtaQuotient

/-- Sum of the absolute values of a finite integer coefficient table. -/
def tableNorm : List ℤ → ℕ
  | [] => 0
  | a :: as => a.natAbs + tableNorm as

/-- Evaluate the polynomial encoded by a coefficient table. -/
def evaluateTable (base : ℤ) : List ℤ → ℤ
  | [] => 0
  | a :: as => a + base * evaluateTable base as

theorem tableNorm_addTables (a b : List ℤ) :
    tableNorm (addTables a b) ≤ tableNorm a + tableNorm b := by
  induction a generalizing b with
  | nil => simp [addTables, tableNorm]
  | cons a as ih =>
    cases b with
    | nil => simp [addTables, tableNorm]
    | cons b bs =>
      simp only [addTables, tableNorm]
      calc
        (a + b).natAbs + tableNorm (addTables as bs) ≤
            (a.natAbs + b.natAbs) + (tableNorm as + tableNorm bs) :=
          Nat.add_le_add (Int.natAbs_add_le a b) (ih bs)
        _ = (a.natAbs + tableNorm as) + (b.natAbs + tableNorm bs) := by omega

theorem tableNorm_scale (a : ℤ) (b : List ℤ) :
    tableNorm (b.map (a * ·)) = a.natAbs * tableNorm b := by
  induction b with
  | nil => simp [tableNorm]
  | cons b bs ih => simp [tableNorm, Int.natAbs_mul, Nat.mul_add, ih]

theorem tableNorm_neg (a : List ℤ) : tableNorm (a.map (- ·)) = tableNorm a := by
  induction a with
  | nil => rfl
  | cons a as ih => simp [tableNorm, ih]

theorem tableNorm_multiplyTables (a b : List ℤ) :
    tableNorm (multiplyTables a b) ≤ tableNorm a * tableNorm b := by
  induction a with
  | nil => simp [multiplyTables, tableNorm]
  | cons a as ih =>
    rw [multiplyTables]
    calc
      tableNorm (addTables (b.map (a * ·)) (0 :: multiplyTables as b)) ≤
          tableNorm (b.map (a * ·)) + tableNorm (0 :: multiplyTables as b) :=
        tableNorm_addTables _ _
      _ = a.natAbs * tableNorm b + tableNorm (multiplyTables as b) := by
        simp [tableNorm_scale, tableNorm]
      _ ≤ a.natAbs * tableNorm b + tableNorm as * tableNorm b := Nat.add_le_add_left ih _
      _ = tableNorm (a :: as) * tableNorm b := by simp [tableNorm, Nat.add_mul]

theorem evaluateTable_addTables (base : ℤ) (a b : List ℤ) :
    evaluateTable base (addTables a b) = evaluateTable base a + evaluateTable base b := by
  induction a generalizing b with
  | nil => simp [addTables, evaluateTable]
  | cons a as ih =>
    cases b with
    | nil => simp [addTables, evaluateTable]
    | cons b bs => simp only [addTables, evaluateTable, ih]; ring

theorem evaluateTable_scale (base a : ℤ) (b : List ℤ) :
    evaluateTable base (b.map (a * ·)) = a * evaluateTable base b := by
  induction b with
  | nil => simp [evaluateTable]
  | cons b bs ih => simp only [List.map_cons, evaluateTable, ih]; ring

theorem evaluateTable_neg (base : ℤ) (a : List ℤ) :
    evaluateTable base (a.map (- ·)) = -evaluateTable base a := by
  induction a with
  | nil => simp [evaluateTable]
  | cons a as ih => simp only [List.map_cons, evaluateTable, ih]; ring

theorem evaluateTable_multiplyTables (base : ℤ) (a b : List ℤ) :
    evaluateTable base (multiplyTables a b) = evaluateTable base a * evaluateTable base b := by
  induction a with
  | nil => simp [multiplyTables, evaluateTable]
  | cons a as ih =>
    rw [multiplyTables, evaluateTable_addTables, evaluateTable_scale]
    simp only [evaluateTable, ih]
    ring

theorem tableCoefficient_neg (a : List ℤ) (n : ℕ) :
    tableCoefficient (a.map (- ·)) n = -tableCoefficient a n := by
  simp only [tableCoefficient, List.getElem?_map]
  cases a[n]? <;> simp

/-- A sufficiently small coefficient cannot disappear into a base carry. -/
theorem tableCoefficient_zero_of_evaluate_dvd {base p : ℕ} {t : List ℤ}
    (hb : tableNorm t < base) (hd : (base : ℤ) ^ p ∣ evaluateTable base t)
    (n : ℕ) (hn : n < p) : tableCoefficient t n = 0 := by
  induction p generalizing t n with
  | zero => omega
  | succ p ih =>
    cases t with
    | nil => rfl
    | cons a as =>
      have hbase : (base : ℤ) ≠ 0 := by
        have : 0 < base := lt_of_le_of_lt (Nat.zero_le _) hb
        exact_mod_cast this.ne'
      have had : (base : ℤ) ∣ a := by
        have hbd : (base : ℤ) ∣ evaluateTable base (a :: as) :=
          dvd_trans (dvd_pow_self (base : ℤ) (Nat.succ_ne_zero p)) hd
        have hsub := dvd_sub hbd (dvd_mul_right (base : ℤ) (evaluateTable base as))
        simpa only [evaluateTable, add_sub_cancel_right] using hsub
      have ha : a = 0 := by
        apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs had
        have hab : a.natAbs < base := by simp only [tableNorm] at hb; omega
        simpa using hab
      subst a
      have htail : (base : ℤ) ^ p ∣ evaluateTable base as := by
        apply (mul_dvd_mul_iff_left hbase).mp
        simpa only [pow_succ', evaluateTable, zero_add] using hd
      cases n with
      | zero => rfl
      | succ n =>
        exact ih (by simpa [tableNorm] using hb) htail n (by omega)

/-- A packed multiplication and a norm bound certify every coefficient below `p`. -/
theorem convolution_table_packed {ta tb tc : List ℤ} {p base : ℕ}
    (hb : tableNorm ta * tableNorm tb + tableNorm tc < base)
    (hd : (base : ℤ) ^ p ∣
      evaluateTable base ta * evaluateTable base tb - evaluateTable base tc) :
    IsCoefficientTable (convolution (tableCoefficient ta) (tableCoefficient tb)) p tc := by
  let difference := addTables (multiplyTables ta tb) (tc.map (- ·))
  have hnorm : tableNorm difference < base := by
    apply lt_of_le_of_lt _ hb
    exact (tableNorm_addTables _ _).trans (by
      rw [tableNorm_neg]
      exact Nat.add_le_add_right (tableNorm_multiplyTables ta tb) _)
  have hdiv : (base : ℤ) ^ p ∣ evaluateTable base difference := by
    simpa only [difference, evaluateTable_addTables, evaluateTable_multiplyTables,
      evaluateTable_neg, sub_eq_add_neg] using hd
  intro n
  have hz := tableCoefficient_zero_of_evaluate_dvd hnorm hdiv n n.isLt
  simp only [difference, tableCoefficient_addTables, tableCoefficient_neg,
    tableCoefficient_multiplyTables, ← sub_eq_add_neg] at hz
  exact sub_eq_zero.mp hz

end WeightTwoCusps.EtaQuotient
