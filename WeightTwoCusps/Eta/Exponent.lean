module

public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.LinearCombination

/-! # The congruence character of the square of the Dedekind eta function

Its two components have orders three and four. The finite arithmetic checks
below take place in rings with only three and four elements respectively.
-/

@[expose] public section

open scoped MatrixGroups

set_option backward.isDefEq.respectTransparency false

namespace WeightTwoCusps.Eta

def exponentThree (a b c d : ZMod 3) : ZMod 3 :=
  if c = 0 then b * d else (a + d) * c

def exponentFour (a b c d : ZMod 4) : ZMod 4 :=
  if c.val % 2 = 1 then
    (a + d) * c - b * d * (c ^ 2 - 1) - 3 * c
  else
    (a + d) * c - b * d * (c ^ 2 - 1) + 3 * d - 3 - 3 * c * d

def liftThree : ZMod 3 →+ ZMod 12 :=
  ZMod.lift 3 ⟨{
    toFun := fun x : ℤ ↦ (x : ZMod 12) * 4
    map_zero' := by simp
    map_add' := by intros; simp [add_mul] }, by decide⟩

def liftFour : ZMod 4 →+ ZMod 12 :=
  ZMod.lift 4 ⟨{
    toFun := fun x : ℤ ↦ (x : ZMod 12) * 9
    map_zero' := by simp
    map_add' := by intros; simp [add_mul] }, by decide⟩

private theorem liftThree_one : liftThree 1 = 4 := by
  change liftThree ((1 : ℤ) : ZMod 3) = 4
  rw [liftThree, ZMod.lift_coe]
  norm_num

private theorem liftFour_one : liftFour 1 = 9 := by
  change liftFour ((1 : ℤ) : ZMod 4) = 9
  rw [liftFour, ZMod.lift_coe]
  norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the character identities for every matrix modulo three.
private theorem exponentThree_laws :
    ∀ a b c d : ZMod 3, a * d - b * c = 1 →
      exponentThree b (-a) d (-c) = exponentThree a b c d ∧
      exponentThree a (a + b) c (c + d) = exponentThree a b c d + 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the character identities for every matrix modulo four.
private theorem exponentFour_laws :
    ∀ a b c d : ZMod 4, a * d - b * c = 1 →
      exponentFour b (-a) d (-c) = exponentFour a b c d + 1 ∧
      exponentFour a (a + b) c (c + d) = exponentFour a b c d + 1 := by
  decide +kernel

abbrev reduceThree : ZMod 12 →+* ZMod 3 := ZMod.castHom (by decide) _
abbrev reduceFour : ZMod 12 →+* ZMod 4 := ZMod.castHom (by decide) _

/-- The exponent of the integral-weight eta multiplier, modulo twelve. -/
def etaExponentResidue (a b c d : ZMod 12) : ZMod 12 :=
  liftThree (exponentThree (reduceThree a) (reduceThree b) (reduceThree c) (reduceThree d)) +
  liftFour (exponentFour (reduceFour a) (reduceFour b) (reduceFour c) (reduceFour d))

private theorem etaExponentResidue_mul_S (a b c d : ZMod 12)
    (h : a * d - b * c = 1) :
    etaExponentResidue b (-a) d (-c) = etaExponentResidue a b c d - 3 := by
  have h3 := (exponentThree_laws _ _ _ _ (show
    reduceThree a * reduceThree d - reduceThree b * reduceThree c = 1 by
      simpa using congrArg reduceThree h)).1
  have h4 := (exponentFour_laws _ _ _ _ (show
    reduceFour a * reduceFour d - reduceFour b * reduceFour c = 1 by
      simpa using congrArg reduceFour h)).1
  simp only [etaExponentResidue, map_neg, h3, h4, map_add, liftFour_one]
  have hnum : (9 : ZMod 12) = -3 := by decide
  rw [hnum]
  abel

private theorem etaExponentResidue_mul_T (a b c d : ZMod 12)
    (h : a * d - b * c = 1) :
    etaExponentResidue a (a + b) c (c + d) = etaExponentResidue a b c d + 1 := by
  have h3 := (exponentThree_laws _ _ _ _ (show
    reduceThree a * reduceThree d - reduceThree b * reduceThree c = 1 by
      simpa using congrArg reduceThree h)).2
  have h4 := (exponentFour_laws _ _ _ _ (show
    reduceFour a * reduceFour d - reduceFour b * reduceFour c = 1 by
      simpa using congrArg reduceFour h)).2
  simp only [etaExponentResidue, map_add, h3, h4, liftThree_one, liftFour_one]
  have hnum : (4 : ZMod 12) + 9 = 1 := by decide
  linear_combination hnum

/-- The eta-square multiplier exponent of an integral modular matrix. -/
def etaExponent (γ : SL(2, ℤ)) : ZMod 12 :=
  etaExponentResidue (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)

@[simp] theorem etaExponent_one : etaExponent 1 = 0 := by
  simp [etaExponent, etaExponentResidue, exponentThree, exponentFour]

private theorem det_mod_twelve (γ : SL(2, ℤ)) :
    (γ 0 0 : ZMod 12) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have h := congrArg (Int.cast : ℤ → ZMod 12) γ.det_coe
  simpa only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one] using h

theorem etaExponent_mul_S (γ : SL(2, ℤ)) :
    etaExponent (γ * ModularGroup.S) = etaExponent γ - 3 := by
  change etaExponentResidue (((γ : Matrix (Fin 2) (Fin 2) ℤ) * ModularGroup.S) 0 0)
    (((γ : Matrix (Fin 2) (Fin 2) ℤ) * ModularGroup.S) 0 1)
    (((γ : Matrix (Fin 2) (Fin 2) ℤ) * ModularGroup.S) 1 0)
    (((γ : Matrix (Fin 2) (Fin 2) ℤ) * ModularGroup.S) 1 1) = _
  simpa [etaExponent, ModularGroup.S, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Fin.sum_univ_two] using
    etaExponentResidue_mul_S (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) (det_mod_twelve γ)

theorem etaExponent_mul_T (γ : SL(2, ℤ)) :
    etaExponent (γ * ModularGroup.T) = etaExponent γ + 1 := by
  change etaExponentResidue (((γ : Matrix (Fin 2) (Fin 2) ℤ) * ModularGroup.T) 0 0)
    (((γ : Matrix (Fin 2) (Fin 2) ℤ) * ModularGroup.T) 0 1)
    (((γ : Matrix (Fin 2) (Fin 2) ℤ) * ModularGroup.T) 1 0)
    (((γ : Matrix (Fin 2) (Fin 2) ℤ) * ModularGroup.T) 1 1) = _
  simpa [etaExponent, ModularGroup.T, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Fin.sum_univ_two] using
    etaExponentResidue_mul_T (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) (det_mod_twelve γ)

@[simp] theorem etaExponent_S : etaExponent ModularGroup.S = -3 := by
  simpa using etaExponent_mul_S 1

@[simp] theorem etaExponent_T : etaExponent ModularGroup.T = 1 := by
  simpa using etaExponent_mul_T 1

end WeightTwoCusps.Eta
