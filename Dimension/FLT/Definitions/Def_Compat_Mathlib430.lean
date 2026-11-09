/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache 2.0 license.
Copied from anthropics/fermats-last-theorem, revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_Compat_Mathlib430.lean.
Adapted for this project: local imports, modules, unused code, and shared proofs.
See Dimension/FLT/LICENSE, NOTICE, and ATTRIBUTION_UPSTREAM.md.
-/
/-
Copyright: the vendored blocks below are verbatim copies from Mathlib (Apache-2.0; see Mathlib's LICENSE),
release v4.30.0 = leanprover-community/mathlib4 commit c5ea00351c28e24afc9f0f84379aa41082b1188f, with declarations
RENAMED (suffix `Finsupp` / trailing prime) so they do not clash with Mathlib v4.33.0. Bodies are the Mathlib v4.30.0 text
with its docstrings omitted, otherwise byte-identical unless a line is marked `-- [port]`.
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.GroupWithZero.Action.Basic
public import Mathlib.Algebra.Ring.AddAut

@[expose] public section

set_option autoImplicit false

/- Only the additive-automorphism compatibility block is needed here. -/

namespace AddAut

section Compat430

variable (A : Type*) [Add A]

instance : Group (AddAut A) where
  mul g h := AddEquiv.trans h g
  one := AddEquiv.refl _
  inv := AddEquiv.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel := AddEquiv.self_trans_symm

/- The following thirteen lemmas are Mathlib v4.30.0 `Mathlib/Algebra/Group/End.lean:758-801`
verbatim except that each name carries a trailing prime. -/

@[simp]
theorem coe_mul' (e₁ e₂ : AddAut A) : ⇑(e₁ * e₂) = e₁ ∘ e₂ :=
  rfl

@[simp]
theorem coe_one' : ⇑(1 : AddAut A) = id :=
  rfl

@[simp]
theorem coe_inv' (e : AddAut A) : ⇑e⁻¹ = e.symm := rfl

theorem mul_def' (e₁ e₂ : AddAut A) : e₁ * e₂ = e₂.trans e₁ :=
  rfl

theorem one_def' : (1 : AddAut A) = AddEquiv.refl _ :=
  rfl

theorem inv_def' (e₁ : AddAut A) : e₁⁻¹ = e₁.symm :=
  rfl

@[simp]
theorem mul_apply' (e₁ e₂ : AddAut A) (a : A) : (e₁ * e₂) a = e₁ (e₂ a) :=
  rfl

@[simp]
theorem one_apply' (a : A) : (1 : AddAut A) a = a :=
  rfl

@[simp]
theorem inv_symm' (e : AddAut A) : e⁻¹.symm = e := rfl

@[simp]
theorem symm_inv' (e : AddAut A) : e.symm⁻¹ = e := rfl

@[simp]
theorem inv_apply' (e : AddAut A) (a : A) : e⁻¹ a = e.symm a := rfl

theorem inv_apply_self' (e : AddAut A) (a : A) : e⁻¹ (e a) = a :=
  AddEquiv.apply_symm_apply _ _

theorem apply_inv_self' (e : AddAut A) (a : A) : e (e⁻¹ a) = a :=
  AddEquiv.apply_symm_apply _ _

example (e₁ e₂ : AddAut A) : e₁ * e₂ = e₁ + e₂ := rfl
example : (1 : AddAut A) = 0 := rfl
example (e : AddAut A) : e⁻¹ = -e := rfl

end Compat430

end AddAut

@[simps]
def DistribMulAction.toAddAut' (G A : Type*) [Group G] [AddMonoid A] [DistribMulAction G A] :
    G →* AddAut A where
  toFun := DistribMulAction.toAddEquiv A
  map_one' := AddEquiv.ext (one_smul _)
  map_mul' _ _ := AddEquiv.ext (mul_smul _ _)

@[simps! +simpRhs]
def AddAut.mulLeft' {R : Type*} [Semiring R] : Rˣ →* AddAut R :=
  DistribMulAction.toAddAut' _ _

/-! ### Block D (continued) — Mathlib v4.30.0 Mathlib/Algebra/GroupWithZero/Action/Basic.lean:104-112: the tautological `DistribMulAction (AddAut A) A`
(`AddAut.applyDistribMulAction`, its `smul_def` and `apply_faithfulSMul`), dropped in v4.33.0 together with the multiplicative structure;
vendored with primed names on top of the Group instance above. -/

namespace AddAut
instance applyDistribMulAction' {A : Type*} [AddMonoid A] : DistribMulAction (AddAut A) A where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero := AddEquiv.map_zero
  smul_add := AddEquiv.map_add

@[simp] protected theorem smul_def' {A : Type*} [AddMonoid A] (f : AddAut A) (a : A) : f • a = f a := rfl

instance apply_faithfulSMul' {A : Type*} [AddMonoid A] : FaithfulSMul (AddAut A) A :=
  ⟨fun h => AddEquiv.ext h⟩
end AddAut

