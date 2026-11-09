module

public import Dimension.GroupTheory.ParabolicRank

/-! # Elliptic orbit counts on finite congruence coset spaces -/

@[expose] public section

noncomputable section

open scoped MatrixGroups

namespace WeightTwoCusps

private theorem cyclic_orbit_out_eq_of_fixed {G X : Type*} [Group G] [MulAction G X]
    (u : G) (x : X) (hx : u • x = x) :
    (⟦x⟧ : MulAction.orbitRel.Quotient (Subgroup.zpowers u) X).out = x := by
  have hrel := Quotient.exact
    (Quotient.out_eq (⟦x⟧ : MulAction.orbitRel.Quotient (Subgroup.zpowers u) X))
  obtain ⟨v, hv⟩ := MulAction.orbitRel_apply.mp hrel
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp v.property
  have hfix : u ^ j • x = x := MulAction.mem_fixedBy_zpow hx j
  apply hv.symm.trans
  change (v.val : G) • x = x
  rw [← hj]
  exact hfix

/-- For a prime-period action on cosets, nontrivial orbits have full prime size;
the fixed cosets supply the correction to the free-action orbit count. -/
theorem prime_mul_card_cyclic_orbits (G : Type*) [Group G] (Γ : Subgroup G)
    [Γ.FiniteIndex] (u : G) (p : ℕ) [Fact p.Prime]
    (hper : ∀ x : G ⧸ Γ, u ^ p • x = x) :
    p * Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers u) (G ⧸ Γ)) =
      Γ.index + (p - 1) * Nat.card (MulAction.fixedBy (G ⧸ Γ) u) := by
  classical
  let O := MulAction.orbitRel.Quotient (Subgroup.zpowers u) (G ⧸ Γ)
  let : Fintype O := Fintype.ofFinite _
  let F := {q : O // u • q.out = q.out}
  let f : F → MulAction.fixedBy (G ⧸ Γ) u := fun q => ⟨q.val.out, q.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro q r hqr
      apply Subtype.ext
      have h := congrArg Subtype.val hqr
      exact (Quotient.out_eq q.val).symm.trans
        ((congrArg (fun x : G ⧸ Γ => (⟦x⟧ : O)) h).trans (Quotient.out_eq r.val))
    · rintro ⟨x, hx⟩
      change u • x = x at hx
      have hout := cyclic_orbit_out_eq_of_fixed u x hx
      refine ⟨⟨⟦x⟧, ?_⟩, Subtype.ext hout⟩
      simpa only [hout] using hx
  have hsumFix : (∑ q : O, if u • q.out = q.out then 1 else 0) =
      Nat.card (MulAction.fixedBy (G ⧸ Γ) u) := by
    rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [Finset.sum_boole, Nat.cast_id]
  have hterm (q : O) : Function.minimalPeriod (u • ·) q.out +
      (p - 1) * (if u • q.out = q.out then 1 else 0) = p := by
    by_cases hfix : u • q.out = q.out
    · rw [ite_eq_left hfix, mul_one,
        MulAction.minimalPeriod_eq_one_iff_fixedBy.mpr hfix]
      have hp := (Fact.out : p.Prime).two_le
      omega
    · rw [ite_eq_right hfix, mul_zero, add_zero]
      apply Function.minimalPeriod_eq_prime
      · change (u • ·)^[p] q.out = q.out
        simpa only [smul_iterate] using hper q.out
      · exact hfix
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset O)) (s₂ := Finset.univ)
    rfl (fun q _ => hterm q)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsumFix,
    ← Subgroup.index_eq_sum_minimalPeriod] at hsum
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Nat.card_eq_fintype_card, mul_comm] using hsum.symm

/-- `-I` acts trivially on the cosets of a subgroup containing it. -/
theorem neg_one_smul_coset (Γ : Subgroup SL(2, ℤ))
    (hneg : (-1 : SL(2, ℤ)) ∈ Γ) (x : SL(2, ℤ) ⧸ Γ) :
    (-1 : SL(2, ℤ)) • x = x := by
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq]
    simpa using hneg

end WeightTwoCusps
