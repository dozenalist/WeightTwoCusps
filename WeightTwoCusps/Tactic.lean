module

public import WeightTwoCusps.Tactic.Gamma_0
public import WeightTwoCusps.Tactic.Gamma_1
public import WeightTwoCusps.Tactic.Gamma
public import WeightTwoCusps.Tactic.EtaCoefficient
public import WeightTwoCusps.Tactic.EtaSimps
public import WeightTwoCusps.Tactic.EtaOldform
public import WeightTwoCusps.Tactic.Basis

/-!
# Numeral evaluation for dimensions and eta-quotient coefficients

Import this module to register the dimension simprocs for `Γ₀`, `Γ₁`, and `Γ`.
The subgroup-specific modules can also be imported separately.
`EtaCoefficient` evaluates q-expansion coefficients and `first_coeffs` lists of signed eta quotients
using finite integer tables checked by the kernel.
`@[eta_simps]` derives individual coefficient simp lemmas from checked prefixes,
and entry simp lemmas from finite bases.
`Basis` provides specialized dimension, period, determinant, and independence tactics,
with `cusp_basis` as a compatibility dispatcher. `IntegerDeterminant` supplies
the general `integer_det` backend for triangular and modular certificates.
`EtaOldform` provides `eta_oldform` for exact identities between degeneracy lifts and eta products.
-/
