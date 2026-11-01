# 07-03 Real Operators Inventory (Stub Audit)

This file inventories the current "real operator" layer as wired into the stack, with an explicit gap statement.

## Modules Referenced

- `DASHI/Physics/RealOperators.agda`
- `DASHI/Physics/RealOperatorStack.agda`
- (related) `DASHI/Physics/RealOperatorStackShift.agda`

## Current Definitions (As Implemented)

Source: `DASHI/Physics/RealOperators.agda`

### `Pᵣ` (projection-like, non-identity)

Behavior: for nonempty vectors, it reverses the vector, sets the head of the reversed vector to `zer`, and reverses back. Concretely it "zeroes the last digit" (tail-most trit) while leaving other positions unchanged.

Key lines:

- `setHead (_ ∷ xs) = zer ∷ xs`
- `Pᵣ {suc n} x = reverse (setHead (reverse x))`

Notes:

- For `n = 0`, `Pᵣ [] = []`.
- There is an involution-commutation lemma for `RTC.invVec`:
  `invVec-Pᵣ : RTC.invVec (Pᵣ x) ≡ Pᵣ (RTC.invVec x)`.

### `Cᵣ` (canonicalization / renormalization, currently identity)

Behavior: identity on `RTC.Carrier n`.

Key line:

- `Cᵣ x = x`

### `Rᵣ` (currently identity)

Behavior: identity on `RTC.Carrier n`.

Key line:

- `Rᵣ x = x`

## Stack Wiring

Source: `DASHI/Physics/RealOperatorStack.agda`

- `C {n} = RO.Cᵣ {n}`
- `P {n} = RO.Pᵣ {n}`
- `R {n} = RO.Rᵣ {n}`

Nonexpansive proofs are re-exported from `RealOperators`:

- `nonexpC {n} = RO.nonexpCᵣ {n}`
- `nonexpR {n} = RO.nonexpRᵣ {n}`

Fiber contraction currently depends on `P` only:

- `strictP-fiber : FC.ContractiveOnFibers ... (P {n})`

## What Is Prototype/Identity and Why That Is "Not Yet Physical"

- `Cᵣ` is labeled canonicalization/renormalization but implemented as identity.
  This makes all downstream theorems about canonicalization vacuous: any property proved
  about `Cᵣ` holds only because it does nothing.

- `Rᵣ` is implemented as identity. If `Rᵣ` is intended to model a physically meaningful
  reparametrization or rotation/renaming, the current definition provides no semantics.

- `Pᵣ` is non-identity and does perform a concrete transformation (tail projection),
  but by itself it does not supply a full "real operators" story.

## Properties Already Proved vs Missing

Source: `DASHI/Physics/RealOperators.agda`

Already present:

- `nonexpPᵣ` under `FAM.ultrametricVec` (proved via an agreement-depth nondecrease lemma).
- `nonexpCᵣ` and `nonexpRᵣ`, but currently only because `Cᵣ`/`Rᵣ` are identity.
- `invVec-Pᵣ` commuting lemma.

Not present / not credible yet:

- Any nontrivial semantics and corresponding proof obligations for `Cᵣ` or `Rᵣ`.
- Any explicit closure-axiom package tying the triad `Cᵣ`/`Pᵣ`/`Rᵣ` together beyond
  wiring and nonexpansiveness.

## Related (Shifted Stack)

`DASHI/Physics/RealOperatorStackShift.agda` already contains a nontrivial `R` (tail shift)
for a split `(m + k)` carrier, with a dedicated nonexpansiveness proof.

This highlights the gap: the primary stack uses identity `Rᵣ`, while a separate module
contains a meaningful `R`-like operator with proofs.
