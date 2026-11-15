module DASHI.Mathematics.Complexity.Karp21NativeSignedLedgerWidthBudgetExact where

------------------------------------------------------------------------
-- F2: actual signed two-lane ledger REGISTER-WIDTH budget.
--
-- This consumes THE executable Ledger.insertSigned / accumulateSigned
-- and real original Add.addBits. A selected signed-gamma token costs
-- at most its magnitude-register length plus one carry bit.
--
-- Thus total final positive+negative register widths do not exceed
-- initial widths plus sum of (1 + binary magnitude width) of EACH
-- actually selected signed token. No source Nat magnitude or ℤ score
-- is allocated on the executable ledger path.
--
-- NOT an all-word bit-Turing-machine clock: parsing, repeated
-- histories, head motion and the physical cost of list allocation
-- remain independent F1/F3/F4 obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (length; reverse)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP
import Data.List.Properties as ListP
open import Relation.Binary.PropositionalEquality using (subst)
open import Data.Nat.Tactic.RingSolver using (solve)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Signed
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact as Ledger
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderExact as Add
import DASHI.Mathematics.Complexity.Karp21NativeBinaryAdderWidthBoundExact as Width

actualLedgerWidth : Ledger.SignedLedger → Nat
actualLedgerWidth ledger =
  length (proj₁ ledger) + length (proj₂ ledger)

signedTokenBitCharge : Signed.SignedMagnitudeBits → Nat
signedTokenBitCharge (Signed.positive magnitude) =
  suc (length magnitude)
signedTokenBitCharge (Signed.negative magnitude) =
  suc (length magnitude)

selectedTokenCharges : List Signed.SignedMagnitudeBits → Nat
selectedTokenCharges [] = zero
selectedTokenCharges (token ∷ rest) =
  signedTokenBitCharge token + selectedTokenCharges rest

reverseMagnitudeLength :
  (bits : Word.BitWord) →
  length (reverse bits) ≡ length bits
reverseMagnitudeLength = ListP.length-reverse

oneLaneAdditionWidth :
  (acc magnitude : Word.BitWord) →
  length (Add.addBits acc (reverse magnitude))
    ≤ suc (length acc + length magnitude)
oneLaneAdditionWidth acc magnitude =
  subst
    (λ k →
      length (Add.addBits acc (reverse magnitude))
      ≤ suc (length acc + k))
    (reverseMagnitudeLength magnitude)
    (Width.addBitsOutputBitWidthLinear acc (reverse magnitude))

-- Numeric reordering of widths (not a runtime integer operation).
widthRearrange :
  (p n k : Nat) →
  suc (p + k) + n ≡ (p + n) + suc k
widthRearrange p n k = solve (p ∷ n ∷ k ∷ [])

-- Each actual signed-token insertion grows the sum of both lane
-- widths by at most one bit plus the token's original binary width.
actualInsertSignedWidthBound :
  (token : Signed.SignedMagnitudeBits)
  (ledger : Ledger.SignedLedger) →
  actualLedgerWidth (Ledger.insertSigned token ledger)
    ≤ actualLedgerWidth ledger + signedTokenBitCharge token
actualInsertSignedWidthBound (Signed.positive bits) (positive , negative) =
  subst
    (λ bound →
      length (Add.addBits positive (reverse bits))
        + length negative ≤ bound)
    (widthRearrange (length positive)
      (length negative) (length bits))
    (NatP.+-mono-≤
      (oneLaneAdditionWidth positive bits)
      NatP.≤-refl)
actualInsertSignedWidthBound (Signed.negative bits) (positive , negative) =
  subst
    (λ bound →
      length positive
        + length (Add.addBits negative (reverse bits)) ≤ bound)
    (widthNegativeRearrange (length positive)
      (length negative) (length bits))
    (NatP.+-mono-≤
      NatP.≤-refl
      (oneLaneAdditionWidth negative bits))
  where
    widthNegativeRearrange :
      (p n k : Nat) →
      p + suc (n + k) ≡ (p + n) + suc k
    widthNegativeRearrange p n k = solve (p ∷ n ∷ k ∷ [])

-- All-list theorem over the ACTUAL executable left-accumulating
-- signed ripple ledger, no abstraction of its arithmetic.
actualAccumulateSignedWidthBudget :
  (selected : List Signed.SignedMagnitudeBits)
  (ledger : Ledger.SignedLedger) →
  actualLedgerWidth (Ledger.accumulateSigned selected ledger)
    ≤ actualLedgerWidth ledger + selectedTokenCharges selected
actualAccumulateSignedWidthBudget [] ledger =
  NatP.m≤m+n (actualLedgerWidth ledger) zero
actualAccumulateSignedWidthBudget (token ∷ rest) ledger =
  subst
    (λ bound →
      actualLedgerWidth
        (Ledger.accumulateSigned (token ∷ rest) ledger) ≤ bound)
    (NatP.+-assoc
      (actualLedgerWidth ledger)
      (signedTokenBitCharge token)
      (selectedTokenCharges rest))
    (NatP.≤-trans
      (actualAccumulateSignedWidthBudget
        rest (Ledger.insertSigned token ledger))
      (NatP.+-mono-≤
        (actualInsertSignedWidthBound token ledger)
        NatP.≤-refl))
