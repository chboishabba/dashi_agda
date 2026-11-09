module DASHI.Mathematics.Complexity.Karp21NativeLedgerIntegerScoreExact where

------------------------------------------------------------------------
-- P0-C: actual binary two-lane ledger -> signed original integer sum.
--
-- Consume the existing executable Ledger.accumulateSigned and its
-- two numerical observation proofs, not a different ledger or adder.
-- Mathematical ℤ observation uses unary Naturals only in the theorem,
-- never in the executable bit-native accumulator.
--
-- The two integer ring identities below are the exact source algebra
-- that turns positive/negative masses into selected signed weights.
-- Original source owner: Karp21BinaryNativeSignedLedgerExact.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (reverse)
open import Data.Product using (_×_; _,_)
open import Data.Integer.Base as Int using (ℤ; +_; -_; -[1+_])
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; sym)
import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Signed
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact as Ledger
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact as Value
import DASHI.Mathematics.Complexity.Karp21SignedGammaNativeOriginalValueExact as TokenValue

module RingZ = NR IntRS.ring
open RingZ using (_⊕_; _⊗_; Κ)

integerFromTwoLaneTotals : Nat → Nat → ℤ
integerFromTwoLaneTotals positive negative =
  Int._+_ (+ positive) (- (+ negative))

observeActualNativeLedger : Ledger.SignedLedger → ℤ
observeActualNativeLedger ledger =
  integerFromTwoLaneTotals
    (Ledger.positiveValue ledger)
    (Ledger.negativeValue ledger)

-- Two *actual* bit registers have exactly the signed total represented
-- by the source's original token-class totals (no equal-value oracle).
nativeLedgerMatchesClassTotals :
  (tokens : List Signed.SignedMagnitudeBits) →
  observeActualNativeLedger
    (Ledger.accumulateSigned tokens Ledger.emptyLedger)
    ≡ integerFromTwoLaneTotals
        (Ledger.sumPositive tokens) (Ledger.sumNegative tokens)
nativeLedgerMatchesClassTotals tokens =
  cong₂ integerFromTwoLaneTotals
    (Ledger.accumulateEmptyPositive tokens)
    (Ledger.accumulateEmptyNegative tokens)

-- Exact integer algebra, specialized to the original binary token
-- interpretation. Negative contributions must negate the *entire*
-- magnitude, not merely their sign bit.
integerPositiveStep :
  (m p n : Nat) →
  integerFromTwoLaneTotals (m + p) n
    ≡ Int._+_ (+ m) (integerFromTwoLaneTotals p n)
integerPositiveStep m p n =
  RingZ.solve 3
    (λ x y z →
      ((x ⊕ y) ⊕ (Κ (-[1+ zero ]) ⊗ z))
      ,
      (x ⊕ (y ⊕ (Κ (-[1+ zero ]) ⊗ z))))
    refl (+ m) (+ p) (+ n)

integerNegativeStep :
  (m p n : Nat) →
  integerFromTwoLaneTotals p (m + n)
    ≡ Int._+_ (- (+ m)) (integerFromTwoLaneTotals p n)
integerNegativeStep m p n =
  RingZ.solve 3
    (λ x y z →
      (y ⊕ (Κ (-[1+ zero ]) ⊗ (x ⊕ z)))
      ,
      ((Κ (-[1+ zero ]) ⊗ x) ⊕
        (y ⊕ (Κ (-[1+ zero ]) ⊗ z))))
    refl (+ m) (+ p) (+ n)

-- The existing original signed decoder stores a magnitude, not an
-- arbitrary negative-zero sentinel. Its value observation coincides
-- with integer negation on ALL binary payloads.
negativeTokenInteger :
  (magnitude : Word.BitWord) →
  TokenValue.interpretNativeToken (Signed.negative magnitude) ≡
    - (+ (Value.valueLE (reverse magnitude)))
negativeTokenInteger magnitude
  with Value.valueLE (reverse magnitude)
... | zero = refl
... | suc k = refl

-- All source signed tokens, including noncanonical zero bitwords:
-- signed class totals equal exactly the original mathematical ℤ fold.
signedTrace : List Signed.SignedMagnitudeBits → ℤ
signedTrace [] = + zero
signedTrace (token ∷ rest) =
  Int._+_ (TokenValue.interpretNativeToken token) (signedTrace rest)

tokenClassesEqualOriginalSignedTrace :
  (tokens : List Signed.SignedMagnitudeBits) →
  integerFromTwoLaneTotals
    (Ledger.sumPositive tokens) (Ledger.sumNegative tokens)
    ≡ signedTrace tokens

tokenClassesEqualOriginalSignedTrace [] = refl
tokenClassesEqualOriginalSignedTrace
  (Signed.positive magnitude ∷ rest) =
  trans
    (integerPositiveStep
      (Value.valueLE (reverse magnitude))
      (Ledger.sumPositive rest)
      (Ledger.sumNegative rest))
    (cong
      (λ total → Int._+_ (+ (Value.valueLE (reverse magnitude))) total)
      (tokenClassesEqualOriginalSignedTrace rest))
tokenClassesEqualOriginalSignedTrace
  (Signed.negative magnitude ∷ rest) =
  trans
    (integerNegativeStep
      (Value.valueLE (reverse magnitude))
      (Ledger.sumPositive rest)
      (Ledger.sumNegative rest))
    (trans
      (cong
        (λ total → Int._+_ (- (+ (Value.valueLE (reverse magnitude)))) total)
        (tokenClassesEqualOriginalSignedTrace rest))
      (cong
        (λ z → Int._+_ z (signedTrace rest))
        (sym (negativeTokenInteger magnitude))))

-- P0-C: the real executable two-register binary fold, observed in
-- ℤ, equals the original signed token trace (no signed subtraction
-- is executed by the verifier's accumulator).
nativeSignedLedgerIntegerEqualsOriginalTraceScore :
  (tokens : List Signed.SignedMagnitudeBits) →
  observeActualNativeLedger
    (Ledger.accumulateSigned tokens Ledger.emptyLedger)
    ≡ signedTrace tokens
nativeSignedLedgerIntegerEqualsOriginalTraceScore tokens =
  trans
    (nativeLedgerMatchesClassTotals tokens)
    (tokenClassesEqualOriginalSignedTrace tokens)
