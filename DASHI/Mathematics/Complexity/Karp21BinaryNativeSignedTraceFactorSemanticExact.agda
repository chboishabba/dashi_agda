{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedTraceFactorSemanticExact where

------------------------------------------------------------------------
-- N21: WHOLE-TRACE NUMERIC SEMANTICS OF ACTUAL SIGNED FACTORISATION.
-- No oracle, hypothetical grouping, fresh graph language or unary
-- runtime. Key equivalence comes from bitwise equality soundness.
--
-- External representation/operation cost and original rawSparseScore
-- numeric decoding remain separate original P0 proof obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.List.Base using (List; reverse)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Nat.Tactic.RingSolver using (solve)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Signed
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderExact as Add
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact as Value
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact as Ledger
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedTraceFactorExact as Factor

positiveTokenValue : Signed.SignedMagnitudeBits → Nat
positiveTokenValue (Signed.positive magnitude) =
  Value.valueLE (reverse magnitude)
positiveTokenValue (Signed.negative magnitude) = zero

negativeTokenValue : Signed.SignedMagnitudeBits → Nat
negativeTokenValue (Signed.positive magnitude) = zero
negativeTokenValue (Signed.negative magnitude) =
  Value.valueLE (reverse magnitude)

commuteIntoSum :
  (a b c : Nat) →
  a + (b + c) ≡ b + (a + c)
commuteIntoSum a b c = solve (a ∷ b ∷ c ∷ [])

incrementPositiveClass :
  (weight : Signed.SignedMagnitudeBits)
  (count : Word.BitWord) →
  Factor.positiveClassTotal
    (weight , Add.addBits count Factor.binaryOne) ≡
  positiveTokenValue weight +
    Factor.positiveClassTotal (weight , count)
incrementPositiveClass (Signed.positive magnitude) count =
  trans
    (cong (λ n → Value.valueLE (reverse magnitude) * n)
      (Factor.binaryCounterIncrementValue count))
    (solve
      (Value.valueLE (reverse magnitude) ∷
       Value.valueLE count ∷ []))
incrementPositiveClass (Signed.negative magnitude) count = refl

incrementNegativeClass :
  (weight : Signed.SignedMagnitudeBits)
  (count : Word.BitWord) →
  Factor.negativeClassTotal
    (weight , Add.addBits count Factor.binaryOne) ≡
  negativeTokenValue weight +
    Factor.negativeClassTotal (weight , count)
incrementNegativeClass (Signed.positive magnitude) count = refl
incrementNegativeClass (Signed.negative magnitude) count =
  trans
    (cong (λ n → Value.valueLE (reverse magnitude) * n)
      (Factor.binaryCounterIncrementValue count))
    (solve
      (Value.valueLE (reverse magnitude) ∷
       Value.valueLE count ∷ []))

singletonPositiveClass :
  (weight : Signed.SignedMagnitudeBits) →
  Factor.positiveFactorTotal
    ((weight , Factor.binaryOne) ∷ []) ≡ positiveTokenValue weight
singletonPositiveClass (Signed.positive magnitude) =
  trans
    (NatP.+-identityʳ (Value.valueLE (reverse magnitude) *
                       Value.valueLE Factor.binaryOne))
    (NatP.*-identityʳ (Value.valueLE (reverse magnitude)))
singletonPositiveClass (Signed.negative magnitude) = refl

singletonNegativeClass :
  (weight : Signed.SignedMagnitudeBits) →
  Factor.negativeFactorTotal
    ((weight , Factor.binaryOne) ∷ []) ≡ negativeTokenValue weight
singletonNegativeClass (Signed.positive magnitude) = refl
singletonNegativeClass (Signed.negative magnitude) =
  trans
    (NatP.+-identityʳ (Value.valueLE (reverse magnitude) *
                       Value.valueLE Factor.binaryOne))
    (NatP.*-identityʳ (Value.valueLE (reverse magnitude)))

-- The actual classifier's branching is used, not an assumed oracle.
insertPositivePreservesTotal :
  (weight : Signed.SignedMagnitudeBits)
  (classes : Factor.SignedTraceFactors) →
  Factor.positiveFactorTotal (Factor.addOccurrence weight classes) ≡
  positiveTokenValue weight + Factor.positiveFactorTotal classes
insertPositivePreservesTotal weight [] =
  trans (singletonPositiveClass weight)
        (sym (NatP.+-identityʳ (positiveTokenValue weight)))
insertPositivePreservesTotal weight ((candidate , count) ∷ rest)
  with Factor.sameSignedToken weight candidate in matching
... | true =
  trans
    (cong (λ n → n + Factor.positiveFactorTotal rest)
      (incrementPositiveClass candidate count))
    (trans
      (NatP.+-assoc
        (positiveTokenValue candidate)
        (Factor.positiveClassTotal (candidate , count))
        (Factor.positiveFactorTotal rest))
      (cong
        (λ x → x +
          (Factor.positiveClassTotal (candidate , count) +
           Factor.positiveFactorTotal rest))
        (cong positiveTokenValue
          (sym (Factor.sameSignedTokenSound weight candidate matching)))))
... | false =
  trans
    (cong
      (λ n → Factor.positiveClassTotal (candidate , count) + n)
      (insertPositivePreservesTotal weight rest))
    (commuteIntoSum
      (Factor.positiveClassTotal (candidate , count))
      (positiveTokenValue weight)
      (Factor.positiveFactorTotal rest))

insertNegativePreservesTotal :
  (weight : Signed.SignedMagnitudeBits)
  (classes : Factor.SignedTraceFactors) →
  Factor.negativeFactorTotal (Factor.addOccurrence weight classes) ≡
  negativeTokenValue weight + Factor.negativeFactorTotal classes
insertNegativePreservesTotal weight [] =
  trans (singletonNegativeClass weight)
        (sym (NatP.+-identityʳ (negativeTokenValue weight)))
insertNegativePreservesTotal weight ((candidate , count) ∷ rest)
  with Factor.sameSignedToken weight candidate in matching
... | true =
  trans
    (cong (λ n → n + Factor.negativeFactorTotal rest)
      (incrementNegativeClass candidate count))
    (trans
      (NatP.+-assoc
        (negativeTokenValue candidate)
        (Factor.negativeClassTotal (candidate , count))
        (Factor.negativeFactorTotal rest))
      (cong
        (λ x → x +
          (Factor.negativeClassTotal (candidate , count) +
           Factor.negativeFactorTotal rest))
        (cong negativeTokenValue
          (sym (Factor.sameSignedTokenSound weight candidate matching)))))
... | false =
  trans
    (cong
      (λ n → Factor.negativeClassTotal (candidate , count) + n)
      (insertNegativePreservesTotal weight rest))
    (commuteIntoSum
      (Factor.negativeClassTotal (candidate , count))
      (negativeTokenValue weight)
      (Factor.negativeFactorTotal rest))

factorPositiveTotalCorrect :
  (tokens : List Signed.SignedMagnitudeBits) →
  Factor.positiveFactorTotal (Factor.factorSignedTrace tokens) ≡
    Ledger.sumPositive tokens
factorPositiveTotalCorrect [] = refl
factorPositiveTotalCorrect (Signed.positive mag ∷ rest) =
  trans
    (insertPositivePreservesTotal (Signed.positive mag)
      (Factor.factorSignedTrace rest))
    (cong (λ n → Value.valueLE (reverse mag) + n)
      (factorPositiveTotalCorrect rest))
factorPositiveTotalCorrect (Signed.negative mag ∷ rest) =
  trans
    (insertPositivePreservesTotal (Signed.negative mag)
      (Factor.factorSignedTrace rest))
    (factorPositiveTotalCorrect rest)

factorNegativeTotalCorrect :
  (tokens : List Signed.SignedMagnitudeBits) →
  Factor.negativeFactorTotal (Factor.factorSignedTrace tokens) ≡
    Ledger.sumNegative tokens
factorNegativeTotalCorrect [] = refl
factorNegativeTotalCorrect (Signed.positive mag ∷ rest) =
  trans
    (insertNegativePreservesTotal (Signed.positive mag)
      (Factor.factorSignedTrace rest))
    (factorNegativeTotalCorrect rest)
factorNegativeTotalCorrect (Signed.negative mag ∷ rest) =
  trans
    (insertNegativePreservesTotal (Signed.negative mag)
      (Factor.factorSignedTrace rest))
    (cong (λ n → Value.valueLE (reverse mag) + n)
      (factorNegativeTotalCorrect rest))

-- The executable ORIGINAL binary signed ledger and the executable
-- FACTORED trace replay have precisely the same two Nat observations.
-- This does not run a Nat arithmetic operation in either executable.
factorReplayPositiveEqualsOriginalLedger :
  (tokens : List Signed.SignedMagnitudeBits) →
  Ledger.positiveValue (Factor.replaySignedTrace tokens) ≡
    Ledger.positiveValue
      (Ledger.accumulateSigned tokens Ledger.emptyLedger)
factorReplayPositiveEqualsOriginalLedger tokens =
  trans
    (trans
      (Factor.replayFactorsPositiveValue
        (Factor.factorSignedTrace tokens) Ledger.emptyLedger)
      (factorPositiveTotalCorrect tokens))
    (sym (Ledger.accumulateEmptyPositive tokens))

factorReplayNegativeEqualsOriginalLedger :
  (tokens : List Signed.SignedMagnitudeBits) →
  Ledger.negativeValue (Factor.replaySignedTrace tokens) ≡
    Ledger.negativeValue
      (Ledger.accumulateSigned tokens Ledger.emptyLedger)
factorReplayNegativeEqualsOriginalLedger tokens =
  trans
    (trans
      (Factor.replayFactorsNegativeValue
        (Factor.factorSignedTrace tokens) Ledger.emptyLedger)
      (factorNegativeTotalCorrect tokens))
    (sym (Ledger.accumulateEmptyNegative tokens))
