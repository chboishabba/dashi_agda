{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21NativeThresholdOriginalSignedDecisionExact where

------------------------------------------------------------------------
-- P0-E: ORIGINAL binary threshold decision -> signed original ℤ.
--
-- Genuine comparator atLeast and ripple addBits execute bitwise.
-- Proof only: Value.valueLE, Nat.<=b and Int.<=b.
--
-- Key integer arithmetic for ALL Nat P,N,W:
--      Nat.(N + W <=b P)
--  === Int.(+W <=b ((+P) + (- (+N))))
--
-- There is NO runtime unary conversion or integer subtraction in the
-- bit-native validator. Uses original Data.Integer.Base definitions,
-- existing Karp compareLE trichotomy and ripple-adder value theorem.
-- Exact-head Agda kernel check remains independently necessary.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import Data.Nat.Base as Nat
import Data.Integer.Base as Int
import Data.Integer.Properties as IntP

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21BinaryNativeThresholdExact as Compare
import DASHI.Mathematics.Complexity.Karp21BinaryNativeThresholdNumericalExact as Correct
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderExact as Add
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact as Value
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact as Ledger
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact as Positive
import DASHI.Mathematics.Complexity.Karp21NativeLedgerIntegerScoreExact as IntegerLedger

-- Small constructive Nat boolean order algebra. No use of an
-- untrusted compare function. All recursion is on the Nat proof
-- observation, not on the executable bit parser.
natLessThanSuccessor :
  (n gap : Nat) →
  Nat._≤ᵇ_ n (suc (n + gap)) ≡ true
natLessThanSuccessor zero gap = refl
natLessThanSuccessor (suc n) gap =
  natLessThanSuccessor n gap

natSuccessorGreater :
  (n gap : Nat) →
  Nat._≤ᵇ_ (suc (n + gap)) n ≡ false
natSuccessorGreater zero gap = refl
natSuccessorGreater (suc n) gap =
  natSuccessorGreater n gap

natAtLeastReflexive :
  (n : Nat) →
  Nat._≤ᵇ_ n n ≡ true
natAtLeastReflexive zero = refl
natAtLeastReflexive (suc n) = natAtLeastReflexive n

-- The ACTUAL original compareLE atLeast Boolean, not a new
-- comparator, numerically reflects the VALUE of its bit operands.
compareAtLeastNumericalBoolean :
  (xs ys : Word.BitWord) →
  Compare.atLeast xs ys
    ≡ Nat._≤ᵇ_ (Value.valueLE ys) (Value.valueLE xs)
compareAtLeastNumericalBoolean xs ys
  with Compare.compareLE xs ys
     | Correct.compareLENumericalCorrect xs ys
... | Compare.less | (gap , equation)
  rewrite equation =
  sym (natSuccessorGreater (Value.valueLE xs) gap)
... | Compare.equal | equation
  rewrite equation =
  sym (natAtLeastReflexive (Value.valueLE xs))
... | Compare.greater | (gap , equation)
  rewrite equation =
  sym (natLessThanSuccessor (Value.valueLE ys) gap)

-- Nat signed mass p-n is exactly Int (+p)+(-( +n)), including n=0.
intSignedDifferenceAsNatOminus :
  (p n : Nat) →
  Int._+_ (Int.+ p) (Int.- (Int.+ n))
    ≡ Int._⊖_ p n
intSignedDifferenceAsNatOminus zero zero = refl
intSignedDifferenceAsNatOminus (suc p) zero = refl
intSignedDifferenceAsNatOminus p (suc n) = refl

-- Cancelling one positive and one negative unit leaves the signed
-- score unchanged. This is the same integer operation used by the
-- original Karp Fin-free rawSparseScore.
intSignedDifferenceSuccSucc :
  (p n : Nat) →
  Int._+_ (Int.+ (suc p)) (Int.- (Int.+ (suc n)))
    ≡ Int._+_ (Int.+ p) (Int.- (Int.+ n))
intSignedDifferenceSuccSucc p n =
  trans
    (IntP.[1+m]⊖[1+n]≡m⊖n p n)
    (sym (intSignedDifferenceAsNatOminus p n))

-- Full SIGNED threshold equivalence for arbitrary p,n,w, even w=0.
-- The original N21 word validator separately insists on W>0.
signedThresholdBoolean :
  (p n w : Nat) →
  Nat._≤ᵇ_ (n + w) p
    ≡ Int._≤ᵇ_ (Int.+ w)
        (Int._+_ (Int.+ p) (Int.- (Int.+ n)))
signedThresholdBoolean p zero w = refl
signedThresholdBoolean zero (suc n) w = refl
signedThresholdBoolean (suc p) (suc n) w =
  trans
    (signedThresholdBoolean p n w)
    (sym
      (cong (Int._≤ᵇ_ (Int.+ w))
        (intSignedDifferenceSuccSucc p n)))

-- The REAL N21 signed binary ledger threshold check is exactly the
-- original signed-integer >= W test as a theorem on its numerical
-- observation. This closes no parser or physical bit-clock premise.
karpNativeThresholdDecisionSameOriginal :
  (ledger : Ledger.SignedLedger)
  (thresholdLE : Word.BitWord) →
  Positive.meetsOriginalPositiveThreshold ledger thresholdLE
    ≡ Int._≤ᵇ_
        (Int.+ (Value.valueLE thresholdLE))
        (IntegerLedger.observeActualNativeLedger ledger)
karpNativeThresholdDecisionSameOriginal (positive , negative) thresholdLE =
  trans
    (compareAtLeastNumericalBoolean
      positive (Add.addBits negative thresholdLE))
    (trans
      (cong
        (λ value → Nat._≤ᵇ_ value (Value.valueLE positive))
        (Value.addBitsValue negative thresholdLE))
      (signedThresholdBoolean
        (Value.valueLE positive)
        (Value.valueLE negative)
        (Value.valueLE thresholdLE)))
