module DASHI.Mathematics.Complexity.PNotEqualsNPBinaryCountdownCostExact where

------------------------------------------------------------------------
-- EXACT WORK BOUND FOR THE XOR / RIPPLE-BORROW COUNTDOWN
--
-- Attribution / authority boundary:
--
-- The sibling IIT/XOR-grid work motivates looking at XOR as an information-
-- preserving local update.  No IIT theorem or phi value is imported here as
-- complexity authority.  The Boolean/ripple semantics used below are the
-- locally reproved DASHI complexity owner
-- `PNotEqualsNPXORCountdownMicrocodeExact`.
--
-- The literal three-rule finite-TM fragment in
-- `PNotEqualsNPBinaryCountdownRuleFragmentExact` scans little-endian bits until
-- the borrow resolves on the first 1, or reaches the end marker and underflows.
-- Therefore one decrement needs at most
--
--     bitWidth + 1
--
-- timer transitions.  The +1 is the resolving/underflow transition.  The bound
-- is tight on an all-zero word, where every bit is visited and the end marker is
-- then consumed.
--
-- This pays the arithmetic cost coordinate for the compact timer option.  It
-- does NOT yet prove the arbitrary-word StandardExactRun correspondence, nor
-- the head-travel cost of integrating this timer with a separate candidate
-- work region on one physical tape.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.Product using (_,_)

import DASHI.Mathematics.Complexity.PNotEqualsNPXORCountdownMicrocodeExact as XOR

------------------------------------------------------------------------
-- 1. Width and literal transition work for one decrement pass.
------------------------------------------------------------------------

bitWidth : List Bool → Nat
bitWidth [] = zero
bitWidth (_ ∷ rest) = suc (bitWidth rest)

-- The rule fragment performs one transition at the first 1, or one transition
-- on the end marker after propagating borrow across an all-zero suffix.
countdownWork : List Bool → Nat
countdownWork [] = suc zero
countdownWork (false ∷ rest) = suc (countdownWork rest)
countdownWork (true ∷ rest) = suc zero

------------------------------------------------------------------------
-- 2. Exact worst-case bound.
------------------------------------------------------------------------

countdownWorkBound :
  (bits : List Bool) →
  countdownWork bits ≤ suc (bitWidth bits)
countdownWorkBound [] = s≤s z≤n
countdownWorkBound (false ∷ rest) =
  s≤s (countdownWorkBound rest)
countdownWorkBound (true ∷ rest) =
  s≤s z≤n

------------------------------------------------------------------------
-- 3. The width+1 bound is attained on all-zero timer words.
------------------------------------------------------------------------

zeroWord : Nat → List Bool
zeroWord zero = []
zeroWord (suc n) = false ∷ zeroWord n

zeroWordWidth :
  (n : Nat) →
  bitWidth (zeroWord n) ≡ n
zeroWordWidth zero = refl
zeroWordWidth (suc n)
  rewrite zeroWordWidth n = refl

allZeroWorkExact :
  (n : Nat) →
  countdownWork (zeroWord n) ≡ suc n
allZeroWorkExact zero = refl
allZeroWorkExact (suc n)
  rewrite allZeroWorkExact n = refl

------------------------------------------------------------------------
-- 4. Small executable fixtures agree with the existing ripple semantics.
------------------------------------------------------------------------

-- 1 = [1]: resolve immediately.
decrementOneWork :
  countdownWork (true ∷ []) ≡ suc zero
decrementOneWork = refl

-- 2 = [0,1]: propagate once, then resolve.
decrementTwoWork :
  countdownWork (false ∷ true ∷ []) ≡ suc (suc zero)
decrementTwoWork = refl

-- 4 = [0,0,1]: propagate twice, then resolve.
decrementFourWork :
  countdownWork (false ∷ false ∷ true ∷ [])
    ≡ suc (suc (suc zero))
decrementFourWork = refl

-- Keep the semantic owner visibly attached: these are the same fixtures whose
-- output values are proved by the XOR/ripple semantics module.
decrementOneSemanticReceipt :
  XOR.countdownOne (true ∷ []) ≡ (false ∷ []) , false
decrementOneSemanticReceipt = XOR.decrementOne

decrementTwoSemanticReceipt :
  XOR.countdownOne (false ∷ true ∷ [])
    ≡ (true ∷ false ∷ []) , false
decrementTwoSemanticReceipt = XOR.decrementTwo

decrementFourSemanticReceipt :
  XOR.countdownOne (false ∷ false ∷ true ∷ [])
    ≡ (true ∷ true ∷ false ∷ []) , false
decrementFourSemanticReceipt = XOR.decrementFour

------------------------------------------------------------------------
-- 5. Max-cut / Pareto boundary.
------------------------------------------------------------------------

record BinaryCountdownCostBoundary : Set where
  constructor binary-countdown-cost-boundary
  field
    localXORBorrowSemanticsPaid : Bool
    literalThreeRuleFragmentPaid : Bool
    singleDecrementWidthPlusOneBoundPaid : Bool
    widthPlusOneWorstCaseIsTight : Bool
    arbitraryWordStandardRunStillRequired : Bool
    candidateTimerHeadTravelStillRequired : Bool
    wholeTargetSameBudgetClosureStillRequired : Bool
    iitPhiIsComplexityLowerBound : Bool

open BinaryCountdownCostBoundary public

canonicalBinaryCountdownCostBoundary : BinaryCountdownCostBoundary
canonicalBinaryCountdownCostBoundary =
  binary-countdown-cost-boundary
    true true true true
    true true true false

countdownCostDoesNotCloseWholeTimer :
  wholeTargetSameBudgetClosureStillRequired
    canonicalBinaryCountdownCostBoundary ≡ true
countdownCostDoesNotCloseWholeTimer = refl

iitStillDoesNotCreateLowerBound :
  iitPhiIsComplexityLowerBound canonicalBinaryCountdownCostBoundary ≡ false
iitStillDoesNotCreateLowerBound = refl
