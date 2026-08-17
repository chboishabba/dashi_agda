module DASHI.Physics.Closure.NSTriadKNCriticalBlockSupportSeparationNoGoRound70Exact where

------------------------------------------------------------------------
-- ROUND 70 / BLOCK-INDEX SUPPORT-SEPARATION NO-GO
--
-- A tempting way around lossy Carleman propagation would be to argue that
-- large critical ratios at different block indices n already produce distinct
-- frequency concentration events.  The current C1 carrier does NOT justify
-- that inference: its Nat index is an abstract block index and carries no
-- support map or disjointness proof.
--
-- This file gives the exact structural countermodel.  For ANY canonical
-- positive critical block and ANY nonempty support carrier A, there is a valid
-- block-support assignment that maps every n to the same support.  In
-- particular supports at 0 and 1 coincide.  Therefore support separation must
-- be a new same-object PDE theorem; it cannot be obtained from the existence of
-- the Nat block index alone.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Physics.Closure.NSTriadKNCriticalRatioNormalizationRound63Exact as C1

record CriticalBlockSupportAssignment
    {balances block}
    (positiveBlock : C1.PositiveCriticalBlockScale balances block)
    (Support : Set) : Set where
  field
    supportAt : Nat → Support

open CriticalBlockSupportAssignment public

constantBlockSupportAssignment :
  ∀ {balances block}
    {positiveBlock : C1.PositiveCriticalBlockScale balances block}
    {Support : Set} →
  Support → CriticalBlockSupportAssignment positiveBlock Support
constantBlockSupportAssignment support = record
  { supportAt = λ n → support }

constantBlockSupportsZeroAndOneCoincide :
  ∀ {balances block}
    {positiveBlock : C1.PositiveCriticalBlockScale balances block}
    {Support : Set}
    (support : Support) →
  supportAt (constantBlockSupportAssignment {positiveBlock = positiveBlock} support) zero
  ≡
  supportAt (constantBlockSupportAssignment {positiveBlock = positiveBlock} support) (suc zero)
constantBlockSupportsZeroAndOneCoincide support = refl

round70BlockIndexAloneImpliesSupportSeparation : Bool
round70BlockIndexAloneImpliesSupportSeparation = false

round70BlockSupportSeparationNeedsPhysicalProducer : Bool
round70BlockSupportSeparationNeedsPhysicalProducer = true

round70BlockIndexAloneImpliesSupportSeparationIsFalse :
  round70BlockIndexAloneImpliesSupportSeparation ≡ false
round70BlockIndexAloneImpliesSupportSeparationIsFalse = refl

round70BlockSupportSeparationNeedsPhysicalProducerIsTrue :
  round70BlockSupportSeparationNeedsPhysicalProducer ≡ true
round70BlockSupportSeparationNeedsPhysicalProducerIsTrue = refl
