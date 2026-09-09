module DASHI.ComputerScience.TernaryResidualBinaryDecisionRefinementExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Codec.BalancedTritBitFibre as Fibre
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.ComputerScience.TinyRadixNeutralRegisterMachineExact as Machine
import DASHI.ComputerScience.EuclidGCDRegisterMachineExact as Euclid

------------------------------------------------------------------------
-- TERNARY RESIDUAL REFINEMENT OF A BINARY QUOTIENT
--
-- The repo's balanced-trit fibre is exactly a support bit plus a retained
-- optional sign residual.  The one-bit support quotient collapses neg and pos;
-- the full recoverable fibre does not.
------------------------------------------------------------------------

supportObserver : Trit → Bool
supportObserver t = Fibre.supportBit (Fibre.encodeFibre t)

signSensitiveConsumer : Trit → Bool
signSensitiveConsumer neg = false
signSensitiveConsumer zer = false
signSensitiveConsumer pos = true

supportNegEqualsSupportPos : supportObserver neg ≡ supportObserver pos
supportNegEqualsSupportPos = refl

signConsumerNegDiffersFromPos :
  signSensitiveConsumer neg ≡ signSensitiveConsumer pos → ⊥
signConsumerNegDiffersFromPos ()

supportNonDescentWitness :
  Descent.ConsumerNonDescentWitness supportObserver signSensitiveConsumer
supportNonDescentWitness =
  Descent.consumerNonDescentWitness
    neg
    pos
    supportNegEqualsSupportPos
    signConsumerNegDiffersFromPos

fullFibreObserver : Trit → Fibre.TritFibre
fullFibreObserver = Fibre.encodeFibre

fullFibreSeparates :
  (left right : Trit) →
  fullFibreObserver left ≡ fullFibreObserver right →
  left ≡ right
fullFibreSeparates left right same =
  trans
    (sym (Fibre.decode-encode left))
    (trans
      (cong Fibre.decodeFibre same)
      (Fibre.decode-encode right))

fullFibreSufficientForSignConsumer :
  Descent.ConsumerSufficient fullFibreObserver signSensitiveConsumer
fullFibreSufficientForSignConsumer left right same =
  cong signSensitiveConsumer (fullFibreSeparates left right same)

------------------------------------------------------------------------
-- THREE-WAY BOUNDED PROGRAM STATUS
--
-- pos : bounded execution halted and the declared Boolean property holds
-- neg : bounded execution halted and the declared Boolean property fails
-- zer : execution has not halted within the supplied fuel, so the semantic
--       property is not promoted to true or false yet.
--
-- This is epistemic/consumer refinement.  It is NOT a non-halting decider.
------------------------------------------------------------------------

BoundedBoolProperty : Set
BoundedBoolProperty = Machine.MachineState → Bool

boundedDecisionTrit :
  Nat →
  BoundedBoolProperty →
  Machine.MachineState →
  Trit
boundedDecisionTrit fuel property start
  with Machine.halted (Machine.runFuel fuel start)
... | false = zer
... | true with property (Machine.runFuel fuel start)
...   | false = neg
...   | true = pos

-- Legacy binary truth projection: both a proved-false result and an unresolved
-- result appear as false.  The ternary carrier keeps those cases distinct.
legacyBinaryTruth : Trit → Bool
legacyBinaryTruth neg = false
legacyBinaryTruth zer = false
legacyBinaryTruth pos = true

legacyBinaryConflatesNegativeAndUnresolved :
  legacyBinaryTruth neg ≡ legacyBinaryTruth zer
legacyBinaryConflatesNegativeAndUnresolved = refl

legacyTruthNonDescentWitness :
  Descent.ConsumerNonDescentWitness legacyBinaryTruth (λ t → t)
legacyTruthNonDescentWitness =
  Descent.consumerNonDescentWitness
    neg
    zer
    refl
    (λ ())

------------------------------------------------------------------------
-- Same-object Euclid regressions.
------------------------------------------------------------------------

r0IsSix : BoundedBoolProperty
r0IsSix state = Machine.equalNat (Machine.reg0 (Machine.registers state)) 6

r0IsOne : BoundedBoolProperty
r0IsOne state = Machine.equalNat (Machine.reg0 (Machine.registers state)) 1

euclidInitiallyUnresolved :
  boundedDecisionTrit 0 r0IsSix (Euclid.euclidInitialState 48 18) ≡ zer
euclidInitiallyUnresolved = refl

euclidAt19ProvesR0IsSix :
  boundedDecisionTrit 19 r0IsSix (Euclid.euclidInitialState 48 18) ≡ pos
euclidAt19ProvesR0IsSix = refl

euclidAt19ProvesR0IsNotOne :
  boundedDecisionTrit 19 r0IsOne (Euclid.euclidInitialState 48 18) ≡ neg
euclidAt19ProvesR0IsNotOne = refl

-- The binary false surface cannot tell the latter two epistemic situations
-- apart when the input trit is neg versus zer; the ternary status can.

data TernaryRefinementIsUniversalHaltingDecider : Set where
data TernaryCarrierHasGreaterTuringComputabilityThanBinary : Set where
data OneBitBinaryQuotientEqualsAllBinaryEncodings : Set where

ternaryRefinementDoesNotSolveUniversalHalting :
  TernaryRefinementIsUniversalHaltingDecider → ⊥
ternaryRefinementDoesNotSolveUniversalHalting ()

ternaryDoesNotGainTuringComputabilityByRadixAlone :
  TernaryCarrierHasGreaterTuringComputabilityThanBinary → ⊥
ternaryDoesNotGainTuringComputabilityByRadixAlone ()

oneBitQuotientIsNotAllBinaryRepresentation :
  OneBitBinaryQuotientEqualsAllBinaryEncodings → ⊥
oneBitQuotientIsNotAllBinaryRepresentation ()

record TernaryResidualBinaryDecisionBoundary : Set where
  constructor ternaryResidualBinaryDecisionBoundary
  field
    oneBitSupportCanLoseSign : Bool
    fullTritFibreRecoversSignSensitiveConsumer : Bool
    boundedThreeWayStatusExecutable : Bool
    unresolvedSeparateFromProvedFalse : Bool
    sameEuclidStateMovesFromUnresolvedToPositiveWithMoreFuel : Bool
    ternaryClaimedAsUniversalHaltingDecider : Bool
    ternaryClaimedAsStrictlyMoreTuringComputableThanBinary : Bool

canonicalTernaryResidualBinaryDecisionBoundary :
  TernaryResidualBinaryDecisionBoundary
canonicalTernaryResidualBinaryDecisionBoundary =
  ternaryResidualBinaryDecisionBoundary
    true true true true true false false
