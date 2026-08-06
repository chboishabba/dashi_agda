module DASHI.Biology.FRACTRANSSPTransitionExact where

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)

import DASHI.Geometry.SSP369Ultrametric as SSP
import DASHI.Biology.OrientedZeroWaveTransitionExact as Zero
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed

------------------------------------------------------------------------
-- Legacy four-coordinate projection retained for backwards compatibility.
-- The complete machine is SignedSSPFRACTRANWeaveExact: all fifteen SSP lanes,
-- signed denominator/numerator orientation, 3/6/9 addresses, and the canonical
-- reduced-fibre 53 construction.  The local 53 -> 47 rule below is only a
-- finite projection example and is not the canonical interpretation of 53.

record PrimeValuationState : Set where
  constructor primeValuationState
  field
    exponent47 : Nat
    exponent53 : Nat
    exponent59 : Nat
    exponent71 : Nat
    address369 : SSP.Address 3
    zeroApproachResidual : Zero.ApproachDirection

open PrimeValuationState public

canonicalSSPAddress : SSP.Address 3
canonicalSSPAddress =
  SSP.digit3 vcons SSP.digit6 vcons SSP.digit9 vcons vnil

data FRACTRANRule : Set where
  transfer47To59 : FRACTRANRule
  transfer59To71 : FRACTRANRule
  transfer71To47 : FRACTRANRule
  residual53To47 : FRACTRANRule

ruleEnabled : FRACTRANRule → PrimeValuationState → Bool
ruleEnabled transfer47To59 (primeValuationState zero b c d addr dir) = false
ruleEnabled transfer47To59 (primeValuationState (suc a) b c d addr dir) = true
ruleEnabled transfer59To71 (primeValuationState a b zero d addr dir) = false
ruleEnabled transfer59To71 (primeValuationState a b (suc c) d addr dir) = true
ruleEnabled transfer71To47 (primeValuationState a b c zero addr dir) = false
ruleEnabled transfer71To47 (primeValuationState a b c (suc d) addr dir) = true
ruleEnabled residual53To47 (primeValuationState a zero c d addr dir) = false
ruleEnabled residual53To47 (primeValuationState a (suc b) c d addr dir) = true

applyRule : FRACTRANRule → PrimeValuationState → PrimeValuationState
applyRule transfer47To59 (primeValuationState zero b c d addr dir) =
  primeValuationState zero b c d addr dir
applyRule transfer47To59 (primeValuationState (suc a) b c d addr dir) =
  primeValuationState a b (suc c) d addr Zero.fromPositive
applyRule transfer59To71 (primeValuationState a b zero d addr dir) =
  primeValuationState a b zero d addr dir
applyRule transfer59To71 (primeValuationState a b (suc c) d addr dir) =
  primeValuationState a b c (suc d) addr Zero.fromPositive
applyRule transfer71To47 (primeValuationState a b c zero addr dir) =
  primeValuationState a b c zero addr dir
applyRule transfer71To47 (primeValuationState a b c (suc d) addr dir) =
  primeValuationState (suc a) b c d addr Zero.fromPositive
applyRule residual53To47 (primeValuationState a zero c d addr dir) =
  primeValuationState a zero c d addr dir
applyRule residual53To47 (primeValuationState a (suc b) c d addr dir) =
  primeValuationState (suc a) b c d addr Zero.fromPositive

canonicalPrimeState : PrimeValuationState
canonicalPrimeState =
  primeValuationState 1 1 0 0 canonicalSSPAddress Zero.fromNegative

firstCanonicalTransfer : PrimeValuationState
firstCanonicalTransfer = applyRule transfer47To59 canonicalPrimeState

firstCanonicalTransferIsExact :
  firstCanonicalTransfer
  ≡ primeValuationState 0 1 1 0 canonicalSSPAddress Zero.fromPositive
firstCanonicalTransferIsExact = refl

secondCanonicalTransfer : PrimeValuationState
secondCanonicalTransfer = applyRule transfer59To71 firstCanonicalTransfer

secondCanonicalTransferIsExact :
  secondCanonicalTransfer
  ≡ primeValuationState 0 1 0 1 canonicalSSPAddress Zero.fromPositive
secondCanonicalTransferIsExact = refl

thirdCanonicalTransfer : PrimeValuationState
thirdCanonicalTransfer = applyRule transfer71To47 secondCanonicalTransfer

threeStepCycleReturnsOggOccupancy :
  exponent47 thirdCanonicalTransfer ≡ 1
  × exponent59 thirdCanonicalTransfer ≡ 0
  × exponent71 thirdCanonicalTransfer ≡ 0
threeStepCycleReturnsOggOccupancy = refl , (refl , refl)

sspAddressIsPreservedByPrimeTransport :
  address369 thirdCanonicalTransfer ≡ canonicalSSPAddress
sspAddressIsPreservedByPrimeTransport = refl

residualPrimeCanEnterOggCycle :
  applyRule residual53To47
    (primeValuationState 0 1 0 0 canonicalSSPAddress Zero.fromNegative)
  ≡
  primeValuationState 1 0 0 0 canonicalSSPAddress Zero.fromPositive
residualPrimeCanEnterOggCycle = refl

------------------------------------------------------------------------
-- Typed first-enabled execution over a fixed rule priority.

firstEnabledStep : PrimeValuationState → PrimeValuationState
firstEnabledStep state with ruleEnabled transfer47To59 state
... | true = applyRule transfer47To59 state
... | false with ruleEnabled transfer59To71 state
...   | true = applyRule transfer59To71 state
...   | false with ruleEnabled transfer71To47 state
...     | true = applyRule transfer71To47 state
...     | false = applyRule residual53To47 state

canonicalPriorityUses47To59 :
  firstEnabledStep canonicalPrimeState ≡ firstCanonicalTransfer
canonicalPriorityUses47To59 = refl

------------------------------------------------------------------------
-- Completion bridge to the full fifteen-lane signed weave.

completeSignedSSPBoundary : Signed.SignedSSPWeaveBoundary
completeSignedSSPBoundary = Signed.canonicalSignedSSPWeaveBoundary

completeSignedSSPPrimeCountIsFifteen :
  Signed.listCount Signed.canonicalSSPPrimes ≡ 15
completeSignedSSPPrimeCountIsFifteen =
  Signed.canonicalSSPPrimeCountIsFifteen

canonicalReducedFiftyThreeProgramLengthIsTwo :
  Signed.listCount Signed.canonicalGeometricFiftyThreeProgram ≡ 2
canonicalReducedFiftyThreeProgramLengthIsTwo =
  Signed.geometricProgramLengthIsTwo

record FRACTRANSSPBoundary : Set where
  constructor fractranSSPBoundary
  field
    oggChannelsWereDerivedFromSSPAlone : Bool
    oggChannelsWereDerivedFromSSPAloneIsFalse :
      oggChannelsWereDerivedFromSSPAlone ≡ false

    priorityProgramConstructsMonsterAction : Bool
    priorityProgramConstructsMonsterActionIsFalse :
      priorityProgramConstructsMonsterAction ≡ false

    primeValuationTransportErasesAddressType : Bool
    primeValuationTransportErasesAddressTypeIsFalse :
      primeValuationTransportErasesAddressType ≡ false

    finiteRuleExampleProvesUniversalComputation : Bool
    finiteRuleExampleProvesUniversalComputationIsFalse :
      finiteRuleExampleProvesUniversalComputation ≡ false

open FRACTRANSSPBoundary public

canonicalFRACTRANSSPBoundary : FRACTRANSSPBoundary
canonicalFRACTRANSSPBoundary =
  fractranSSPBoundary false refl false refl false refl false refl
