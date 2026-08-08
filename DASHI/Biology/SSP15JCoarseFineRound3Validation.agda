module DASHI.Biology.SSP15JCoarseFineRound3Validation where

import DASHI.Biology.StageEulerTreeComplementRound2Validation
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Quotient
import DASHI.Biology.SSP15ComplementPhaseProjectorExact as Internal
import DASHI.Biology.OggPrimeNonaryAddressExact as Address
import DASHI.Biology.JCoarseFineEvaluationFibreExact as J
import DASHI.Biology.SSP15NineObserverAtlasExact as Atlas
import DASHI.Biology.SSP15JCoarseFineIntegratedExact as Integrated
import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (_+_; _*_)

completionQuotientRoundTrip :
  (state : Quotient.DecimalCompletionState) →
  Quotient.decodeModePhase (Quotient.encodeModePhase state) ≡ state
completionQuotientRoundTrip = Quotient.decodeAfterEncode

completionFlipsBinaryPhase :
  (state : Quotient.DecimalCompletionState) →
  Quotient.binaryPhase (Quotient.complementState state)
  ≡ Quotient.flipBinaryPhase (Quotient.binaryPhase state)
completionFlipsBinaryPhase = Quotient.complementFlipsBinaryPhase

internalSSP15HasFifteenLanes :
  Internal.listCount Internal.canonicalSSP15InternalLanes ≡ 15
internalSSP15HasFifteenLanes = Internal.ssp15InternalLaneCountIsFifteen

internalProjectorOwnsLane :
  (lane : Internal.SSP15InternalLane) →
  Internal.laneProjectorCoefficient lane lane ≡ 1
internalProjectorOwnsLane = Internal.laneProjectorOwnCoefficient

phaseReversalTransportsProjectors :
  (selected actual : Internal.SSP15InternalLane) →
  Internal.laneProjectorCoefficient
    (Internal.reverseLane selected) (Internal.reverseLane actual)
  ≡ Internal.laneProjectorCoefficient selected actual
phaseReversalTransportsProjectors = Internal.laneProjectorReverseCovariant

allOggAddressesReconstructTheirPrime :
  (prime : Lane.MonsterPrimeLane) →
  Lane.monsterPrimeLaneToNat prime
  ≡ Address.coarseSheets (Address.nonaryOggAddress prime) * 9
    + Address.remainder (Address.nonaryOggAddress prime)
allOggAddressesReconstructTheirPrime prime =
  Address.addressExact (Address.nonaryOggAddress prime)

p71IsSevenSheetsPlusEight :
  Lane.monsterPrimeLaneToNat Lane.p71 ≡ 7 * 9 + 8
p71IsSevenSheetsPlusEight = refl

p71RemovesBinaryFiveInterface : 71 + 5 * 2 ≡ 81
p71RemovesBinaryFiveInterface =
  Integrated.seventyOneRemovesBinaryFiveInterface

p41IsDepthTwoPhaseMidpointDivisionFree : 2 * 41 ≡ 81 + 1
p41IsDepthTwoPhaseMidpointDivisionFree =
  Address.fortyOneIsHalfOfPointedEightyOneDivisionFree

jEvaluationHasSection :
  (fine : Harmonic.FineFrequency) →
  Harmonic.jFine (J.constantFineAssignment fine) ≡ fine
jEvaluationHasSection = J.constantAssignmentEvaluatesAtJ

primeSpecificObserverMatchesP47 :
  Atlas.observedValue
    (Integrated.nineObserver
      (Integrated.primeSpecificSSP15Reading Lane.p47))
  ≡ 47
primeSpecificObserverMatchesP47 = refl

pointedSignedChainReachesFortySeven :
  Atlas.pointedSignedCardinalityValue 23 ≡ 47
pointedSignedChainReachesFortySeven =
  Atlas.pointedSignedTwentyThreeIsFortySeven
