module DASHI.Biology.TraumaSensitiveDeriveExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.OrientedZeroJetTransitionExact as Jet
import DASHI.Biology.PsychogeographicFieldExact as Field

------------------------------------------------------------------------
-- A derive is constrained by agency and a workable window.  Failure to cross
-- a threshold can still be productive semantic movement while physical
-- position remains unchanged.
------------------------------------------------------------------------

data RegulationWindow : Set where
  underloadWindow : RegulationWindow
  workableWindow : RegulationWindow
  overloadWindow : RegulationWindow

record AdmissibleMove : Set where
  constructor admissibleMove
  field
    physicallyPossible : Bool
    physicallyPossibleIsTrue : physicallyPossible ≡ true
    consented : Bool
    consentedIsTrue : consented ≡ true
    window : RegulationWindow
    forcedExposure : Bool
    forcedExposureIsFalse : forcedExposure ≡ false
    destination : Field.Site
    moveReceipt : String

open AdmissibleMove public

canonicalSafeApproach : AdmissibleMove
canonicalSafeApproach =
  admissibleMove true refl true refl workableWindow false refl
    Field.churchSite
    "approach permitted; crossing not compelled"

data AttemptOutcome : Set where
  crossedThreshold : AttemptOutcome
  productiveFailure : AttemptOutcome
  withdrewSafely : AttemptOutcome

data SemanticState : Set where
  unchangedMeaning : SemanticState
  newNarrativeEdge : SemanticState
  expandedActionChoice : SemanticState

data PhysicalPosition : Set where
  outsideThreshold : PhysicalPosition
  insideThreshold : PhysicalPosition

outcomePosition : AttemptOutcome → PhysicalPosition
outcomePosition crossedThreshold = insideThreshold
outcomePosition productiveFailure = outsideThreshold
outcomePosition withdrewSafely = outsideThreshold

outcomeMeaning : AttemptOutcome → SemanticState
outcomeMeaning crossedThreshold = expandedActionChoice
outcomeMeaning productiveFailure = newNarrativeEdge
outcomeMeaning withdrewSafely = unchangedMeaning

outcomeJet : AttemptOutcome → Jet.OrientedSecondJet
outcomeJet crossedThreshold = Jet.negativeToPositiveCrossingJet
outcomeJet productiveFailure = Jet.negativeApproachJet
outcomeJet withdrewSafely = Jet.negativeReflectionJet

productiveFailureKeepsPhysicalPosition :
  outcomePosition productiveFailure ≡ outcomePosition withdrewSafely
productiveFailureKeepsPhysicalPosition = refl

productiveFailureChangesSemanticState :
  ¬ (outcomeMeaning productiveFailure ≡ outcomeMeaning withdrewSafely)
productiveFailureChangesSemanticState ()

crossingAndProductiveFailureShareCoarseThreshold :
  Jet.coarseJetPosition (outcomeJet crossedThreshold)
  ≡ Jet.coarseJetPosition (outcomeJet productiveFailure)
crossingAndProductiveFailureShareCoarseThreshold = refl

crossingAndProductiveFailureRetainDifferentPassageKinds :
  ¬ (Jet.passage (outcomeJet crossedThreshold)
     ≡ Jet.passage (outcomeJet productiveFailure))
crossingAndProductiveFailureRetainDifferentPassageKinds ()

record TraumaSensitiveDeriveBoundary : Set where
  constructor traumaSensitiveDeriveBoundary
  field
    blockedCrossingMeansNoChange : Bool
    blockedCrossingMeansNoChangeIsFalse :
      blockedCrossingMeansNoChange ≡ false
    consentMayBeReplacedByRouteAvailability : Bool
    consentMayBeReplacedByRouteAvailabilityIsFalse :
      consentMayBeReplacedByRouteAvailability ≡ false
    coarseThresholdPositionDeterminesPassage : Bool
    coarseThresholdPositionDeterminesPassageIsFalse :
      coarseThresholdPositionDeterminesPassage ≡ false
    finiteWindowIsClinicalExposureProtocol : Bool
    finiteWindowIsClinicalExposureProtocolIsFalse :
      finiteWindowIsClinicalExposureProtocol ≡ false

canonicalTraumaSensitiveDeriveBoundary : TraumaSensitiveDeriveBoundary
canonicalTraumaSensitiveDeriveBoundary =
  traumaSensitiveDeriveBoundary false refl false refl false refl false refl
