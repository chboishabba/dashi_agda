module DASHI.Education.DigitalESDEvidenceBraidTensionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed
import DASHI.Education.DigitalESDSourceAuditScaleExact as Scale

------------------------------------------------------------------------
-- EVIDENCE BRAID / TENSION
--
-- Different admissible observations can converge, complement, remain in
-- productive tension, or remain unresolved. No averaging/fusion is required.
------------------------------------------------------------------------

data BraidRelation : Set where
  convergence : BraidRelation
  complementarity : BraidRelation
  productiveTension : BraidRelation
  unresolvedConflict : BraidRelation
  scopeDifference : BraidRelation
  authorityDifference : BraidRelation
  provenanceDifference : BraidRelation
  prohibitedCollapse : BraidRelation

record TensionReceipt : Set where
  constructor tension-receipt
  field
    leftObservationRef : String
    rightObservationRef : String
    leftProvenanceRef : String
    rightProvenanceRef : String
    relation : BraidRelation
    reasonNotCollapsed : String

open TensionReceipt public

twoEyedBoundary : TwoEyed.KimmererTwoEyedSeeingBoundary
twoEyedBoundary = TwoEyed.canonicalKimmererTwoEyedSeeingBoundary

------------------------------------------------------------------------
-- Finite fixture: same operational availability, different situated access.
------------------------------------------------------------------------

data AvailabilityWorld : Set where
  highAvailabilityEffectiveAccess : AvailabilityWorld
  highAvailabilityBrokenAssistiveWorkflow : AvailabilityWorld

data AvailabilitySurface : Set where highAvailability : AvailabilitySurface

data AccessibilitySurface : Set where effectiveAccess brokenAccess : AccessibilitySurface

availabilityProjection : AvailabilityWorld → AvailabilitySurface
availabilityProjection highAvailabilityEffectiveAccess = highAvailability
availabilityProjection highAvailabilityBrokenAssistiveWorkflow = highAvailability

accessibilityProjection : AvailabilityWorld → AccessibilitySurface
accessibilityProjection highAvailabilityEffectiveAccess = effectiveAccess
accessibilityProjection highAvailabilityBrokenAssistiveWorkflow = brokenAccess

accessibilityDiffers :
  accessibilityProjection highAvailabilityEffectiveAccess ≡
  accessibilityProjection highAvailabilityBrokenAssistiveWorkflow → ⊥
accessibilityDiffers ()

availabilityCannotDetermineAccessibilityWitness :
  INF.NonFactorabilityWitness availabilityProjection accessibilityProjection
availabilityCannotDetermineAccessibilityWitness =
  INF.nonFactorabilityWitness
    highAvailabilityEffectiveAccess
    highAvailabilityBrokenAssistiveWorkflow
    refl
    accessibilityDiffers

availabilityCannotDetermineAccessibility :
  INF.FactorsThrough availabilityProjection accessibilityProjection → ⊥
availabilityCannotDetermineAccessibility =
  INF.witnessRulesOutEveryFlatFactorisation
    availabilityCannotDetermineAccessibilityWitness

availabilityAccessibilityTension : TensionReceipt
availabilityAccessibilityTension = tension-receipt
  "institutional service telemetry: high availability"
  "disabled/access-needs participant observation: assistive workflow broken after change"
  "institutional operational observer"
  "situated participant/access observer"
  productiveTension
  "Both observations may be admissible for different consumers. Averaging them would erase the distinction between operational availability and realised accessibility."

------------------------------------------------------------------------
-- No-promotion / no-fusion firewalls.
------------------------------------------------------------------------

data SharedObservationCreatesSameProvenance : Set where
data CoordinatedUseCreatesEpistemicFusion : Set where
data PluralObservationsCreateForcedConsensus : Set where
data DisagreementCreatesInvalidEvidence : Set where
data SharedScoreCreatesSameSituatedState : Set where

sharedObservationDoesNotCreateSameProvenance :
  SharedObservationCreatesSameProvenance → ⊥
sharedObservationDoesNotCreateSameProvenance ()

coordinatedUseDoesNotCreateEpistemicFusion :
  CoordinatedUseCreatesEpistemicFusion → ⊥
coordinatedUseDoesNotCreateEpistemicFusion ()

pluralObservationsDoNotCreateForcedConsensus :
  PluralObservationsCreateForcedConsensus → ⊥
pluralObservationsDoNotCreateForcedConsensus ()

disagreementDoesNotCreateInvalidEvidence : DisagreementCreatesInvalidEvidence → ⊥
disagreementDoesNotCreateInvalidEvidence ()

sharedScoreDoesNotCreateSameSituatedState : SharedScoreCreatesSameSituatedState → ⊥
sharedScoreDoesNotCreateSameSituatedState ()

record EvidenceBraidBoundary : Set where
  constructor evidence-braid-boundary
  field
    coordinatedUseRequiresFusion : Bool
    coordinatedUseRequiresFusionIsFalse : coordinatedUseRequiresFusion ≡ false
    pluralObservationRequiresConsensusScore : Bool
    pluralObservationRequiresConsensusScoreIsFalse :
      pluralObservationRequiresConsensusScore ≡ false
    tensionMayRemainVisible : Bool
    tensionMayRemainVisibleIsTrue : tensionMayRemainVisible ≡ true

open EvidenceBraidBoundary public

canonicalEvidenceBraidBoundary : EvidenceBraidBoundary
canonicalEvidenceBraidBoundary = evidence-braid-boundary
  false refl
  false refl
  true refl

holdTheTensionReading : String
holdTheTensionReading =
  "Distinct admissible observations may be coordinated without fusion. Convergence does not erase provenance; disagreement need not invalidate either observation; and operational, participant, ecological, political-economic, cultural and standards lenses can remain jointly visible until a declared consumer justifies a more specific relation."
