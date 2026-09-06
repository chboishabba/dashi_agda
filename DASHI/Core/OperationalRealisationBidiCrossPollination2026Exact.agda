module DASHI.Core.OperationalRealisationBidiCrossPollination2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.RuntimeEventExecutionBridgeExact as Runtime
import DASHI.Core.DeclaredRealizedIntegrityResidualExact as DeclaredRealized
import DASHI.Cognition.PNF.SensibLawBillyEffectiveRemedyTwoEyedSeeingExact as Billy

------------------------------------------------------------------------
-- OPERATIONAL REALISATION -- BIDI CROSS-POLLINATION
--
-- Source attribution / authority:
--   Human Rights Committee, Billy and others v Australia,
--   CCPR/C/135/D/3624/2019, Views adopted 21 July 2022.
--   Runtime donor: DASHI.Core.RuntimeEventExecutionBridgeExact,
--   merged executable vertical PR #708.
--
-- DASHI extension: declaration/order, authorised implementation, execution,
-- observed world-state and consumer-defined success are distinct coordinates.
-- This does not turn the Committee's Views into a domestic execution writ.
------------------------------------------------------------------------

data OperationalStage : Set where
  declaredStage authorisedStage emittedStage executedStage observedStage consumerAcceptedStage : OperationalStage

record OperationalTransition : Set where
  constructor operational-transition
  field
    transitionReference : String
    declaredReference : String
    authorityReference : String
    executionReference : String
    observationReference : String
    consumerOutcomeReference : String

open OperationalTransition public

record RealisationReceipt : Set where
  constructor realisation-receipt
  field
    transition : OperationalTransition
    stage : OperationalStage
    stageReceiptReference : String

open RealisationReceipt public

record ConsumerDefinedOutcome : Set where
  constructor consumer-defined-outcome
  field
    outcomeReference : String
    affectedConsumerReference : String
    successPredicateReference : String
    satisfied : Bool

open ConsumerDefinedOutcome public

------------------------------------------------------------------------
-- Runtime and remedy share a stage-separation shape without carrier identity.
------------------------------------------------------------------------

record RuntimeOperationalAdapter : Set where
  constructor runtime-operational-adapter
  field
    donorBoundary : Runtime.RuntimeEventExecutionBoundary
    adapterReference : String

record RemedyOperationalAdapter : Set where
  constructor remedy-operational-adapter
  field
    sourceReference : String
    remedyImplementationReference : String
    noExecutionWritPromotion : Bool
    noExecutionWritPromotionIsTrue : noExecutionWritPromotion ≡ true

open RuntimeOperationalAdapter public
open RemedyOperationalAdapter public

------------------------------------------------------------------------
-- No-promotion boundaries.
------------------------------------------------------------------------

data DeclarationEqualsRealisation : Set where
data EmissionEqualsExecution : Set where
data ExecutionEqualsDesiredOutcome : Set where
data ConsultationEqualsFullReparation : Set where
data GovernmentCommitmentEqualsConsumerSuccess : Set where

declarationDoesNotEqualRealisation : DeclarationEqualsRealisation → ⊥
declarationDoesNotEqualRealisation ()

emissionDoesNotEqualExecution : EmissionEqualsExecution → ⊥
emissionDoesNotEqualExecution ()

executionDoesNotEqualDesiredOutcome : ExecutionEqualsDesiredOutcome → ⊥
executionDoesNotEqualDesiredOutcome ()

consultationDoesNotEqualFullReparation : ConsultationEqualsFullReparation → ⊥
consultationDoesNotEqualFullReparation ()

governmentCommitmentDoesNotEqualConsumerSuccess : GovernmentCommitmentEqualsConsumerSuccess → ⊥
governmentCommitmentDoesNotEqualConsumerSuccess ()

record OperationalRealisationBoundary : Set where
  constructor operational-realisation-boundary
  field
    declarationExecutionObservationSeparated : Bool
    consumerOutcomeIndependentCoordinate : Bool
    partialExecutionMayRetainResidual : Bool
    realisedEffectDoesNotBackProveIntent : Bool

canonicalOperationalRealisationBoundary : OperationalRealisationBoundary
canonicalOperationalRealisationBoundary =
  operational-realisation-boundary true true true true
