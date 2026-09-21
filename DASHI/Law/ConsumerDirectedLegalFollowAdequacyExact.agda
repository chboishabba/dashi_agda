module DASHI.Law.ConsumerDirectedLegalFollowAdequacyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query

------------------------------------------------------------------------
-- Consumer-directed LegalFollow adequacy.
--
-- Runtime coverage receipts may route missing coordinates, but they are not
-- themselves a proof of FactorsThrough.  The exact semantic obligation remains
-- query-indexed factorisation.  A missing treatment coordinate can be witnessed
-- by an exact fibre collision; adding that coordinate repairs the projection.
------------------------------------------------------------------------

data DemoWorld : Set where
  treatmentMissing : DemoWorld
  treatmentPaid : DemoWorld

data CoarseProjection : Set where
  sameLegalSurface : CoarseProjection

data RefinedProjection : Set where
  missingTreatmentSurface : RefinedProjection
  paidTreatmentSurface : RefinedProjection

data DemoQuery : Set where
  treatmentSensitiveQuery : DemoQuery

data DemoAnswer : Set where
  unresolvedAnswer : DemoAnswer
  resolvedAnswer : DemoAnswer

coarseProject : DemoWorld → CoarseProjection
coarseProject treatmentMissing = sameLegalSurface
coarseProject treatmentPaid = sameLegalSurface

refinedProject : DemoWorld → RefinedProjection
refinedProject treatmentMissing = missingTreatmentSurface
refinedProject treatmentPaid = paidTreatmentSurface

answer : DemoQuery → DemoWorld → DemoAnswer
answer treatmentSensitiveQuery treatmentMissing = unresolvedAnswer
answer treatmentSensitiveQuery treatmentPaid = resolvedAnswer

semantics : Query.QuerySemantics DemoWorld DemoQuery DemoAnswer
semantics = Query.querySemantics answer

coarseTreatmentDefect :
  Query.QueryAdequacyDefect
    coarseProject semantics treatmentSensitiveQuery
coarseTreatmentDefect =
  Query.queryAdequacyDefect
    treatmentMissing
    treatmentPaid
    refl
    (λ ())

coarseProjectionCannotAnswerTreatmentQuery :
  Query.AdequateFor
    coarseProject semantics treatmentSensitiveQuery → ⊥
coarseProjectionCannotAnswerTreatmentQuery =
  Query.queryAdequacyDefectBlocksFactorisation coarseTreatmentDefect

decodeRefined : RefinedProjection → DemoAnswer
decodeRefined missingTreatmentSurface = unresolvedAnswer
decodeRefined paidTreatmentSurface = resolvedAnswer

refinedProjectionRepairsTreatmentQuery :
  Query.AdequateFor
    refinedProject semantics treatmentSensitiveQuery
refinedProjectionRepairsTreatmentQuery =
  Query.factorsForQuery
    decodeRefined
    proof
  where
    proof : (state : DemoWorld) →
      answer treatmentSensitiveQuery state
      ≡
      decodeRefined (refinedProject state)
    proof treatmentMissing = refl
    proof treatmentPaid = refl

record ConsumerDirectedLegalFollowAdequacyBoundary : Set where
  constructor consumerDirectedLegalFollowAdequacyBoundary
  field
    runtimeCoverageReceiptIsFormalFactorsThroughProof : Bool
    runtimeCoverageReceiptIsFormalFactorsThroughProofIsFalse :
      runtimeCoverageReceiptIsFormalFactorsThroughProof ≡ false

    missingRequiredAxisMayBeTreatedAsAdequate : Bool
    missingRequiredAxisMayBeTreatedAsAdequateIsFalse :
      missingRequiredAxisMayBeTreatedAsAdequate ≡ false

    nonFactorabilityMayRouteTypedResearchDemand : Bool
    nonFactorabilityMayRouteTypedResearchDemandIsTrue :
      nonFactorabilityMayRouteTypedResearchDemand ≡ true

    addingMissingAxisMayRepairAdequacy : Bool
    addingMissingAxisMayRepairAdequacyIsTrue :
      addingMissingAxisMayRepairAdequacy ≡ true

    explicitlyClosedMissingAxisMayTerminateUnresolved : Bool
    explicitlyClosedMissingAxisMayTerminateUnresolvedIsTrue :
      explicitlyClosedMissingAxisMayTerminateUnresolved ≡ true

    unresolvedTerminationCreatesClaimTruth : Bool
    unresolvedTerminationCreatesClaimTruthIsFalse :
      unresolvedTerminationCreatesClaimTruth ≡ false

    consumerAdequacyCreatesLegalAuthority : Bool
    consumerAdequacyCreatesLegalAuthorityIsFalse :
      consumerAdequacyCreatesLegalAuthority ≡ false

open ConsumerDirectedLegalFollowAdequacyBoundary public

canonicalConsumerDirectedLegalFollowAdequacyBoundary :
  ConsumerDirectedLegalFollowAdequacyBoundary
canonicalConsumerDirectedLegalFollowAdequacyBoundary =
  consumerDirectedLegalFollowAdequacyBoundary
    false refl
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl

data RuntimeCoverageAutomaticallyFactorsThrough : Set where
data MissingAxisAutomaticallyAdequate : Set where
data ExplicitlyUnresolvedAutomaticallyClaimTruth : Set where

runtimeCoverageDoesNotAutomaticallyFactor :
  RuntimeCoverageAutomaticallyFactorsThrough → ⊥
runtimeCoverageDoesNotAutomaticallyFactor ()

missingAxisDoesNotAutomaticallyBecomeAdequate :
  MissingAxisAutomaticallyAdequate → ⊥
missingAxisDoesNotAutomaticallyBecomeAdequate ()

explicitlyUnresolvedDoesNotCreateClaimTruth :
  ExplicitlyUnresolvedAutomaticallyClaimTruth → ⊥
explicitlyUnresolvedDoesNotCreateClaimTruth ()
