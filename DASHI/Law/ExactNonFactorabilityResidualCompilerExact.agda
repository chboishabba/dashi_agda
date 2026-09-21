module DASHI.Law.ExactNonFactorabilityResidualCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query

------------------------------------------------------------------------
-- Exact non-factorability witness -> exact consumer research residual.
------------------------------------------------------------------------

data ConsumerAxis : Set where
  semanticIdentity sourceRevision sourceSpan provenance treatment temporal
  jurisdiction factualPredicate burdenOrException : ConsumerAxis

data ResearchKind : Set where
  acquireSource reviewTreatment resolveTemporal resolveJurisdiction reviewFact
  reviewBurdenOrException recoverProvenance resolveSemanticIdentity :
    ResearchKind

researchKind : ConsumerAxis → ResearchKind
researchKind semanticIdentity = resolveSemanticIdentity
researchKind sourceRevision = acquireSource
researchKind sourceSpan = acquireSource
researchKind provenance = recoverProvenance
researchKind treatment = reviewTreatment
researchKind temporal = resolveTemporal
researchKind jurisdiction = resolveJurisdiction
researchKind factualPredicate = reviewFact
researchKind burdenOrException = reviewBurdenOrException

record ExactConsumerResidual
    {State Observation QueryType Answer : Set}
    (project : State → Observation)
    (semantics : Query.QuerySemantics State QueryType Answer)
    (query : QueryType) : Set₁ where
  constructor exactConsumerResidual
  field
    lostAxis : ConsumerAxis
    targetRef : String
    theoremModuleRef : String
    theoremRef : String
    defect : Query.QueryAdequacyDefect project semantics query
    demandKind : ResearchKind
    demandKindIsExact : demandKind ≡ researchKind lostAxis
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse :
      createsSemanticAuthority ≡ false
    createsClaimTruth : Bool
    createsClaimTruthIsFalse :
      createsClaimTruth ≡ false

open ExactConsumerResidual public

residualRetainsNonFactorability :
  ∀ {State Observation QueryType Answer}
    {project : State → Observation}
    {semantics : Query.QuerySemantics State QueryType Answer}
    {query : QueryType} →
  ExactConsumerResidual project semantics query →
  Query.QueryAdequacyDefect project semantics query
residualRetainsNonFactorability = defect

treatmentDefectCompilesToTreatmentDemand :
  ExactConsumerResidual
    Consumer.ConsumerDirectedLegalFollowAdequacyExact.coarseProject
    Consumer.ConsumerDirectedLegalFollowAdequacyExact.semantics
    Consumer.ConsumerDirectedLegalFollowAdequacyExact.treatmentSensitiveQuery
treatmentDefectCompilesToTreatmentDemand =
  exactConsumerResidual
    treatment
    "case:target"
    "DASHI.Law.ConsumerDirectedLegalFollowAdequacyExact"
    "coarseTreatmentDefect"
    Consumer.ConsumerDirectedLegalFollowAdequacyExact.coarseTreatmentDefect
    reviewTreatment
    refl
    true refl
    false refl
    false refl
  where
    import DASHI.Law.ConsumerDirectedLegalFollowAdequacyExact as Consumer

treatmentResidualDemandIsExact :
  demandKind treatmentDefectCompilesToTreatmentDemand ≡ reviewTreatment
treatmentResidualDemandIsExact = refl

data ApproximateCollisionAutomaticallyExactResidual : Set where
data ResidualAutomaticallyClaimTruth : Set where

approximateCollisionCannotAutomaticallyCreateExactResidual :
  ApproximateCollisionAutomaticallyExactResidual → ⊥
approximateCollisionCannotAutomaticallyCreateExactResidual ()

residualDoesNotCreateClaimTruth :
  ResidualAutomaticallyClaimTruth → ⊥
residualDoesNotCreateClaimTruth ()

record ExactNonFactorabilityResidualCompilerBoundary : Set where
  constructor exactNonFactorabilityResidualCompilerBoundary
  field
    exactResidualRetainsQueryDefect : Bool
    exactResidualRetainsQueryDefectIsTrue :
      exactResidualRetainsQueryDefect ≡ true

    lostAxisDeterministicallyChoosesResearchKind : Bool
    lostAxisDeterministicallyChoosesResearchKindIsTrue :
      lostAxisDeterministicallyChoosesResearchKind ≡ true

    approximateCollisionMayPromoteExactResidual : Bool
    approximateCollisionMayPromoteExactResidualIsFalse :
      approximateCollisionMayPromoteExactResidual ≡ false

    residualCreatesSemanticAuthority : Bool
    residualCreatesSemanticAuthorityIsFalse :
      residualCreatesSemanticAuthority ≡ false

    residualCreatesClaimTruth : Bool
    residualCreatesClaimTruthIsFalse :
      residualCreatesClaimTruth ≡ false

open ExactNonFactorabilityResidualCompilerBoundary public

canonicalExactNonFactorabilityResidualCompilerBoundary :
  ExactNonFactorabilityResidualCompilerBoundary
canonicalExactNonFactorabilityResidualCompilerBoundary =
  exactNonFactorabilityResidualCompilerBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
