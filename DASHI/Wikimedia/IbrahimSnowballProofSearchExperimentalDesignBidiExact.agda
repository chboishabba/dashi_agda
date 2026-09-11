module DASHI.Wikimedia.IbrahimSnowballProofSearchExperimentalDesignBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey
import DASHI.Wikimedia.IbrahimSnowballLearningMemoryTraumaReplicationConsensusBidiExact as MemoryReplication
import DASHI.Interop.SourceDiligenceProofSearchBridgeExact as SourceSearch
import DASHI.Interop.DialecticalMaterialProofSearchExperimentLoopExact as ExperimentLoop
import DASHI.Interop.IntrospectiveProofLoopExact as Introspective
import DASHI.Reasoning.EvidenceDesignAdmissibilityExact as Design
import DASHI.Culture.JohnAnthonyBrownStudyDesignBidiExact as BrownDesign

------------------------------------------------------------------------
-- IBRAHIM / PROOF SEARCH / EXPERIMENTAL DESIGN BIDI
--
-- A live consumer defect may reopen source search, motivate a discriminating
-- experiment, or close only after a separately paid refinement.  Experimental
-- design is obligation-relative: an experiment is useful here only when it
-- separates the concrete states witnessing the live non-factorability defect.
-- An interesting measurement, significant result, visualisation, source hit or
-- replication count is not itself consumer closure.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim proof-search/experimental-design BIDI"
  "verified external concept identity"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not create design adequacy, discrimination, causal identification, source admission or consumer closure")

researchDesignQid : Identity.ExternalIdentityDemand
researchDesignQid = mkQid "research design" "Q1438035"

designOfExperimentsQid : Identity.ExternalIdentityDemand
designOfExperimentsQid = mkQid "design of experiments / experimental design" "Q2334061"

experimentQid : Identity.ExternalIdentityDemand
experimentQid = mkQid "scientific experiment" "Q101965"

hypothesisQid : Identity.ExternalIdentityDemand
hypothesisQid = mkQid "hypothesis" "Q41719"

scientificHypothesisQid : Identity.ExternalIdentityDemand
scientificHypothesisQid = mkQid "scientific hypothesis" "Q3144351"

randomizedControlledTrialQid : Identity.ExternalIdentityDemand
randomizedControlledTrialQid = mkQid "randomized controlled trial" "Q1436668"

proofSearchQid : Identity.ExternalIdentityDemand
proofSearchQid = Identity.mkOptionalIdentityDemand
  "Ibrahim proof-search/experimental-design BIDI"
  "external concept identity"
  "proof search as repository proof/refinement process"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact cross-domain QID promoted; repository proof-search/refinement machinery remains authoritative for the formal process")

------------------------------------------------------------------------
-- Dewey stays navigation-only.  No exact inspected DDC statements were
-- promoted for this group in this pass.
------------------------------------------------------------------------

researchDesignDewey : Dewey.DeweyCoordinate
researchDesignDewey = Dewey.mkUnresolvedDewey
  "research design"
  "no exact inspected DDC value promoted in this pass"

experimentalDesignDewey : Dewey.DeweyCoordinate
experimentalDesignDewey = Dewey.mkUnresolvedDewey
  "design of experiments"
  "no exact inspected DDC value promoted in this pass"

experimentDewey : Dewey.DeweyCoordinate
experimentDewey = Dewey.mkUnresolvedDewey
  "scientific experiment"
  "no exact inspected DDC value promoted in this pass"

------------------------------------------------------------------------
-- Existing repository engines are the semantics.  This file only composes
-- their boundaries into the Ibrahim graph.
------------------------------------------------------------------------

sourceSearchBoundary : SourceSearch.SourceDiligenceProofSearchBoundary
sourceSearchBoundary = SourceSearch.canonicalSourceDiligenceProofSearchBoundary

experimentLoopBoundary : ExperimentLoop.DialecticalMaterialProofSearchExperimentBoundary
experimentLoopBoundary = ExperimentLoop.canonicalDialecticalMaterialProofSearchExperimentBoundary

introspectiveBoundary : Introspective.IntrospectiveProofLoopBoundary
introspectiveBoundary = Introspective.canonicalIntrospectiveProofLoopBoundary

evidenceDesignBoundary : Design.EvidenceDesignBoundary
evidenceDesignBoundary = Design.canonicalEvidenceDesignBoundary

brownDesignBoundary : BrownDesign.JohnAnthonyBrownStudyDesignBoundary
brownDesignBoundary = BrownDesign.canonicalJohnAnthonyBrownStudyDesignBoundary

memoryReplicationBoundary : MemoryReplication.LearningMemoryTraumaReplicationConsensusBoundary
memoryReplicationBoundary = MemoryReplication.canonicalLearningMemoryTraumaReplicationConsensusBoundary

------------------------------------------------------------------------
-- Regression 1: residual existence cannot determine the appropriate next route.
------------------------------------------------------------------------

data ResidualCase : Set where
  sameResidualNeedsSource sameResidualNeedsExperiment : ResidualCase

data ResidualSurface : Set where sameObservedConsumerDefect : ResidualSurface
data InquiryRoute : Set where sourceDiligenceRoute discriminatingExperimentRoute : InquiryRoute

residualSurface : ResidualCase → ResidualSurface
residualSurface _ = sameObservedConsumerDefect

inquiryRoute : ResidualCase → InquiryRoute
inquiryRoute sameResidualNeedsSource = sourceDiligenceRoute
inquiryRoute sameResidualNeedsExperiment = discriminatingExperimentRoute

residualRouteDefect : INF.NonFactorabilityWitness residualSurface inquiryRoute
residualRouteDefect = INF.nonFactorabilityWitness
  sameResidualNeedsSource sameResidualNeedsExperiment refl (λ ())

consumerDefectCannotFactorNextInquiryRoute :
  INF.FactorsThrough residualSurface inquiryRoute → ⊥
consumerDefectCannotFactorNextInquiryRoute =
  INF.witnessRulesOutEveryFlatFactorisation residualRouteDefect

------------------------------------------------------------------------
-- Regression 2: more measurements cannot recover discriminatory adequacy.
------------------------------------------------------------------------

data MeasurementCase : Set where
  sameMeasurementCountSeparatesWitness sameMeasurementCountDoesNotSeparateWitness : MeasurementCase

data MeasurementCountSurface : Set where sameMeasurementMultiplicity : MeasurementCountSurface
data DiscriminationStatus : Set where defectWitnessSeparated defectWitnessNotSeparated : DiscriminationStatus

measurementCountSurface : MeasurementCase → MeasurementCountSurface
measurementCountSurface _ = sameMeasurementMultiplicity

discriminationStatus : MeasurementCase → DiscriminationStatus
discriminationStatus sameMeasurementCountSeparatesWitness = defectWitnessSeparated
discriminationStatus sameMeasurementCountDoesNotSeparateWitness = defectWitnessNotSeparated

measurementDiscriminationDefect : INF.NonFactorabilityWitness measurementCountSurface discriminationStatus
measurementDiscriminationDefect = INF.nonFactorabilityWitness
  sameMeasurementCountSeparatesWitness sameMeasurementCountDoesNotSeparateWitness refl (λ ())

measurementMultiplicityCannotFactorDiscrimination :
  INF.FactorsThrough measurementCountSurface discriminationStatus → ⊥
measurementMultiplicityCannotFactorDiscrimination =
  INF.witnessRulesOutEveryFlatFactorisation measurementDiscriminationDefect

------------------------------------------------------------------------
-- Regression 3: successful pairwise discrimination cannot recover consumer
-- closure.  The result still has to compile into a refined observer/receipt.
------------------------------------------------------------------------

data ExperimentResultCase : Set where
  sameSeparatedPairConsumerOpen sameSeparatedPairConsumerClosedAfterRefinement : ExperimentResultCase

data SeparationSurface : Set where samePairwiseSeparation : SeparationSurface
data ConsumerClosureStatus : Set where consumerStillOpen consumerClosedWithRefinement : ConsumerClosureStatus

separationSurface : ExperimentResultCase → SeparationSurface
separationSurface _ = samePairwiseSeparation

consumerClosureStatus : ExperimentResultCase → ConsumerClosureStatus
consumerClosureStatus sameSeparatedPairConsumerOpen = consumerStillOpen
consumerClosureStatus sameSeparatedPairConsumerClosedAfterRefinement = consumerClosedWithRefinement

separationClosureDefect : INF.NonFactorabilityWitness separationSurface consumerClosureStatus
separationClosureDefect = INF.nonFactorabilityWitness
  sameSeparatedPairConsumerOpen sameSeparatedPairConsumerClosedAfterRefinement refl (λ ())

pairwiseDiscriminationCannotFactorConsumerClosure :
  INF.FactorsThrough separationSurface consumerClosureStatus → ⊥
pairwiseDiscriminationCannotFactorConsumerClosure =
  INF.witnessRulesOutEveryFlatFactorisation separationClosureDefect

------------------------------------------------------------------------
-- Regression 4: design label cannot recover what question it answers well.
------------------------------------------------------------------------

data DesignCase : Set where
  sameDesignLabelCausalFit sameDesignLabelExperienceFit : DesignCase

data DesignSurface : Set where sameStudyDesignLabel : DesignSurface
data EvidenceConsumer : Set where causalEffectConsumer livedExperienceConsumer : EvidenceConsumer

designSurface : DesignCase → DesignSurface
designSurface _ = sameStudyDesignLabel

evidenceConsumer : DesignCase → EvidenceConsumer
evidenceConsumer sameDesignLabelCausalFit = causalEffectConsumer
evidenceConsumer sameDesignLabelExperienceFit = livedExperienceConsumer

designConsumerDefect : INF.NonFactorabilityWitness designSurface evidenceConsumer
designConsumerDefect = INF.nonFactorabilityWitness
  sameDesignLabelCausalFit sameDesignLabelExperienceFit refl (λ ())

designLabelCannotFactorEvidenceConsumer :
  INF.FactorsThrough designSurface evidenceConsumer → ⊥
designLabelCannotFactorEvidenceConsumer =
  INF.witnessRulesOutEveryFlatFactorisation designConsumerDefect

------------------------------------------------------------------------
-- Explicit experimental-design coordinates inherited from the Brown study
-- design lane.  These are candidate audit axes, not a universal closed list.
------------------------------------------------------------------------

record ExperimentalDesignAuditCoordinates : Set where
  constructor experimental-design-audit-coordinates
  field
    samplingFrame : Bool
    comparator : Bool
    exposureOrInterventionTiming : Bool
    repeatedMeasurement : Bool
    measurementValidity : Bool
    attritionHandling : Bool
    confoundingControl : Bool
    multiplicityHandling : Bool
    effectSizeSurface : Bool
    uncertaintySurface : Bool
    externalValidityDomain : Bool
    participantRole : Bool
    implementationFidelity : Bool
    independenceAndCommonSourceAudit : Bool
open ExperimentalDesignAuditCoordinates public

canonicalExperimentalDesignAuditCoordinates : ExperimentalDesignAuditCoordinates
canonicalExperimentalDesignAuditCoordinates =
  experimental-design-audit-coordinates
    true true true true true true true true true true true true true true

------------------------------------------------------------------------
-- Reverse BIDI constraints into Ibrahim parent nodes.
------------------------------------------------------------------------

record ProofSearchDesignReverseConstraint : Set where
  constructor proof-search-design-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open ProofSearchDesignReverseConstraint public

knowledgeConstraint : ProofSearchDesignReverseConstraint
knowledgeConstraint = proof-search-design-reverse-constraint
  "Knowledge / verification"
  "live claim, missing coordinate, source-search result, admitted source, evidence result and consumer closure remain distinct"
  false

scienceConstraint : ProofSearchDesignReverseConstraint
scienceConstraint = proof-search-design-reverse-constraint
  "Science / experiment"
  "hypothesis, design, manipulation/observation, measurement, discrimination, inference, causal identification and transport remain distinct"
  false

memoryTraumaConstraint : ProofSearchDesignReverseConstraint
memoryTraumaConstraint = proof-search-design-reverse-constraint
  "Learning / memory / trauma"
  "reported surface, latent state, context/update history, discriminating observation, diagnosis and intervention authority remain distinct"
  false

replicationConstraint : ProofSearchDesignReverseConstraint
replicationConstraint = proof-search-design-reverse-constraint
  "Replication / consensus"
  "repeat count, provenance independence, design equivalence, result concordance, uncertainty and consensus remain distinct"
  false

lawConstraint : ProofSearchDesignReverseConstraint
lawConstraint = proof-search-design-reverse-constraint
  "SensibLaw / evidence"
  "source discovery, admissibility, factual finding, causal element and legal conclusion remain separate consumers"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data ResidualChoosesExperiment : Set where
data MoreMeasurementsMeanBetterExperiment : Set where
data SignificantResultMeansConsumerClosed : Set where
data VisualAuditMeansEvidence : Set where
data SourceHitMeansClaimSupported : Set where
data LongitudinalDesignMeansCausation : Set where
data RCTMeansUniversalTransport : Set where
data NullResultMeansLogicalNegation : Set where
data QidMeansDesignAdequacy : Set where

residualDoesNotChooseExperiment : ResidualChoosesExperiment → ⊥
residualDoesNotChooseExperiment ()

moreMeasurementsDoNotMeanBetterExperiment : MoreMeasurementsMeanBetterExperiment → ⊥
moreMeasurementsDoNotMeanBetterExperiment ()

significantResultDoesNotCloseConsumer : SignificantResultMeansConsumerClosed → ⊥
significantResultDoesNotCloseConsumer ()

visualAuditDoesNotCreateEvidence : VisualAuditMeansEvidence → ⊥
visualAuditDoesNotCreateEvidence ()

sourceHitDoesNotMeanClaimSupported : SourceHitMeansClaimSupported → ⊥
sourceHitDoesNotMeanClaimSupported ()

longitudinalDoesNotMeanCausation : LongitudinalDesignMeansCausation → ⊥
longitudinalDoesNotMeanCausation ()

rctDoesNotMeanUniversalTransport : RCTMeansUniversalTransport → ⊥
rctDoesNotMeanUniversalTransport ()

nullResultDoesNotMeanLogicalNegation : NullResultMeansLogicalNegation → ⊥
nullResultDoesNotMeanLogicalNegation ()

qidDoesNotMeanDesignAdequacy : QidMeansDesignAdequacy → ⊥
qidDoesNotMeanDesignAdequacy ()

record ProofSearchExperimentalDesignBoundary : Set where
  constructor proof-search-experimental-design-boundary
  field
    qidsAttachedWhenSafelyResolved : Bool
    unresolvedDeweyRetainedExplicitly : Bool
    existingProofSearchArchitectureReused : Bool
    designAdmissibilityIsObligationRelative : Bool
    experimentMustSeparateLiveDefectWitness : Bool
    sourceSearchAndExperimentRemainDistinctRoutes : Bool
    pairwiseDiscriminationDoesNotAutoCloseConsumer : Bool
    visualAuditIsDiagnosticOnly : Bool
    nullEvidenceIsNotLogicalNegation : Bool
    longitudinalObservationDoesNotAutoCreateCausation : Bool
    replicationIndependenceRemainsSeparate : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open ProofSearchExperimentalDesignBoundary public

canonicalProofSearchExperimentalDesignBoundary : ProofSearchExperimentalDesignBoundary
canonicalProofSearchExperimentalDesignBoundary =
  proof-search-experimental-design-boundary
    true true true true true true true true true true true true false
