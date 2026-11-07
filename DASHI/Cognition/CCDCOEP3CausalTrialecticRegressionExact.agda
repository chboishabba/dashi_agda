module DASHI.Cognition.CCDCOEP3CausalTrialecticRegressionExact where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import Base369 as Base
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.BinaryInteractionNonseparabilityExact as Interaction
import DASHI.Cognition.CCDCOEP3TypedIntersectionalAxisExact as Axis
import DASHI.Cognition.CCDCOEP3SituatedHistoryPNFExact as History
import DASHI.Core.DiscriminatorSynthesisExact as Discriminator
import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Perm
import DASHI.Foundations.TernaryPermutationS3LawsExact as S3
import DASHI.Cognition.CCDCOEP3CausalTrialecticInteractionExact as P3
import DASHI.Cognition.CCDCOEP3ClimateGenealogyCaseExact as ClimateCase
import DASHI.Cognition.CCDCOEP3API1998PrimaryPlanExact as API1998
import DASHI.Cognition.CCDCOEP3ClimateContestedAttributionExact as Contested
import DASHI.Cognition.CCDCOEP3ClimateObservedActivityAndCorpusExact as Observed
import DASHI.Cognition.CCDCOEP3SourcePowerEvidenceWeldExact as Source
import DASHI.Culture.JohnAnthonyBrownChildReligiousPowerBidiExact as Brown
import DASHI.Governance.EvidenceGradedGenealogyCore as Genealogy
import DASHI.Wikimedia.IbrahimSnowballAnthropologyClimateDenialPoliticalTheologyExact as Climate

-- The two axes have different indexed point carriers despite their
-- equal finite point counts. Their contextual response is not recovered
-- by adding, counting, or recharting those point coordinates.

typedRaceSexNotIdentical :
  Axis.raceAxis ≡ Axis.sexAxis → ⊥
typedRaceSexNotIdentical = P3.typedRaceSexAxesDistinct

typedIntersectionIsNotEndpointAdditive :
  Interaction.NonseparableAdditiveInteraction Axis.typedJointSurface
typedIntersectionIsNotEndpointAdditive =
  P3.typedInteractionHasNoEndpointAdditiveReconstruction

sameTypedPositionsDoNotFixSituatedOutcome :
  NF.FactorsThrough Axis.coordinatesOnly Axis.recognition → ⊥
sameTypedPositionsDoNotFixSituatedOutcome =
  P3.sameTypedCoordinatesDoNotDetermineSituatedRecognition

-- A positive context observation separates the originally indistinguishable
-- pair. It cannot be simulated by recharting the two axis coordinates.
contextualDiscriminatorClosesTheSelectedPair :
  Discriminator.BundleSeparates Axis.contextualObservationBundle
    Axis.sameCoordinatesAccessible Axis.sameCoordinatesExclusionary
contextualDiscriminatorClosesTheSelectedPair =
  Axis.contextualObservationSeparates

historicalCandidateCannotBeAutoPromoted :
  ∀ {About}
    (evidence : History.SituatedEventEvidence About) →
  PNF.candidateOnly (History.originalCandidate evidence) ≡ true
historicalCandidateCannotBeAutoPromoted =
  History.candidateStatusPreserved

originalS3Reverse :
  Perm.applyPermutation
    (Perm.inversePermutation Perm.permRotate)
    (Perm.applyPermutation Perm.permRotate Base.tri-low)
  ≡ Base.tri-low
originalS3Reverse =
  P3.sixReorientationsReversible Perm.permRotate Base.tri-low

originalS3OrderObstruction :
  S3._∙_ Perm.permRotate Perm.permSwapLowMid
  ≡ S3._∙_ Perm.permSwapLowMid Perm.permRotate → ⊥
originalS3OrderObstruction = P3.orderOfS3OperationsMatters

causalWorldsLookIdentical :
  P3.observedPairFor P3.directEffect
  ≡ P3.observedPairFor P3.commonCause
causalWorldsLookIdentical = P3.observedDistributionsIdentical

selectedProbeDoesSeparate :
  Discriminator.BundleSeparates
    P3.counterfactualDistinguishingProbe
    P3.directEffect P3.commonCause
selectedProbeDoesSeparate = P3.counterfactualProbeSeparates

noCausalInferenceFromObservationsAlone :
  NF.FactorsThrough P3.observedPairFor P3.interventionalProbe → ⊥
noCausalInferenceFromObservationsAlone =
  P3.observationalAssociationDoesNotIdentifyCausation

noIntentFromMeasuredEffectAlone :
  NF.FactorsThrough P3.observedEffect P3.worldPurpose → ⊥
noIntentFromMeasuredEffectAlone =
  P3.effectCannotIdentifyHostilePurpose

coherenceDoesNotFixEpistemicRevision :
  NF.FactorsThrough P3.publicCoherence P3.evidenceRevision → ⊥
coherenceDoesNotFixEpistemicRevision =
  P3.narrativeCoherenceDoesNotDetermineRevisability

revisionMeasurementSeparatesCoherenceCollision :
  Discriminator.BundleSeparates
    P3.revisabilityDistinguishingProbe
    P3.coherentAndContestable P3.coherentButSelfSealed
revisionMeasurementSeparatesCoherenceCollision =
  P3.revisionProbeSeparates

denialSurfaceCannotIdentifyMeaning :
  NF.FactorsThrough Climate.projectDenialSurface
    Climate.denialSocialReading → ⊥
denialSurfaceCannotIdentifyMeaning =
  Source.climateDenialLabelCannotIdentifySocialCause

brownInstitutionalPowerIsOriginalAxis :
  Brown.BrownPaperClaim.axis Brown.institutionalHegemonyClaim
  ≡ Brown.institutionalPower
brownInstitutionalPowerIsOriginalAxis =
  Source.brownPaperContainsInstitutionalHegemonyAxis

-- The actual tobacco-to-climate historical continuity is grade B,
-- rather than a certificate of central command or a belief-change effect.
climateCaseHistoricallyStrong :
  Genealogy.StrongEvidenceEdge ClimateCase.originalClimateContinuity
climateCaseHistoricallyStrong =
  ClimateCase.historicalContinuityHasStrongReceipt

climateCaseCannotInferCentralCommand :
  NF.FactorsThrough ClimateCase.publicHistoricalGrade
    ClimateCase.commandHypothesis → ⊥
climateCaseCannotInferCentralCommand =
  ClimateCase.gradeBDoesNotIdentifyCentralCommand

climateCaseHypotheticalCommandDiscriminator :
  Discriminator.BundleSeparates
    ClimateCase.candidateCommandProbe
    ClimateCase.decentralisedCandidate ClimateCase.centralisedCandidate
climateCaseHypotheticalCommandDiscriminator =
  ClimateCase.centralisationHypothesesCanBeSeparatedIfEvidenceExists

-- A contemporaneous Congressional Record primary plan is evidence of
-- drafting and intended tactics, NOT documentary proof of their execution.
primaryDraftDoesNotEstablishImplementation :
  NF.FactorsThrough API1998.publicDraftObservation API1998.implementation → ⊥
primaryDraftDoesNotEstablishImplementation =
  API1998.draftDocumentDoesNotIdentifyImplementation

primaryDraftAndActualImplementationWouldSeparate :
  Discriminator.BundleSeparates API1998.implementationEvidenceProbe
    API1998.unimplementedWorld API1998.implementedWorld
primaryDraftAndActualImplementationWouldSeparate =
  API1998.implementationEvidenceSeparates

-- Source-type and organisation-authority are NOT interchangeable claims.
-- The 1998 API response and the historical Congressional draft remain
-- distinct source objects; the existence of the draft does not settle
-- the attributed dispute over corporate adoption.
climateSourceTypeMustRemainDistinguishable :
  NF.FactorsThrough Contested.flattenSource Contested.sourceDisposition → ⊥
climateSourceTypeMustRemainDistinguishable =
  Contested.sourceKindNotIdentifiedByTopic

apiInstitutionalAuthorisationStillUnderidentified :
  NF.FactorsThrough Contested.publishedDraft
    Contested.authorityHypothesis → ⊥
apiInstitutionalAuthorisationStillUnderidentified =
  Contested.publishedDraftCannotProveInstitutionalAuthorisation

originalApprovalRecordsWouldSeparateAlternatives :
  Discriminator.BundleSeparates Contested.authorisationRecordProbe
    Contested.unapprovedWorld Contested.approvedWorld
originalApprovalRecordsWouldSeparateAlternatives =
  Contested.authorisationRecordWouldSeparate

-- Independent public communication materials exist while the April 1998
-- API document retains the type of a draft. The original publication
-- does not support a causal or same-plan command/effect promotion.
realPublicationIsNotThe1998Draft :
  NF.FactorsThrough Observed.unqualifiedLabel Observed.sourceStage → ⊥
realPublicationIsNotThe1998Draft =
  Observed.stageDoesNotFactorThroughGenericLabel

realArchiveStageDiscriminator :
  Discriminator.BundleSeparates Observed.evidenceStageBundle
    Observed.apiDraft1998 Observed.ice1991
realArchiveStageDiscriminator =
  Observed.stageSeparatesDraftFromPublicCommunication

publishedCommunicationCorpusHas187Documents :
  Observed.PublishedCorpusMeasurement.totalDocuments
    Observed.originalPublishedCorpusMeasurement ≡ 187
publishedCommunicationCorpusHas187Documents =
  Observed.publishedCorpusSize

publishedMessageDiscrepancyDoesNotMeasurePersuasion :
  Observed.PublishedCorpusMeasurement.isHumanTreatmentEffect
    Observed.originalPublishedCorpusMeasurement ≡ false
publishedMessageDiscrepancyDoesNotMeasurePersuasion =
  Observed.documentContentIsNotPublicBeliefEffect
