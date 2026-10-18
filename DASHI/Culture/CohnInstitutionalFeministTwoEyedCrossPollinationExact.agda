module DASHI.Culture.CohnInstitutionalFeministTwoEyedCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.FeministRechartingSourceBridgeExact as Feminist
import DASHI.Core.LacanIrigarayTernaryGrammarBridgeExact as LI
import DASHI.Core.TernaryRoleCarrierExact as Ternary
import DASHI.Core.RepresentationSubjectPositionNonfactorabilityExact as Subject
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as IK
import DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionExact as Acquisition1
import DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionTwoExact as Acquisition2

------------------------------------------------------------------------
-- FEMINIST / ANTI-LACANIAN / INTERSECTIONAL / TWO-EYED CROSS-POLLINATION
--
-- This owner asks which newly acquired institutional-epistemic coordinate
-- families are already structurally supported by canonical DASHI machinery,
-- and which remain genuinely new candidate debts.
--
-- Existing owners may supply mathematical grammar (collision, non-factorability,
-- strict refinement, provenance non-fusion, subject-position separation), but
-- they do not retrospectively author or exhaust the source concepts acquired
-- from Longino, Dotson, Medina, Tuana, Pohlhaus or Anderson.
------------------------------------------------------------------------

intersectionalCollision :
  INF.NonFactorabilityWitness INF.flatProjection INF.relationalOutcome
intersectionalCollision = INF.canonicalIntersectionalNonFactorability

feministPositiveRepair : Feminist.PositiveRecharting Feminist.inheritedChart
feministPositiveRepair = Feminist.canonicalPositiveRecharting

lacanIrigarayBoundary : LI.LacanIrigarayGrammarBoundary
lacanIrigarayBoundary = LI.canonicalLacanIrigarayGrammarBoundary

subjectPositionBoundary : Subject.RepresentationSubjectPositionBoundary
subjectPositionBoundary = Subject.canonicalRepresentationSubjectPositionBoundary

twoEyedBoundary : TwoEyed.KimmererTwoEyedSeeingBoundary
twoEyedBoundary = TwoEyed.canonicalKimmererTwoEyedSeeingBoundary

data ExistingRepairFamily : Set where
  erasedRelationFamily : ExistingRepairFamily
  positiveResidualFamily : ExistingRepairFamily
  subjectPositionAuthorityFamily : ExistingRepairFamily
  provenanceHistoryFamily : ExistingRepairFamily
  permissionObligationFamily : ExistingRepairFamily
  relationalGrammarFamily : ExistingRepairFamily

data AcquiredCandidateFamily : Set where
  evidentialContextFamily : AcquiredCandidateFamily
  testimonyUptakeFamily : AcquiredCandidateFamily
  pluralInterpretiveResourcesFamily : AcquiredCandidateFamily
  ignoranceProductionFamily : AcquiredCandidateFamily
  hermeneuticalRefusalFamily : AcquiredCandidateFamily
  criticalUptakeFamily : AcquiredCandidateFamily

data StructuralCoverage : Set where
  genericStructurePaid : StructuralCoverage
  partiallyRelatedButNotPaid : StructuralCoverage
  genuinelyUnpaidCandidate : StructuralCoverage

coverageOf : AcquiredCandidateFamily → StructuralCoverage
coverageOf evidentialContextFamily = partiallyRelatedButNotPaid
coverageOf testimonyUptakeFamily = partiallyRelatedButNotPaid
coverageOf pluralInterpretiveResourcesFamily = partiallyRelatedButNotPaid
coverageOf ignoranceProductionFamily = genuinelyUnpaidCandidate
coverageOf hermeneuticalRefusalFamily = genuinelyUnpaidCandidate
coverageOf criticalUptakeFamily = partiallyRelatedButNotPaid

evidentialContextExistingAnalogue : ExistingRepairFamily
evidentialContextExistingAnalogue = erasedRelationFamily

testimonyUptakeExistingAnalogue : ExistingRepairFamily
testimonyUptakeExistingAnalogue = subjectPositionAuthorityFamily

pluralResourcesExistingAnalogue : ExistingRepairFamily
pluralResourcesExistingAnalogue = provenanceHistoryFamily

criticalUptakeExistingAnalogue : ExistingRepairFamily
criticalUptakeExistingAnalogue = positiveResidualFamily

sharedCarrierDoesNotIdentifyRelationalGrammar :
  (permutation : Ternary.TernaryPermutation) → LI.GrammarPreserving permutation → ⊥
sharedCarrierDoesNotIdentifyRelationalGrammar = LI.noTernaryRelabellingPreservesGrammar

categoryVisibilityCannotRecoverOriginatingSubject :
  INF.FactorsThrough Subject.categoryVisibility Subject.subjectPosition → ⊥
categoryVisibilityCannotRecoverOriginatingSubject =
  Subject.categoryVisibilityCannotRecoverSubjectPosition

sharedObservationCannotRecoverKnowledgeProvenance :
  INF.FactorsThrough TwoEyed.observeKnowledgeHistory TwoEyed.provenance → ⊥
sharedObservationCannotRecoverKnowledgeProvenance =
  TwoEyed.sharedObservationDoesNotRecoverProvenance

extractedPropositionCannotRecoverAuthority :
  INF.FactorsThrough IK.extractedProposition IK.authority → ⊥
extractedPropositionCannotRecoverAuthority = IK.propositionCannotRecoverAuthority

extractedPropositionCannotRecoverPermission :
  INF.FactorsThrough IK.extractedProposition IK.permission → ⊥
extractedPropositionCannotRecoverPermission = IK.propositionCannotRecoverPermission

extractedPropositionCannotRecoverObligation :
  INF.FactorsThrough IK.extractedProposition IK.obligation → ⊥
extractedPropositionCannotRecoverObligation = IK.propositionCannotRecoverObligation

record CrossPollinationBoundary : Set where
  constructor crossPollinationBoundary
  field
    existingTheoryPaysErasedRelationGrammar : Bool
    existingTheoryPaysSubjectAuthoritySeparation : Bool
    existingTheoryPaysProvenanceNonFusion : Bool
    existingTheoryPaysPermissionObligationSeparation : Bool
    positiveRepairRequiresAddedResidual : Bool
    constructedIgnoranceAlreadyPaidByIntersectionality : Bool
    hermeneuticalRefusalAlreadyPaidByTwoEyedSeeing : Bool
    criticalUptakeAlreadyPaidByFeministRecharting : Bool
    acquiredSourceConceptEqualsExistingDashiFamily : Bool
    newSourcesCollapseIntoExistingTheory : Bool
    crossPollinationCreatesHistoricalInfluenceClaim : Bool
    sourceConceptCreatesDashiTheorem : Bool

open CrossPollinationBoundary public

canonicalCrossPollinationBoundary : CrossPollinationBoundary
canonicalCrossPollinationBoundary = crossPollinationBoundary
  true true true true true
  false false false false false false false

priorAcquisitionOneBoundary : Acquisition1.AcquisitionAttributionBoundary
priorAcquisitionOneBoundary = Acquisition1.canonicalAcquisitionAttributionBoundary

priorAcquisitionTwoBoundary : Acquisition2.AcquisitionTwoAttributionBoundary
priorAcquisitionTwoBoundary = Acquisition2.canonicalAcquisitionTwoAttributionBoundary

record DiagnosisCrosswalk : Set where
  constructor diagnosisCrosswalk
  field
    alreadyPaidGenericStructure : String
    stillUnpaidSourceSpecificCandidates : String
    promotionRule : String
    attributionRule : String

open DiagnosisCrosswalk public

canonicalDiagnosisCrosswalk : DiagnosisCrosswalk
canonicalDiagnosisCrosswalk = diagnosisCrosswalk
  "collision/non-factorability; recharting cannot recover erased coordinates; strict refinement by adding a residual; subject-position/authority separation; provenance non-fusion; permission/obligation separation; same carrier does not imply same relational grammar"
  "evidential context and criticism conditions; testimony uptake; plural interpretive resources; constructed ignorance; hermeneutical refusal; institutional critical uptake"
  "for an observed consumer collision, instantiate candidate residuals and retain only those that actually distinguish the fibre; no source label or theory family is automatically sufficient"
  "Irigaray, Crenshaw, Two-Eyed Seeing/Kimmerer/Bartlett, Longino, Dotson, Medina, Tuana, Pohlhaus and Anderson retain distinct source roles; structural analogy and cross-pollination do not create theory identity, historical influence, proof authorship or authority"
