module DASHI.Wikimedia.IbrahimSnowballTiwi88SiteEvidenceIndependenceConsumerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Wikimedia.IbrahimSnowballTiwi88SitePairwiseJoinDeweyDoiQidExact as Tiwi88
import DASHI.Wikimedia.IbrahimSnowballEvidenceSynthesisPeerReviewConflictIndependenceBidiExact as Synthesis
import DASHI.Wikimedia.IbrahimSnowballLearningMemoryTraumaReplicationConsensusBidiExact as Replication

------------------------------------------------------------------------
-- CONCRETE CONSUMER: TIWI 2015 MELVILLE 88-SITE MULTI-PAPER EVIDENCE GENEALOGY
--
-- Davies 2017, Davies 2020 and Penton 2021 are valuable distinct analyses but
-- the paid repository facts say that they share the 2015 Melville 88-site
-- survey carrier family.  Therefore publication multiplicity is not independent
-- replication multiplicity.  This owner instantiates the shared provenance
-- grammar on a concrete scientific consumer instead of extending the parent
-- ontology again.
------------------------------------------------------------------------

pairwiseReceipt : Tiwi88.Pairwise88SiteJoinReceipt
pairwiseReceipt = Tiwi88.canonicalPairwise88SiteJoinReceipt

synthesisBoundary : Synthesis.EvidenceSynthesisPeerReviewIndependenceBoundary
synthesisBoundary = Synthesis.canonicalEvidenceSynthesisPeerReviewIndependenceBoundary

replicationBoundary : Replication.LearningMemoryTraumaReplicationConsensusBoundary
replicationBoundary = Replication.canonicalLearningMemoryTraumaReplicationConsensusBoundary

------------------------------------------------------------------------
-- The three DOI/source identities remain independently attributable.
------------------------------------------------------------------------

davies2017Source : Tiwi88.PairwisePrimarySource
davies2017Source = Tiwi88.davies2017

davies2020Source : Tiwi88.PairwisePrimarySource
davies2020Source = Tiwi88.davies2020

penton2021Source : Tiwi88.PairwisePrimarySource
penton2021Source = Tiwi88.penton2021

------------------------------------------------------------------------
-- Publication count cannot recover independence class.
------------------------------------------------------------------------

data ThreePaperCase : Set where
  threeIndependentStudyCarriers
  threePapersShared88SiteCarrier : ThreePaperCase

data PublicationCountSurface : Set where threePublishedAnalyses : PublicationCountSurface
data EvidenceGenealogy : Set where independentStudyGenealogy sharedCarrierGenealogy : EvidenceGenealogy

publicationCountSurface : ThreePaperCase → PublicationCountSurface
publicationCountSurface _ = threePublishedAnalyses

evidenceGenealogy : ThreePaperCase → EvidenceGenealogy
evidenceGenealogy threeIndependentStudyCarriers = independentStudyGenealogy
evidenceGenealogy threePapersShared88SiteCarrier = sharedCarrierGenealogy

publicationIndependenceDefect :
  INF.NonFactorabilityWitness publicationCountSurface evidenceGenealogy
publicationIndependenceDefect = INF.nonFactorabilityWitness
  threeIndependentStudyCarriers
  threePapersShared88SiteCarrier
  refl
  (λ ())

publicationMultiplicityCannotFactorStudyIndependence :
  INF.FactorsThrough publicationCountSurface evidenceGenealogy → ⊥
publicationMultiplicityCannotFactorStudyIndependence =
  INF.witnessRulesOutEveryFlatFactorisation publicationIndependenceDefect

------------------------------------------------------------------------
-- Same site carrier does not imply same analysis/response/model.
------------------------------------------------------------------------

data SharedCarrierCase : Set where
  same88DifferentResponseA
  same88DifferentResponseB : SharedCarrierCase

data SiteCarrierSurface : Set where same2015Melville88Carrier : SiteCarrierSurface
data AnalysisRole : Set where predatorDistributionAnalysis mammalVegetationAnalysis : AnalysisRole

siteCarrierSurface : SharedCarrierCase → SiteCarrierSurface
siteCarrierSurface _ = same2015Melville88Carrier

analysisRole : SharedCarrierCase → AnalysisRole
analysisRole same88DifferentResponseA = predatorDistributionAnalysis
analysisRole same88DifferentResponseB = mammalVegetationAnalysis

sameCarrierAnalysisDefect : INF.NonFactorabilityWitness siteCarrierSurface analysisRole
sameCarrierAnalysisDefect = INF.nonFactorabilityWitness
  same88DifferentResponseA same88DifferentResponseB refl (λ ())

same88SiteCarrierCannotFactorAnalysisRole :
  INF.FactorsThrough siteCarrierSurface analysisRole → ⊥
same88SiteCarrierCannotFactorAnalysisRole =
  INF.witnessRulesOutEveryFlatFactorisation sameCarrierAnalysisDefect

------------------------------------------------------------------------
-- Cross-analysis consistency is useful evidence but is not an independent
-- replication receipt when the underlying carrier/data genealogy overlaps.
------------------------------------------------------------------------

data AgreementCase : Set where
  agreementIndependentData
  agreementSharedCarrier : AgreementCase

data AgreementSurface : Set where sameCrossPaperAgreement : AgreementSurface
data AgreementWeightClass : Set where independentCorroborativeWeight dependentCorroborativeWeight : AgreementWeightClass

agreementSurface : AgreementCase → AgreementSurface
agreementSurface _ = sameCrossPaperAgreement

agreementWeightClass : AgreementCase → AgreementWeightClass
agreementWeightClass agreementIndependentData = independentCorroborativeWeight
agreementWeightClass agreementSharedCarrier = dependentCorroborativeWeight

agreementWeightDefect : INF.NonFactorabilityWitness agreementSurface agreementWeightClass
agreementWeightDefect = INF.nonFactorabilityWitness
  agreementIndependentData agreementSharedCarrier refl (λ ())

agreementCannotFactorIndependentCorroborativeWeight :
  INF.FactorsThrough agreementSurface agreementWeightClass → ⊥
agreementCannotFactorIndependentCorroborativeWeight =
  INF.witnessRulesOutEveryFlatFactorisation agreementWeightDefect

------------------------------------------------------------------------
-- Dependency matrix: currently paid at carrier-family level only.
------------------------------------------------------------------------

record TiwiEvidenceDependencyMatrix : Set where
  constructor tiwi-evidence-dependency-matrix
  field
    davies2017Davies2020Share2015SiteNetwork : Bool
    davies2017Penton2021Share2015SiteNetwork : Bool
    allThreeShare88SiteCarrierFamily : Bool
    exactRowIdentityPaid : Bool
    exactRawDataIdentityPaid : Bool
    exactCameraRecordIdentityAcrossAllThreePaid : Bool
    exactResponseVariableIdentityPaid : Bool
    exactModelIdentityPaid : Bool
    independentReplicationPaid : Bool
open TiwiEvidenceDependencyMatrix public

canonicalTiwiEvidenceDependencyMatrix : TiwiEvidenceDependencyMatrix
canonicalTiwiEvidenceDependencyMatrix =
  tiwi-evidence-dependency-matrix
    true true true
    false false false false false false

------------------------------------------------------------------------
-- QID / Dewey / DOI travel from the owners that paid them.
------------------------------------------------------------------------

systematicReviewIdentity = Synthesis.systematicReviewQid
metaAnalysisIdentity = Synthesis.metaAnalysisQid
peerReviewIdentity = Synthesis.peerReviewQid
reproducibilityIdentity = Replication.reproducibilityQid
scientificConsensusIdentity = Replication.scientificConsensusQid

tiwiDisturbanceIdentity = Tiwi88.ecologicalDisturbanceQid
herbivoryIdentity = Tiwi88.herbivoryQid
waterBuffaloIdentity = Tiwi88.waterBuffaloQid
horseIdentity = Tiwi88.horseQid

pairwiseKnowledgeCoordinate = Tiwi88.same88PairwiseCoordinate

------------------------------------------------------------------------
-- Reverse BIDI constraints.
------------------------------------------------------------------------

record TiwiIndependenceReverseConstraint : Set where
  constructor tiwi-independence-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open TiwiIndependenceReverseConstraint public

replicationConstraint : TiwiIndependenceReverseConstraint
replicationConstraint = tiwi-independence-reverse-constraint
  "Replication / corroboration"
  "publication count, site/data genealogy, methodological independence, response-variable independence and model independence remain separate"
  false

ecologyConstraint : TiwiIndependenceReverseConstraint
ecologyConstraint = tiwi-independence-reverse-constraint
  "Ecology / disturbance / predator-prey"
  "shared site carrier, distinct driver variables, distinct response variables, cross-analysis agreement and causal mediation remain separate"
  false

metaResearchConstraint : TiwiIndependenceReverseConstraint
metaResearchConstraint = tiwi-independence-reverse-constraint
  "Evidence synthesis / meta-research"
  "multiple publications from one carrier family cannot be weighted as independent studies without an explicit dependence model"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data ThreePapersMeanThreeIndependentReplications : Set where
data Same88MeansSameRawData : Set where
data SameCarrierMeansSameModel : Set where
data CrossPaperAgreementMeansIndependentCorroboration : Set where
data PeerReviewMeansIndependence : Set where

threePapersDoNotCreateThreeIndependentReplications :
  ThreePapersMeanThreeIndependentReplications → ⊥
threePapersDoNotCreateThreeIndependentReplications ()

same88DoesNotCreateRawDataIdentity : Same88MeansSameRawData → ⊥
same88DoesNotCreateRawDataIdentity ()

sameCarrierDoesNotCreateSameModel : SameCarrierMeansSameModel → ⊥
sameCarrierDoesNotCreateSameModel ()

crossPaperAgreementDoesNotCreateIndependentCorroboration :
  CrossPaperAgreementMeansIndependentCorroboration → ⊥
crossPaperAgreementDoesNotCreateIndependentCorroboration ()

peerReviewDoesNotCreateIndependence : PeerReviewMeansIndependence → ⊥
peerReviewDoesNotCreateIndependence ()

firstUnpaidDependencyReceipt : String
firstUnpaidDependencyReceipt =
  "For each Davies 2017 / Davies 2020 / Penton 2021 pair, recover exact row/raw-camera/derived-variable provenance and build a dependence matrix before any evidence synthesis weights them as independent replications."

record Tiwi88SiteEvidenceIndependenceBoundary : Set where
  constructor tiwi-88-site-evidence-independence-boundary
  field
    threeSourceDoisRetained : Bool
    qidCoordinatesRetained : Bool
    deweyCoordinateRetained : Bool
    shared88CarrierPaid : Bool
    publicationCountSeparatedFromIndependence : Bool
    sharedCarrierSeparatedFromAnalysisRole : Bool
    crossPaperAgreementSeparatedFromIndependentCorroboration : Bool
    exactRowAndRawDataDependenceStillOpen : Bool
    parentEvidenceSynthesisGrammarReused : Bool
    consumerSpecificDependencyMatrixIsNext : Bool
open Tiwi88SiteEvidenceIndependenceBoundary public

canonicalTiwi88SiteEvidenceIndependenceBoundary :
  Tiwi88SiteEvidenceIndependenceBoundary
canonicalTiwi88SiteEvidenceIndependenceBoundary =
  tiwi-88-site-evidence-independence-boundary
    true true true true true true true true true true
