module DASHI.Education.DigitalESDAcademicCorpusWorldCrossPollinationRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Education.DigitalESDAcademicCorpusWorldCrossPollinationExact as Bridge
import DASHI.Education.DigitalESDSLRSourceReviewBridgeExact as Review
import DASHI.Education.DigitalESDStudyClaimCeilingExact as Ceiling
import DASHI.Wikimedia.IbrahimSnowballSystematicReviewMetaAnalysisPublicationBiasBidiExact as Systematic
import DASHI.Wikimedia.IbrahimSnowballEvidenceSynthesisSourceIndependenceParetoBidiExact as Independence

slrOwnerRegression :
  Bridge.slrReviewBoundary ≡ Review.canonicalDigitalESDSLRBridgeBoundary
slrOwnerRegression = refl

claimCeilingOwnerRegression :
  Bridge.studyClaimCeilingBoundary ≡ Ceiling.canonicalStudyClaimCeilingBoundary
claimCeilingOwnerRegression = refl

systematicOwnerRegression :
  Bridge.systematicReviewBoundary
  ≡ Systematic.canonicalSystematicReviewMetaAnalysisBoundary
systematicOwnerRegression = refl

includedCountRegression :
  INF.FactorsThrough Systematic.includedCountSurface Systematic.evidenceIndependence → ⊥
includedCountRegression = Bridge.includedStudyCountCannotRecoverIndependentEvidenceUnits

pooledEstimateRegression :
  INF.FactorsThrough Systematic.pooledSurface Systematic.selectionBiasStatus → ⊥
pooledEstimateRegression = Bridge.pooledEstimateCannotRecoverPublicationBiasState

reviewInclusionRegression :
  INF.FactorsThrough Systematic.inclusionSurface Systematic.evidentiaryWeight → ⊥
reviewInclusionRegression = Bridge.reviewInclusionCannotRecoverEvidentiaryWeight

citationPrimaryRegression :
  INF.FactorsThrough Independence.citationSurface Independence.primarySupport → ⊥
citationPrimaryRegression = Bridge.citationAgreementCannotRecoverPrimarySupport

sourceIndependenceRegression :
  INF.FactorsThrough Independence.perceivedIndependence Independence.provenanceIndependence → ⊥
sourceIndependenceRegression =
  Bridge.perceivedSourceIndependenceCannotRecoverProvenanceIndependence
