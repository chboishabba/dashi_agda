module DASHI.Reasoning.SensibLawCorpusWorldPNFBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.SensibLawSpacyPredicateNormalFormBridgeExact as SpacyBridge
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone

------------------------------------------------------------------------
-- DOCUMENT -> SOURCE CORPUS -> WORLD RESOLUTION HORIZONS
--
-- SensibLaw's strict numeric PNF closes a document interface while carrying
-- residual demands and explicitly deferring world resolution. This owner turns
-- that runtime boundary into a proof-facing context spine for evidence claims.
------------------------------------------------------------------------

data PNFResolutionHorizon : Set where
  documentLocalHorizon
  citedSourceCorpusHorizon
  externalWorldHorizon
  : PNFResolutionHorizon

data ResolutionStatus : Set where
  unresolvedResolution
  partiallyResolved
  resolvedWithReceipt
  : ResolutionStatus

record HorizonResolutionReceipt : Set where
  constructor horizonResolutionReceipt
  field
    horizon : PNFResolutionHorizon
    status : ResolutionStatus
    inputReferences : List String
    resolvedReferences : List String
    residualDemandReferences : List String
    identityOrSemanticsReference : String
    authorityReference : String

open HorizonResolutionReceipt public

record SensibLawCorpusWorldContext
    {source : Cone.NaturalLanguageExperimentalAssertion}
    (documentReceipt : SpacyBridge.SensibLawNumericPNFReceipt source) : Set₁ where
  constructor sensibLawCorpusWorldContext
  field
    documentResolution : HorizonResolutionReceipt
    citedSourceResolution : HorizonResolutionReceipt
    worldResolution : HorizonResolutionReceipt

    documentHorizonExact :
      horizon documentResolution ≡ documentLocalHorizon
    citedHorizonExact :
      horizon citedSourceResolution ≡ citedSourceCorpusHorizon
    worldHorizonExact :
      horizon worldResolution ≡ externalWorldHorizon

    citationTraversalReference : String
    crossDocumentIdentityReference : String
    worldKnowledgeReference : String
    unresolvedDemandCarryReference : String

open SensibLawCorpusWorldContext public

------------------------------------------------------------------------
-- Every evidential interpretation can name which horizon warrants it.
------------------------------------------------------------------------

record EvidentialPNFHorizonProvenance : Set where
  constructor evidentialPNFHorizonProvenance
  field
    predicateOrScopeReference : String
    requiredHorizon : PNFResolutionHorizon
    resolutionStatus : ResolutionStatus
    evidenceReference : String
    unresolvedReference : String

open EvidentialPNFHorizonProvenance public

record CorpusWorldPNFBoundary : Set where
  constructor corpusWorldPNFBoundary
  field
    closedDocumentPNFMeansWorldClosed : Bool
    closedDocumentPNFMeansWorldClosedIsFalse :
      closedDocumentPNFMeansWorldClosed ≡ false
    citedSourceRecoveryEqualsWorldIdentity : Bool
    citedSourceRecoveryEqualsWorldIdentityIsFalse :
      citedSourceRecoveryEqualsWorldIdentity ≡ false
    localDependencyParseMaySupportLocalPredicateExtraction : Bool
    localDependencyParseMaySupportLocalPredicateExtractionIsTrue :
      localDependencyParseMaySupportLocalPredicateExtraction ≡ true
    transportOrWorldClaimMayRequireExternalHorizon : Bool
    transportOrWorldClaimMayRequireExternalHorizonIsTrue :
      transportOrWorldClaimMayRequireExternalHorizon ≡ true
    residualDemandsPropagateAcrossHorizons : Bool
    residualDemandsPropagateAcrossHorizonsIsTrue :
      residualDemandsPropagateAcrossHorizons ≡ true

canonicalCorpusWorldPNFBoundary : CorpusWorldPNFBoundary
canonicalCorpusWorldPNFBoundary =
  corpusWorldPNFBoundary false refl false refl true refl true refl true refl
