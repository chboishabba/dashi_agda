module DASHI.Cognition.PNF.SensibLawOALCSectionPNFSemanticAdmissionBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Interop.SensibLawResidualLattice as Residual
import DASHI.Cognition.PNF.SensibLawSpacyCompositionOnlySemanticConstitutionExact as Constitution
import DASHI.Cognition.PNF.SensibLawLegalSemanticAdmissionFrontierExact as Admission
import DASHI.Cognition.PNF.SensibLawAttributedSourcePNFCandidateWeldExact as Weld
import DASHI.Cognition.PNF.SensibLawOALCLegislationParserInputContractExact as OALC

------------------------------------------------------------------------
-- OALC SECTION -> PNF -> SEMANTIC ADMISSION BRIDGE
--
-- This owner binds the actual OALC source-resolution/slice carrier to the
-- existing generic attributed PNF candidate weld. It does NOT classify an OALC
-- parser output as a legal atom. The semantic-candidate relationship remains a
-- reviewed/admitted coordinate supplied downstream.
--
--   governed OALC document receipt
--     -> source-preserving section slice
--     -> parser handoff
--     -> PNF emission
--     -> candidate fibre
--     -> existing reviewed AttributedPNFCandidateWeld.
------------------------------------------------------------------------

record OALCSectionPNFCandidateBridge
    {dataset : OALC.OALCDatasetSelection}
    {demand : OALC.OALCLegislationSourceDemand}
    (parent : OALC.OALCResolvedDocumentReceipt dataset demand)
    (slice : OALC.OALCSectionSliceReceipt parent) : Set₁ where
  constructor oalc-section-pnf-candidate-bridge
  field
    parserHandoff : OALC.OALCParserHandoff slice
    emission : Residual.PNFEmissionReceipt
    candidateFibre : Constitution.SemanticCandidateFibre

    -- Runtime/source projection owns this exact retained source-span identity.
    expectedEmissionSpanRef : String
    emissionSpanMatchesExpected :
      Residual.PNFEmissionReceipt.sourceSpan emission ≡ expectedEmissionSpanRef
    sectionProjectionMatchesExpected :
      OALC.OALCSectionSliceReceipt.sourcePreservingProjectionRef slice
      ≡ expectedEmissionSpanRef

    -- This is provenance/identity only. It is not a semantic promotion.
    parserRelationshipRef : String

open OALCSectionPNFCandidateBridge public

record AdmittedOALCSectionPNFCandidate
    {dataset : OALC.OALCDatasetSelection}
    {demand : OALC.OALCLegislationSourceDemand}
    {parent : OALC.OALCResolvedDocumentReceipt dataset demand}
    {slice : OALC.OALCSectionSliceReceipt parent}
    (bridge : OALCSectionPNFCandidateBridge parent slice) : Set₁ where
  constructor admitted-oalc-section-pnf-candidate
  field
    attributedSource : Source.AttributedSource
    reviewAuthority : Admission.ResolutionAuthority
    reviewReference : String
    candidateSourceRelationship : String

    -- Existing canonical generic weld remains the semantic-admission owner.
    genericWeld : Weld.AttributedPNFCandidateWeld

    weldUsesSameSource :
      Weld.attributedSource genericWeld ≡ attributedSource
    weldUsesSameEmission :
      Weld.emission genericWeld ≡ OALCSectionPNFCandidateBridge.emission bridge
    weldUsesSameCandidate :
      Weld.candidateFibre genericWeld ≡ OALCSectionPNFCandidateBridge.candidateFibre bridge
    weldUsesSameReviewAuthority :
      Weld.reviewAuthority genericWeld ≡ reviewAuthority
    weldUsesSameLocator :
      Weld.sourceLocator genericWeld
      ≡ OALCSectionPNFCandidateBridge.expectedEmissionSpanRef bridge

open AdmittedOALCSectionPNFCandidate public

------------------------------------------------------------------------
-- The bridge is intentionally non-promoting.
------------------------------------------------------------------------

data OALCPNFEmissionAutomaticallyIdentifiesLegalAtom : Set where
data OALCSectionHeadingAutomaticallyIdentifiesWrongElement : Set where
data ParserNegationAutomaticallyCreatesAtomicNegative : Set where
data PNFConditionAutomaticallyCreatesLegalPremise : Set where
data PNFExceptionAutomaticallyCreatesLegalDefeater : Set where
data PNFAttributionAutomaticallyCreatesAuthorityRole : Set where
data LatestKnownOALCTextAutomaticallyPaysHistoricalApplicability : Set where
data AdmittedCandidateAutomaticallyCreatesAtomicGate : Set where

pnfEmissionDoesNotAutomaticallyIdentifyLegalAtom :
  OALCPNFEmissionAutomaticallyIdentifiesLegalAtom → ⊥
pnfEmissionDoesNotAutomaticallyIdentifyLegalAtom ()

sectionHeadingDoesNotAutomaticallyIdentifyWrongElement :
  OALCSectionHeadingAutomaticallyIdentifiesWrongElement → ⊥
sectionHeadingDoesNotAutomaticallyIdentifyWrongElement ()

parserNegationDoesNotCreateAtomicNegative :
  ParserNegationAutomaticallyCreatesAtomicNegative → ⊥
parserNegationDoesNotCreateAtomicNegative ()

pnfConditionDoesNotCreateLegalPremise :
  PNFConditionAutomaticallyCreatesLegalPremise → ⊥
pnfConditionDoesNotCreateLegalPremise ()

pnfExceptionDoesNotCreateLegalDefeater :
  PNFExceptionAutomaticallyCreatesLegalDefeater → ⊥
pnfExceptionDoesNotCreateLegalDefeater ()

pnfAttributionDoesNotCreateAuthorityRole :
  PNFAttributionAutomaticallyCreatesAuthorityRole → ⊥
pnfAttributionDoesNotCreateAuthorityRole ()

latestKnownTextDoesNotPayHistoricalApplicability :
  LatestKnownOALCTextAutomaticallyPaysHistoricalApplicability → ⊥
latestKnownTextDoesNotPayHistoricalApplicability ()

admittedCandidateDoesNotCreateAtomicGate :
  AdmittedCandidateAutomaticallyCreatesAtomicGate → ⊥
admittedCandidateDoesNotCreateAtomicGate ()

record OALCSectionPNFSemanticAdmissionBoundary : Set where
  constructor oalc-section-pnf-semantic-admission-boundary
  field
    governedDocumentReceiptRequired : Bool
    sourcePreservingSectionSliceRequired : Bool
    exactPNFSpanWeldRequired : Bool
    genericAttributedCandidateWeldReused : Bool
    parserMayAssignLegalAtomAutomatically : Bool
    parserNegationCreatesAtomicNegative : Bool
    admittedCandidateCreatesAtomicGate : Bool
    latestKnownTextPaysHistoricalApplicability : Bool

canonicalOALCSectionPNFSemanticAdmissionBoundary :
  OALCSectionPNFSemanticAdmissionBoundary
canonicalOALCSectionPNFSemanticAdmissionBoundary =
  oalc-section-pnf-semantic-admission-boundary
    true true true true false false false false
