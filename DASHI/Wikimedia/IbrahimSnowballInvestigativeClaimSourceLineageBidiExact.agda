module DASHI.Wikimedia.IbrahimSnowballInvestigativeClaimSourceLineageBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey
import DASHI.Wikimedia.IbrahimSnowballSourceGenealogyIndependenceEvidenceSynthesisBidiExact as Genealogy

------------------------------------------------------------------------
-- THIN INVESTIGATIVE CLAIM ROUTER
--
-- The imported genealogy stack already owns dependence, synthesis, information
-- cascades, source quality, replication genealogy and primary-source role.
-- This file makes the concrete CLAIM the routed object.
--
-- A claim can be seen in many places while still descending from one source.
-- A primary source can be inspected yet inaccurate.  A secondary source can be
-- useful yet derivative.  A citation can exist without the cited carrier ever
-- having been inspected.  Promotion is therefore paid claim-by-claim by an
-- explicit source-lineage / acquisition / independence receipt.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim investigative claim/source-lineage BIDI"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not create truth, inspection, independence, evidentiary weight or same-object continuity")

primarySourceQid : Identity.ExternalIdentityDemand
primarySourceQid = Genealogy.primarySourceQid

secondarySourceQid : Identity.ExternalIdentityDemand
secondarySourceQid = mkQid "secondary source" "Q905511"

tertiarySourceQid : Identity.ExternalIdentityDemand
tertiarySourceQid = mkQid "tertiary source" "Q1063801"

citationAnalysisQid : Identity.ExternalIdentityDemand
citationAnalysisQid = Identity.mkOptionalIdentityDemand
  "Ibrahim investigative claim/source-lineage BIDI"
  "external concept identity"
  "claim-specific citation analysis / citation-network analysis"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact same-concept QID safely promoted in this pass; bibliometrics/citation-analysis neighbours must not be substituted without same-object inspection")

------------------------------------------------------------------------
-- Dewey remains a library coordinate, not a source hierarchy.
------------------------------------------------------------------------

primarySourceDewey : Dewey.DeweyCoordinate
primarySourceDewey = Genealogy.primarySourceDewey

secondarySourceDewey : Dewey.DeweyCoordinate
secondarySourceDewey = Dewey.mkUnresolvedDewey
  "secondary source"
  "Q905511 verified; no exact inspected DDC value promoted in this pass"

tertiarySourceDewey : Dewey.DeweyCoordinate
tertiarySourceDewey = Dewey.mkUnresolvedDewey
  "tertiary source"
  "Q1063801 verified; no exact inspected DDC value promoted in this pass"

------------------------------------------------------------------------
-- Source-paid calibration: claim-specific citation networks can expose copied
-- authority, dead-end citation, amplification and hypothesis-to-fact drift.
------------------------------------------------------------------------

greenbergClaimCitationNetworkSource : Attribution.AttributedSource
greenbergClaimCitationNetworkSource = Attribution.mkDOISource
  "Steven A. Greenberg"
  "How citation distortions create unfounded authority: analysis of a citation network"
  "BMJ 339:b2680"
  "2009"
  "10.1136/bmj.b2680"
  "https://doi.org/10.1136/bmj.b2680"
  Attribution.academicArticleSource
  "claim-specific citation-network analysis of citation bias, amplification, invention and dead-end citation; calibrates source genealogy but does not establish that every highly cited claim is distorted"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Source role is relational to the investigated claim/event.
------------------------------------------------------------------------

data InvestigativeSourceRole : Set where
  primaryCarrier : InvestigativeSourceRole
  secondaryCarrier : InvestigativeSourceRole
  tertiaryCarrier : InvestigativeSourceRole
  derivativeCopy : InvestigativeSourceRole
  independentCorroboratingCarrier : InvestigativeSourceRole
  roleUnresolved : InvestigativeSourceRole

data AcquisitionState : Set where
  identifiedOnly : AcquisitionState
  acquiredNotInspected : AcquisitionState
  inspected : AcquisitionState
  inspectedAndClaimLocated : AcquisitionState

data IndependenceState : Set where
  independenceUnresolved : IndependenceState
  commonSourceDependent : IndependenceState
  independentlyOriginated : IndependenceState

data PromotionState : Set where
  retainOnly : PromotionState
  supportsBoundedClaim : PromotionState
  promotionBlocked : PromotionState

record InvestigativeClaimReceipt : Set where
  constructor investigative-claim-receipt
  field
    claimLabel : String
    claimIdentity : String
    carrierLabel : String
    carrierCanonicalLink : String
    carrierRole : InvestigativeSourceRole
    acquisition : AcquisitionState
    genealogyReceipt : String
    independence : IndependenceState
    sameObjectReceipt : String
    firstUnpaidLeaf : String
    promotion : PromotionState
    qidDoiDeweyTravelSeparately : Bool
    citationCreatesInspection : Bool
    roleCreatesTruth : Bool
open InvestigativeClaimReceipt public

------------------------------------------------------------------------
-- Regression 1: mention/citation multiplicity cannot recover independence.
------------------------------------------------------------------------

data MentionCase : Set where
  sameMentionCountCommonAncestor sameMentionCountIndependentOrigins : MentionCase

data MentionSurface : Set where sameMentionMultiplicity : MentionSurface

data MentionIndependence : Set where oneCommonAncestor genuinelyIndependentOrigins : MentionIndependence

mentionSurface : MentionCase → MentionSurface
mentionSurface _ = sameMentionMultiplicity

mentionIndependence : MentionCase → MentionIndependence
mentionIndependence sameMentionCountCommonAncestor = oneCommonAncestor
mentionIndependence sameMentionCountIndependentOrigins = genuinelyIndependentOrigins

mentionIndependenceDefect :
  INF.NonFactorabilityWitness mentionSurface mentionIndependence
mentionIndependenceDefect = INF.nonFactorabilityWitness
  sameMentionCountCommonAncestor sameMentionCountIndependentOrigins refl (λ ())

mentionMultiplicityCannotFactorIndependentEvidence :
  INF.FactorsThrough mentionSurface mentionIndependence → ⊥
mentionMultiplicityCannotFactorIndependentEvidence =
  INF.witnessRulesOutEveryFlatFactorisation mentionIndependenceDefect

------------------------------------------------------------------------
-- Regression 2: same claim text cannot recover source genealogy.
------------------------------------------------------------------------

data ClaimTextCase : Set where
  sameTextCopiedChain sameTextIndependentObservation : ClaimTextCase

data ClaimTextSurface : Set where sameClaimText : ClaimTextSurface

data ClaimGenealogy : Set where copiedCitationChain independentOrigin : ClaimGenealogy

claimTextSurface : ClaimTextCase → ClaimTextSurface
claimTextSurface _ = sameClaimText

claimGenealogy : ClaimTextCase → ClaimGenealogy
claimGenealogy sameTextCopiedChain = copiedCitationChain
claimGenealogy sameTextIndependentObservation = independentOrigin

claimGenealogyDefect : INF.NonFactorabilityWitness claimTextSurface claimGenealogy
claimGenealogyDefect = INF.nonFactorabilityWitness
  sameTextCopiedChain sameTextIndependentObservation refl (λ ())

sameClaimTextCannotFactorSourceGenealogy :
  INF.FactorsThrough claimTextSurface claimGenealogy → ⊥
sameClaimTextCannotFactorSourceGenealogy =
  INF.witnessRulesOutEveryFlatFactorisation claimGenealogyDefect

------------------------------------------------------------------------
-- Regression 3: citation presence cannot recover inspection/payment state.
------------------------------------------------------------------------

data CitationInspectionCase : Set where
  citedButNotInspected citedAndClaimLocated : CitationInspectionCase

data CitationSurface : Set where sameCitationPresent : CitationSurface

data InspectionPayment : Set where inspectionUnpaid inspectionAndClaimPaid : InspectionPayment

citationSurface : CitationInspectionCase → CitationSurface
citationSurface _ = sameCitationPresent

inspectionPayment : CitationInspectionCase → InspectionPayment
inspectionPayment citedButNotInspected = inspectionUnpaid
inspectionPayment citedAndClaimLocated = inspectionAndClaimPaid

citationInspectionDefect : INF.NonFactorabilityWitness citationSurface inspectionPayment
citationInspectionDefect = INF.nonFactorabilityWitness
  citedButNotInspected citedAndClaimLocated refl (λ ())

citationPresenceCannotFactorInspectionPayment :
  INF.FactorsThrough citationSurface inspectionPayment → ⊥
citationPresenceCannotFactorInspectionPayment =
  INF.witnessRulesOutEveryFlatFactorisation citationInspectionDefect

------------------------------------------------------------------------
-- Regression 4: source role cannot recover truth.
------------------------------------------------------------------------

data RoleTruthCase : Set where
  samePrimaryRoleTrueClaim samePrimaryRoleFalseClaim : RoleTruthCase

data RoleSurface : Set where samePrimaryRole : RoleSurface

data ClaimTruth : Set where claimTrue claimFalse : ClaimTruth

roleSurface : RoleTruthCase → RoleSurface
roleSurface _ = samePrimaryRole

claimTruth : RoleTruthCase → ClaimTruth
claimTruth samePrimaryRoleTrueClaim = claimTrue
claimTruth samePrimaryRoleFalseClaim = claimFalse

roleTruthDefect : INF.NonFactorabilityWitness roleSurface claimTruth
roleTruthDefect = INF.nonFactorabilityWitness
  samePrimaryRoleTrueClaim samePrimaryRoleFalseClaim refl (λ ())

primaryRoleCannotFactorClaimTruth :
  INF.FactorsThrough roleSurface claimTruth → ⊥
primaryRoleCannotFactorClaimTruth =
  INF.witnessRulesOutEveryFlatFactorisation roleTruthDefect

------------------------------------------------------------------------
-- Ordered residual router: acquisition may snowball out of dependency order,
-- but promotion waits for the first claim-paying unpaid leaf.
------------------------------------------------------------------------

record ClaimResidualRouter : Set where
  constructor claim-residual-router
  field
    claim : String
    earliestReachableCarrier : String
    laterDerivativeEvidenceMayBeRetained : Bool
    laterIndependentEvidenceMayBeRetained : Bool
    exactFirstUnpaidLeaf : String
    laterEvidenceAutomaticallyPaysEarlierLeaf : Bool
    promotionAllowedBeforeLeafPaid : Bool
open ClaimResidualRouter public

mkClaimResidualRouter : String → String → String → ClaimResidualRouter
mkClaimResidualRouter claimLabel earliest leaf =
  claim-residual-router claimLabel earliest true true leaf false false

------------------------------------------------------------------------
-- Reuse generic source genealogy rather than defining another synthesis model.
------------------------------------------------------------------------

genealogyBoundary : Genealogy.SourceGenealogyIndependenceEvidenceSynthesisBoundary
genealogyBoundary = Genealogy.canonicalSourceGenealogyIndependenceEvidenceSynthesisBoundary

------------------------------------------------------------------------
-- Reverse BIDI constraints.
------------------------------------------------------------------------

record InvestigativeReverseConstraint : Set where
  constructor investigative-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open InvestigativeReverseConstraint public

investigationConstraint : InvestigativeReverseConstraint
investigationConstraint = investigative-reverse-constraint
  "Investigation / OSINT"
  "claim identity, carrier identity, primary/secondary relation, inspection state, copying genealogy, independence, same-object continuity and unresolved leaf remain distinct"
  false

scienceConstraint : InvestigativeReverseConstraint
scienceConstraint = investigative-reverse-constraint
  "Science / evidence synthesis"
  "paper count, citation count, primary data, replication, independence, synthesis and consensus remain distinct"
  false

historyConstraint : InvestigativeReverseConstraint
historyConstraint = investigative-reverse-constraint
  "History / archives"
  "surviving mention, original carrier, derivative retelling, acquisition, inspection and independent corroboration remain distinct"
  false

mediaConstraint : InvestigativeReverseConstraint
mediaConstraint = investigative-reverse-constraint
  "Media / information cascades"
  "many outlets repeating one upstream report must not be counted as many independent sources"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data PrimaryMeansTrue : Set where
data SecondaryMeansInvalid : Set where
data CitationMeansInspected : Set where
data MentionCountMeansIndependentEvidence : Set where
data QidMeansSamePublication : Set where
data DOIProvesClaim : Set where
data DeweyMeansEvidenceRank : Set where

primaryDoesNotMeanTrue : PrimaryMeansTrue → ⊥
primaryDoesNotMeanTrue ()

secondaryDoesNotMeanInvalid : SecondaryMeansInvalid → ⊥
secondaryDoesNotMeanInvalid ()

citationDoesNotMeanInspected : CitationMeansInspected → ⊥
citationDoesNotMeanInspected ()

mentionCountDoesNotMeanIndependentEvidence : MentionCountMeansIndependentEvidence → ⊥
mentionCountDoesNotMeanIndependentEvidence ()

qidDoesNotMeanSamePublication : QidMeansSamePublication → ⊥
qidDoesNotMeanSamePublication ()

doiDoesNotProveClaim : DOIProvesClaim → ⊥
doiDoesNotProveClaim ()

deweyDoesNotMeanEvidenceRank : DeweyMeansEvidenceRank → ⊥
deweyDoesNotMeanEvidenceRank ()

record InvestigativeClaimSourceLineageBoundary : Set where
  constructor investigative-claim-source-lineage-boundary
  field
    existingGenealogyStackReused : Bool
    primarySecondaryTertiaryQidsAttached : Bool
    unresolvedCitationAnalysisQidRetained : Bool
    deweyUnresolvedStatesRetained : Bool
    greenbergPrimaryCalibrationAttributed : Bool
    sourceRoleSeparatedFromTruth : Bool
    citationSeparatedFromInspection : Bool
    multiplicitySeparatedFromIndependence : Bool
    claimTextSeparatedFromGenealogy : Bool
    orderedFirstUnpaidLeafRetained : Bool
    acquisitionMaySnowballOutOfPaymentOrder : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open InvestigativeClaimSourceLineageBoundary public

canonicalInvestigativeClaimSourceLineageBoundary :
  InvestigativeClaimSourceLineageBoundary
canonicalInvestigativeClaimSourceLineageBoundary =
  investigative-claim-source-lineage-boundary
    true true true true true true true true true true true true false
