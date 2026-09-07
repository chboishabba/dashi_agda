module DASHI.Culture.FourfoldRetreatIndigenousPluralAuthorityCrossPollinationExact where

------------------------------------------------------------------------
-- FOURFOLD RETREAT x INDIGENOUS PLURAL AUTHORITY CROSS-POLLINATION
--
-- This is a structural comparison owner only.
--
-- It does NOT assert:
--   * that Indigenous knowledge is poststructuralism;
--   * that Mabo, Two-Eyed Seeing, Kimmerer or Australian Indigenous legal
--     orders belong to one doctrine;
--   * that any Indigenous source owns the DASHI theorems below;
--   * that one Australian/Torres Strait fixture universalises Indigenous law
--     or epistemology;
--   * that recognition by a state/court creates antecedent Indigenous law,
--     authority, provenance or relation to Country.
--
-- Attribution boundary:
--   source proposition / living authority
--   != later interpretation
--   != cross-domain analogy
--   != DASHI finite construction
--   != school-wide or civilisation-wide classification.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Culture.FoucaultDerridaFourfoldRetreatAxisCrossPollinationExact as Fourfold
import DASHI.Culture.PoststructuralismFourfoldRetreatCrossPollinationExact as PS
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as IK
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed
import DASHI.Culture.KimmererBraidingAcknowledgement as Kimmerer
import DASHI.Cognition.PNF.SensibLawMaboTwoLegalOrderFibreExact as Mabo
import DASHI.Cognition.PNF.SensibLawMaboLandBackSourceAttributionAuditExact as MaboAudit
import DASHI.Cognition.PNF.SensibLawBillySituatedKnowledgeRemedyAdequacyExact as Billy
import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- 1. Plural knowledge carriers do not imply epistemic fusion or relativism.
------------------------------------------------------------------------

data PluralKnowledgeReading : Set where
  coordinatedDistinctWarrants
  fusedSingleEpistemology
  anythingGoesRelativism
  : PluralKnowledgeReading

twoEyedReading : PluralKnowledgeReading
twoEyedReading = coordinatedDistinctWarrants

coordinatedKnowledgeIsNotFusion :
  twoEyedReading ≡ fusedSingleEpistemology → ⊥
coordinatedKnowledgeIsNotFusion ()

coordinatedKnowledgeIsNotAnythingGoes :
  twoEyedReading ≡ anythingGoesRelativism → ⊥
coordinatedKnowledgeIsNotAnythingGoes ()

sharedObservationStillDoesNotRecoverProvenance :
  INF.FactorsThrough TwoEyed.observeKnowledgeHistory TwoEyed.provenance → ⊥
sharedObservationStillDoesNotRecoverProvenance =
  TwoEyed.sharedObservationDoesNotRecoverProvenance

------------------------------------------------------------------------
-- 2. Material relation / authority / obligation survive proposition extraction.
------------------------------------------------------------------------

sameExtractedContentCannotRecoverAuthority :
  INF.FactorsThrough IK.extractedProposition IK.authority → ⊥
sameExtractedContentCannotRecoverAuthority = IK.propositionCannotRecoverAuthority

sameExtractedContentCannotRecoverPermission :
  INF.FactorsThrough IK.extractedProposition IK.permission → ⊥
sameExtractedContentCannotRecoverPermission = IK.propositionCannotRecoverPermission

sameExtractedContentCannotRecoverObligation :
  INF.FactorsThrough IK.extractedProposition IK.obligation → ⊥
sameExtractedContentCannotRecoverObligation = IK.propositionCannotRecoverObligation

------------------------------------------------------------------------
-- 3. Mabo's two-order architecture supplies a direct anti-collapse pattern.
--
-- The Crown order can recognise an Indigenous interest without thereby
-- creating the antecedent Indigenous order. Translation across orders is not
-- semantic identity, and municipal legal effect is not a theorem of legitimate
-- sovereignty transfer.
------------------------------------------------------------------------

maboRecognitionDoesNotCreateIndigenousLaw :
  Mabo.CrownRecognitionCreatesIndigenousLaw → ⊥
maboRecognitionDoesNotCreateIndigenousLaw = Mabo.recognitionDoesNotCreateIndigenousLaw

maboTranslationDoesNotMeanIdentity :
  Mabo.CrossOrderTranslationMeansSemanticIdentity → ⊥
maboTranslationDoesNotMeanIdentity = Mabo.translationDoesNotMeanIdentity

maboMunicipalEffectDoesNotProveLegitimateTransfer :
  Mabo.MunicipalLegalEffectProvesLegitimateSovereigntyTransfer → ⊥
maboMunicipalEffectDoesNotProveLegitimateTransfer =
  Mabo.municipalEffectDoesNotProveLegitimateTransfer

------------------------------------------------------------------------
-- 4. Consultation/recognition surface does not recover community authority.
------------------------------------------------------------------------

consultationRecordCannotRecoverAuthorityParticipation :
  INF.FactorsThrough Billy.consultationSurface Billy.authorityParticipation → ⊥
consultationRecordCannotRecoverAuthorityParticipation =
  Billy.consultationRecordCannotRecoverAuthorityParticipation

consultationRecordCannotRecoverReciprocity :
  INF.FactorsThrough Billy.consultationSurface Billy.reciprocalImplementation → ⊥
consultationRecordCannotRecoverReciprocity =
  Billy.consultationRecordCannotRecoverReciprocalImplementation

------------------------------------------------------------------------
-- 5. Cross-pollination with the fourfold-retreat problem.
--
-- A framework may reject epistemic fusion, preserve plural authority, retain
-- material land/Country relations and still remain rationally discriminating.
-- Therefore the following promotions are blocked independently.
------------------------------------------------------------------------

data EpistemicPluralityMeansRetreatFromReason : Set where
data ProvenancePluralityMeansRelativism : Set where
data DistinctLegalOrdersMeanAntiMaterialism : Set where
data RecognitionWithoutCreationMeansAntiInstitutionalism : Set where
data BraidingMeansConceptualFusion : Set where
data IndigenousPluralAuthorityIsPoststructuralism : Set where
data FourfoldRetreatCritiqueExhaustsIndigenousEpistemology : Set where

epistemicPluralityDoesNotMeanRetreatFromReason :
  EpistemicPluralityMeansRetreatFromReason → ⊥
epistemicPluralityDoesNotMeanRetreatFromReason ()

provenancePluralityDoesNotMeanRelativism :
  ProvenancePluralityMeansRelativism → ⊥
provenancePluralityDoesNotMeanRelativism ()

distinctLegalOrdersDoNotMeanAntiMaterialism :
  DistinctLegalOrdersMeanAntiMaterialism → ⊥
distinctLegalOrdersDoNotMeanAntiMaterialism ()

recognitionWithoutCreationDoesNotMeanAntiInstitutionalism :
  RecognitionWithoutCreationMeansAntiInstitutionalism → ⊥
recognitionWithoutCreationDoesNotMeanAntiInstitutionalism ()

braidingDoesNotMeanConceptualFusion : BraidingMeansConceptualFusion → ⊥
braidingDoesNotMeanConceptualFusion ()

indigenousPluralAuthorityDoesNotMeanPoststructuralism :
  IndigenousPluralAuthorityIsPoststructuralism → ⊥
indigenousPluralAuthorityDoesNotMeanPoststructuralism ()

fourfoldRetreatDoesNotExhaustIndigenousEpistemology :
  FourfoldRetreatCritiqueExhaustsIndigenousEpistemology → ⊥
fourfoldRetreatDoesNotExhaustIndigenousEpistemology ()

------------------------------------------------------------------------
-- 6. The useful common structure is loss-sensitive plural coordination.
------------------------------------------------------------------------

data CoordinationCoordinate : Set where
  propositionContent
  provenance
  authority
  permission
  obligation
  materialRelation
  legalOrder
  translationInterface
  : CoordinationCoordinate

data CoordinationRequirement : Set where
  preserveDistinct
  coordinateWithoutFusion
  independentlySource
  cannotInferFromSurface
  : CoordinationRequirement

requirement : CoordinationCoordinate → CoordinationRequirement
requirement propositionContent = coordinateWithoutFusion
requirement provenance = preserveDistinct
requirement authority = preserveDistinct
requirement permission = independentlySource
requirement obligation = independentlySource
requirement materialRelation = preserveDistinct
requirement legalOrder = preserveDistinct
requirement translationInterface = cannotInferFromSurface

------------------------------------------------------------------------
-- 7. Source/provenance weld.
------------------------------------------------------------------------

record FourfoldIndigenousCrossPollinationBoundary : Set where
  constructor fourfold-indigenous-cross-pollination-boundary
  field
    fourfoldAxisBoundary : Fourfold.NamedThinkerAxisWeld
    poststructuralismBoundary : PS.FourfoldRetreatCrossPollinationWeld
    kimmererAcknowledgement : Kimmerer.KimmererBraidingAcknowledgement
    twoEyedBoundary : TwoEyed.KimmererTwoEyedSeeingBoundary
    maboAttributionAuditItem : MaboAudit.SourceAttributionAuditItem
    sameObservationDoesNotFuseProvenance : Bool
    extractedContentDoesNotDetermineAuthority : Bool
    courtRecognitionDoesNotCreateIndigenousOrder : Bool
    consultationDoesNotCreateCommunityAuthority : Bool
    pluralAuthorityDoesNotImplyRelativism : Bool
    pluralAuthorityDoesNotImplyIrrationalism : Bool
    materialCountryRelationNotReducedToDiscourse : Bool
    crossDomainSimilarityDoesNotMergeTraditions : Bool
    indigenousAuthorityNotTransferredToDASHI : Bool
    dashiTheoremsNotAttributedToIndigenousSources : Bool

canonicalFourfoldIndigenousCrossPollinationBoundary :
  FourfoldIndigenousCrossPollinationBoundary
canonicalFourfoldIndigenousCrossPollinationBoundary =
  fourfold-indigenous-cross-pollination-boundary
    Fourfold.canonicalNamedThinkerAxisWeld
    PS.canonicalFourfoldRetreatCrossPollinationWeld
    Kimmerer.canonicalKimmererBraidingAcknowledgement
    TwoEyed.canonicalKimmererTwoEyedSeeingBoundary
    MaboAudit.dawsonHingeAudit
    true true true true true true true true true true
