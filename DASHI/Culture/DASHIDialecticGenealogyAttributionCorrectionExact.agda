module DASHI.Culture.DASHIDialecticGenealogyAttributionCorrectionExact where

------------------------------------------------------------------------
-- DASHI DIALECTIC GENEALOGY ATTRIBUTION CORRECTION
--
-- User-reported historical genealogy, recorded 2026-09-07:
--   * Philosophy Tube's Hegel video was an important interpretive input;
--   * discussion with friends contributed to the developing picture;
--   * spiral-development material and related visual intuitions contributed;
--   * nongin material contributed;
--   * popular Hegel memes / simplified cultural transmission contributed;
--   * these influences mixed with the already-recorded bottom-up DASHI stream.
--
-- This corrects the historical provenance only.  None of these inputs thereby
-- owns later DASHI formal theorems, and Philosophy Tube / memes are not promoted
-- to primary Hegel authority.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.DialecticOriginSourceAtlasExact as Origin

philosophyTubeHegelSource : Source.AttributedSource
philosophyTubeHegelSource =
  Source.mkNoDOISource
    "Philosophy Tube (Abigail Thorn)"
    "Intro to Hegel (& Progressive Politics)"
    "Philosophy Tube / YouTube"
    "2018-04-27"
    "https://www.youtube.com/watch?v=OgNt1C72B_4"
    (Source.namedSourceKind "public philosophy video")
    "user-reported historical influence on DASHI's developing dialectical picture; secondary/pedagogical interpretation of Hegel and Fanon, not primary Hegel authority"
    Source.publicAttribution

data GenealogyInput : Set where
  philosophyTubeHegelVideo
  friendDiscussion
  spiralDevelopmentMaterial
  nonginMaterial
  hegelMemeTransmission
  bottomUpDashiExploration
  laterFormalisation
  : GenealogyInput

data GenealogyAuthority : Set where
  userReportedHistoricalInfluence
  publicSecondaryInterpretation
  privateConversationInfluence
  culturalTransmissionInfluence
  primaryPhilosophicalAuthority
  formalTheoremOwner
  : GenealogyAuthority

authority : GenealogyInput → GenealogyAuthority
authority philosophyTubeHegelVideo = publicSecondaryInterpretation
authority friendDiscussion = privateConversationInfluence
authority spiralDevelopmentMaterial = userReportedHistoricalInfluence
authority nonginMaterial = userReportedHistoricalInfluence
authority hegelMemeTransmission = culturalTransmissionInfluence
authority bottomUpDashiExploration = userReportedHistoricalInfluence
authority laterFormalisation = formalTheoremOwner

record DASHIDialecticGenealogyCorrection : Set where
  constructor dashi-dialectic-genealogy-correction
  field
    inheritedOriginBoundary : Origin.DialecticOriginSourceAtlasBoundary
    philosophyTubeInfluenceRecorded : Bool
    friendDiscussionInfluenceRecorded : Bool
    spiralInfluenceRecorded : Bool
    nonginInfluenceRecorded : Bool
    hegelMemeInfluenceRecorded : Bool
    bottomUpExplorationRetained : Bool
    philosophyTubeIsPrimaryHegelAuthority : Bool
    privateFriendsReceivePublicAuthorship : Bool
    hegelMemesCountAsPrimaryHegelText : Bool
    laterFormalOwnerRetroactivelyBecomesHistoricalOrigin : Bool
    genealogyProvesFormalIdentityWithHegel : Bool

canonicalDASHIDialecticGenealogyCorrection : DASHIDialecticGenealogyCorrection
canonicalDASHIDialecticGenealogyCorrection =
  dashi-dialectic-genealogy-correction
    Origin.canonicalDialecticOriginSourceAtlasBoundary
    true true true true true true
    false false false false false

------------------------------------------------------------------------
-- Explicit non-promotions.
------------------------------------------------------------------------

data PhilosophyTubeEqualsHegelPrimaryText : Set where
data FriendDiscussionCreatesPublicAuthorship : Set where
data HegelMemeEqualsHegelPrimaryText : Set where
data HistoricalInfluenceOwnsLaterDASHITheorem : Set where
data MixedGenealogyMeansExactDerivationFromOneSource : Set where

philosophyTubeDoesNotEqualHegelPrimaryText :
  PhilosophyTubeEqualsHegelPrimaryText → ⊥
philosophyTubeDoesNotEqualHegelPrimaryText ()

friendDiscussionDoesNotCreatePublicAuthorship :
  FriendDiscussionCreatesPublicAuthorship → ⊥
friendDiscussionDoesNotCreatePublicAuthorship ()

hegelMemeDoesNotEqualHegelPrimaryText : HegelMemeEqualsHegelPrimaryText → ⊥
hegelMemeDoesNotEqualHegelPrimaryText ()

historicalInfluenceDoesNotOwnLaterDASHITheorem :
  HistoricalInfluenceOwnsLaterDASHITheorem → ⊥
historicalInfluenceDoesNotOwnLaterDASHITheorem ()

mixedGenealogyDoesNotMeanExactSingleSourceDerivation :
  MixedGenealogyMeansExactDerivationFromOneSource → ⊥
mixedGenealogyDoesNotMeanExactSingleSourceDerivation ()
