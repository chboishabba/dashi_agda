module DASHI.Governance.EpistemicAttractorCore where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.DevelopmentalInfluenceSourceAtlas as Sources

------------------------------------------------------------------------
-- Epistemic attractor / radicalisation grammar.
--
-- This is a structural carrier only.  It does not classify any named group,
-- religion, political tendency, movement or person as conspiratorial or
-- extremist.  Such promotion requires external, case-specific evidence.
------------------------------------------------------------------------

record TrustUpdateSystem : Set₁ where
  field
    Informant : Set
    Domain : Set
    Trust : Set
    Evidence : Set
    update : Informant → Domain → Trust → Evidence → Trust

open TrustUpdateSystem public

record EvidenceReframingSystem
  (S : TrustUpdateSystem) : Set₁ where
  field
    reframe : Evidence S → Evidence S
    Contrary : Evidence S → Set
    Supportive : Evidence S → Set

record DisconfirmationInversion
  (S : TrustUpdateSystem)
  (R : EvidenceReframingSystem S)
  : Set₁ where
  field
    contraryEvidence : Evidence S
    isContrary : EvidenceReframingSystem.Contrary R contraryEvidence
    reframedAsSupport :
      EvidenceReframingSystem.Supportive R
        (EvidenceReframingSystem.reframe R contraryEvidence)

record SelfSealingUpdate
  (S : TrustUpdateSystem)
  (R : EvidenceReframingSystem S)
  : Set₁ where
  field
    informant : Informant S
    domain : Domain S
    trust : Trust S
    inversion : DisconfirmationInversion S R
    updateAfterReframing : Trust S
    updateEquation :
      update S informant domain trust
        (EvidenceReframingSystem.reframe R
          (DisconfirmationInversion.contraryEvidence inversion))
      ≡ updateAfterReframing

------------------------------------------------------------------------
-- Persuasion sequence: a reusable graph of possible transitions rather than a
-- theorem that all people traverse a single pipeline.
------------------------------------------------------------------------

data PersuasionStage : Set where
  legitimateAnxiety : PersuasionStage
  institutionalBetrayal : PersuasionStage
  authorityDestabilisation : PersuasionStage
  replacementAuthority : PersuasionStage
  identityRecode : PersuasionStage
  communityFormation : PersuasionStage
  adjacentGrievanceLinking : PersuasionStage
  enemyReification : PersuasionStage
  disconfirmationCapture : PersuasionStage
  causalTotalisation : PersuasionStage
  worldviewEscalation : PersuasionStage

canonicalPersuasionStages : List PersuasionStage
canonicalPersuasionStages =
  legitimateAnxiety
  ∷ institutionalBetrayal
  ∷ authorityDestabilisation
  ∷ replacementAuthority
  ∷ identityRecode
  ∷ communityFormation
  ∷ adjacentGrievanceLinking
  ∷ enemyReification
  ∷ disconfirmationCapture
  ∷ causalTotalisation
  ∷ worldviewEscalation
  ∷ []

record PipelineGraph : Set₁ where
  field
    Node : Set
    Edge : Node → Node → Set
    BridgeNode : Node → Set
    nextExposure : Node → Node → Set

------------------------------------------------------------------------
-- Enemy reification and causal totalisation.
------------------------------------------------------------------------

record EnemyReificationSystem : Set₁ where
  field
    Actor : Set
    Event : Set
    ReifiedEnemy : Set
    participates : Actor → Event → Set
    compress : List Actor → ReifiedEnemy
    explains : ReifiedEnemy → Event → Set

record CausalTotalisation
  (S : EnemyReificationSystem) : Set₁ where
  field
    enemy : ReifiedEnemy S
    eventOne : Event S
    eventTwo : Event S
    explanationOne : explains S enemy eventOne
    explanationTwo : explains S enemy eventTwo

------------------------------------------------------------------------
-- Structural inquiry vs low-resolution totalisation.
------------------------------------------------------------------------

record CausalInquirySystem : Set₁ where
  field
    Node : Set
    Edge : Set
    Evidence : Set
    namesSource : Edge → Node
    namesTarget : Edge → Node
    supportsEdge : Evidence → Edge → Set
    revisesEdge : Evidence → Edge → Edge

record StructuralInquiry
  (S : CausalInquirySystem) : Set₁ where
  field
    edge : CausalInquirySystem.Edge S
    evidence : CausalInquirySystem.Evidence S
    edgeInspectable : CausalInquirySystem.supportsEdge S evidence edge
    revisionPermitted : Set

record CausalResolutionBoundary : Set where
  constructor causalResolutionBoundary
  field
    criticismOfInstitutionEqualsConspiracy : Bool
    distributedActorsEqualSingleHiddenAgent : Bool
    politicalSimilarityEqualsCommonCommand : Bool
    contraryEvidenceMayBeReframedWithoutReceipt : Bool
    structuralClaimsRequireInspectableEdges : Bool
    claimsMustRemainRevisable : Bool

canonicalCausalResolutionBoundary : CausalResolutionBoundary
canonicalCausalResolutionBoundary =
  causalResolutionBoundary false false false false true true

------------------------------------------------------------------------
-- Identity words such as "awake", "woke", "natural", "traditional", etc.
-- are not assigned an ideology by this core.  Identity salience and epistemic
-- closure are separate axes.
------------------------------------------------------------------------

record IdentityEpistemicSeparation : Set where
  constructor identityEpistemicSeparation
  field
    identitySalienceImpliesClosure : Bool
    criticalConsciousnessRequiresRevisability : Bool
    conspiratorialClosureRequiresNamedIdeology : Bool

canonicalIdentityEpistemicSeparation : IdentityEpistemicSeparation
canonicalIdentityEpistemicSeparation =
  identityEpistemicSeparation false true false

record EpistemicAttractorReceipt : Set where
  constructor epistemicAttractorReceipt
  field
    label : String
    sources : List Sources.ScholarlySource
    stages : List PersuasionStage
    causalBoundary : CausalResolutionBoundary
    identityBoundary : IdentityEpistemicSeparation
    noNamedGroupClassifiedByCarrier : Bool

canonicalEpistemicAttractorReceipt : EpistemicAttractorReceipt
canonicalEpistemicAttractorReceipt =
  epistemicAttractorReceipt
    "epistemic attractor and causal-resolution boundary"
    (Sources.epistemicTrustReview
      ∷ Sources.conspiritualitySource
      ∷ Sources.nationalSmokersAllianceSource
      ∷ [])
    canonicalPersuasionStages
    canonicalCausalResolutionBoundary
    canonicalIdentityEpistemicSeparation
    true
