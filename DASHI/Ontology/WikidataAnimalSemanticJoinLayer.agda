module DASHI.Ontology.WikidataAnimalSemanticJoinLayer where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Biology.AnimalexicAnimalUtteranceSurface
open import DASHI.Biology.CrossSpeciesOntologyTranslationBridge as CrossSpecies
import DASHI.Core.AuthorityNonPromotionCore as AuthorityCore
import DASHI.Core.BridgeRequirementCore as BridgeCore
import DASHI.Core.CandidateOnlyCore as CandidateCore
import DASHI.Core.EmptyPromotionCore as EmptyPromotion
import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Public ontology vocabulary for Animalexic-style review joins.
------------------------------------------------------------------------

data PublicOntologySource : Set where
  wikidataSource : PublicOntologySource
  wikipediaSource : PublicOntologySource
  wikiSpeciesSource : PublicOntologySource
  ethologySource : PublicOntologySource
  anatomySource : PublicOntologySource
  sensoryBiologySource : PublicOntologySource
  habitatSource : PublicOntologySource

data SemanticFacet : Set where
  taxonFacet : SemanticFacet
  speciesDescriptionFacet : SemanticFacet
  ethologyFacet : SemanticFacet
  anatomyFacet : SemanticFacet
  sensoryBiologyFacet : SemanticFacet
  habitatFacet : SemanticFacet
  vocalizationFacet : SemanticFacet
  postureFacet : SemanticFacet
  socialBehaviourFacet : SemanticFacet

data JoinDisposition : Set where
  joinPromoted : JoinDisposition
  joinHeld : JoinDisposition
  joinContradictory : JoinDisposition
  joinUnsupported : JoinDisposition

data JoinResidualKind : Set where
  missingWikidataID : JoinResidualKind
  missingWikipediaDescription : JoinResidualKind
  missingEthologyReceipt : JoinResidualKind
  missingAnatomyReceipt : JoinResidualKind
  missingSensoryBiologyReceipt : JoinResidualKind
  missingHabitatReceipt : JoinResidualKind
  missingVocalizationReceipt : JoinResidualKind
  missingPostureReceipt : JoinResidualKind
  missingSocialBehaviourReceipt : JoinResidualKind
  ontologyContradiction : JoinResidualKind
  observationOntologyMismatch : JoinResidualKind
  anthropomorphicProjectionRisk : JoinResidualKind

data SemanticJoinBoundary : Set where
  reviewJoinLayerOnly : SemanticJoinBoundary
  noEditAuthority : SemanticJoinBoundary
  noTruthAuthority : SemanticJoinBoundary
  noBlindEdit : SemanticJoinBoundary
  noContextFreeTranslation : SemanticJoinBoundary
  noQualiaIdentity : SemanticJoinBoundary
  noAnthropomorphicPromotion : SemanticJoinBoundary
  noPublicOntologyAsCompleteMeaningSpace : SemanticJoinBoundary

canonicalSemanticJoinBoundaries : List SemanticJoinBoundary
canonicalSemanticJoinBoundaries =
  reviewJoinLayerOnly
  ∷ noEditAuthority
  ∷ noTruthAuthority
  ∷ noBlindEdit
  ∷ noContextFreeTranslation
  ∷ noQualiaIdentity
  ∷ noAnthropomorphicPromotion
  ∷ noPublicOntologyAsCompleteMeaningSpace
  ∷ []

------------------------------------------------------------------------
-- Public ontology packet.
------------------------------------------------------------------------

record PublicAnimalOntologyPacket : Set₁ where
  field
    WikidataID : Set
    WikipediaPage : Set
    SpeciesDescription : Set
    EthologyNote : Set
    AnatomyNote : Set
    SensoryBiologyNote : Set
    HabitatNote : Set
    VocalizationNote : Set
    PostureNote : Set
    SocialBehaviourNote : Set
    SourceReceipt : Set

    wikidataID : WikidataID
    wikipediaPage : WikipediaPage
    speciesDescription : SpeciesDescription
    ethology : EthologyNote
    anatomy : AnatomyNote
    sensoryBiology : SensoryBiologyNote
    habitat : HabitatNote
    vocalization : VocalizationNote
    posture : PostureNote
    socialBehaviour : SocialBehaviourNote

    sourceReceiptFor :
      PublicOntologySource →
      SourceReceipt

    facetReceiptFor :
      SemanticFacet →
      SourceReceipt

    sourceReceiptAdmissible :
      SourceReceipt →
      Set

    packetReading : String

open PublicAnimalOntologyPacket public

record SituatedAnimalObservationJoin
    (animalexic : AnimalexicAnimalUtteranceSurface)
    (packet : PublicAnimalOntologyPacket) : Set₁ where
  field
    ObservationPacket : Set
    LatentBehaviourPredicate : Set
    CandidateMeaning : Set
    ReviewReceipt : Set
    JoinResidual : Set

    animalexicObservation :
      ObservationPacket →
      ObservationTrace animalexic

    latentPredicate :
      ObservationPacket →
      LatentBehaviourPredicate

    candidateMeaning :
      ObservationPacket →
      CandidateMeaning

    facetSupport :
      CandidateMeaning →
      SemanticFacet →
      Set

    residualFor :
      CandidateMeaning →
      JoinResidual

    residualKinds :
      JoinResidual →
      List JoinResidualKind

    disposition :
      CandidateMeaning →
      JoinDisposition

    reviewReceiptFor :
      CandidateMeaning →
      ReviewReceipt

    reviewReceiptAdmissible :
      ReviewReceipt →
      Set

    joinReading : String

open SituatedAnimalObservationJoin public

------------------------------------------------------------------------
-- Join layer over the existing CrossSpecies biology surface.
------------------------------------------------------------------------

record WikidataAnimalSemanticJoinLayer : Set₁ where
  field
    animalexicSurface :
      AnimalexicAnimalUtteranceSurface

    crossSpeciesBridge :
      CrossSpecies.CrossSpeciesOntologyTranslationBridge

    publicPacket :
      PublicAnimalOntologyPacket

    situatedJoin :
      SituatedAnimalObservationJoin animalexicSurface publicPacket

    publicSources :
      List PublicOntologySource

    reviewedFacets :
      List SemanticFacet

    defaultDisposition :
      JoinDisposition

    boundaries :
      List SemanticJoinBoundary

    reviewLayerOnly :
      Bool

    reviewLayerOnlyIsTrue :
      reviewLayerOnly ≡ true

    editAuthority :
      Bool

    editAuthorityIsFalse :
      editAuthority ≡ false

    truthAuthority :
      Bool

    truthAuthorityIsFalse :
      truthAuthority ≡ false

    blindEditAllowed :
      Bool

    blindEditAllowedIsFalse :
      blindEditAllowed ≡ false

    contextFreeTranslationAllowed :
      Bool

    contextFreeTranslationAllowedIsFalse :
      contextFreeTranslationAllowed ≡ false

    qualiaIdentityClaim :
      Bool

    qualiaIdentityClaimIsFalse :
      qualiaIdentityClaim ≡ false

    anthropomorphicPromotionAllowed :
      Bool

    anthropomorphicPromotionAllowedIsFalse :
      anthropomorphicPromotionAllowed ≡ false

    candidateOnlyCoreAdapter :
      CandidateCore.CandidateOnlyRow

    candidateOnlyCoreAdapterReceipt :
      CandidateCore.CandidateOnlyReceipt candidateOnlyCoreAdapter

    bridgeRequirementCoreAdapter :
      BridgeCore.BridgeRequirementCoreReceipt

    emptyPromotionCoreAdapter :
      EmptyPromotion.EmptyPromotionReceipt

    authorityNonPromotionCoreAdapter :
      AuthorityCore.AuthorityNonPromotionBundle

    genericNonPromotingReceipts :
      List GenericReceipt.GenericReceipt

    genericNonPromotingReceiptsAreNonPromoting :
      GenericReceipt.AllReceiptsNonPromoting genericNonPromotingReceipts

    layerReading :
      String

open WikidataAnimalSemanticJoinLayer public

record WikidataSemanticJoinNonAuthorityCertificate
    (layer : WikidataAnimalSemanticJoinLayer) : Set where
  field
    reviewOnly :
      reviewLayerOnly layer ≡ true

    editBlocked :
      editAuthority layer ≡ false

    truthBlocked :
      truthAuthority layer ≡ false

    blindEditBlocked :
      blindEditAllowed layer ≡ false

    contextFreeTranslationBlocked :
      contextFreeTranslationAllowed layer ≡ false

    qualiaIdentityBlocked :
      qualiaIdentityClaim layer ≡ false

    anthropomorphicPromotionBlocked :
      anthropomorphicPromotionAllowed layer ≡ false

    candidateOnlyCoreCandidateOnly :
      CandidateCore.candidateOnly (candidateOnlyCoreAdapter layer) ≡ true

    candidateOnlyCorePromotedFalse :
      CandidateCore.promoted (candidateOnlyCoreAdapter layer) ≡ false

    candidateOnlyCoreTruthAuthorityFalse :
      CandidateCore.carriesTruthAuthority (candidateOnlyCoreAdapter layer)
      ≡ false

    bridgeCoreAuthorityPromotionFalse :
      BridgeCore.receiptAuthorityPromotion (bridgeRequirementCoreAdapter layer)
      ≡ false

    bridgeCoreTransportMapAuthorityFalse :
      BridgeCore.receiptTransportMapAuthority
        (bridgeRequirementCoreAdapter layer)
      ≡ false

    bridgeCoreBackgroundBridgeAuthorityFalse :
      BridgeCore.receiptBackgroundBridgeAuthority
        (bridgeRequirementCoreAdapter layer)
      ≡ false

    emptyPromotionCorePromotionsEmpty :
      EmptyPromotion.promotions (emptyPromotionCoreAdapter layer) ≡ []

    authorityCoreTruthAuthorityFalse :
      AuthorityCore.truthAuthorityFlag (authorityNonPromotionCoreAdapter layer)
      ≡ false

    authorityCoreRuntimeAuthorityFalse :
      AuthorityCore.runtimeAuthorityFlag (authorityNonPromotionCoreAdapter layer)
      ≡ false

    authorityCorePromotesAnyAuthorityFalse :
      AuthorityCore.promotesAnyAuthority
        (authorityNonPromotionCoreAdapter layer)
      ≡ false

    certificateReading :
      String

open WikidataSemanticJoinNonAuthorityCertificate public

------------------------------------------------------------------------
-- Reusable core adapters.
--
-- These adapters are additive only: they route the local candidate-only,
-- bridge-false, authority-false, and empty-promotion readings through the
-- reusable fail-closed cores without changing the public ontology records.
------------------------------------------------------------------------

wikidataSemanticJoinCandidateOnlyCoreAdapter :
  CandidateCore.CandidateOnlyRow
wikidataSemanticJoinCandidateOnlyCoreAdapter =
  CandidateCore.mkCandidateOnlyRow
    "wikidata animal semantic join candidate-only adapter"
    "DASHI.Ontology.WikidataAnimalSemanticJoinLayer"
    "WikidataAnimalSemanticJoinLayer"
    CandidateCore.bridgeCandidateKind
    CandidateCore.bridgeCandidateOnlyStatus
    "Wikidata/Wikipedia animal semantics join Animalexic observations as review candidates only."
    "Edit authority, truth authority, context-free translation, and anthropomorphic promotion remain outside this join layer."

wikidataSemanticJoinCandidateOnlyCoreAdapterReceipt :
  CandidateCore.CandidateOnlyReceipt
    wikidataSemanticJoinCandidateOnlyCoreAdapter
wikidataSemanticJoinCandidateOnlyCoreAdapterReceipt =
  CandidateCore.canonicalCandidateOnlyReceipt
    wikidataSemanticJoinCandidateOnlyCoreAdapter
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

wikidataSemanticJoinBridgeRequirementCoreAdapter :
  BridgeCore.BridgeRequirementCoreReceipt
wikidataSemanticJoinBridgeRequirementCoreAdapter =
  BridgeCore.canonicalBridgeRequirementCoreReceipt

wikidataSemanticJoinEmptyPromotionCoreAdapter :
  EmptyPromotion.EmptyPromotionReceipt
wikidataSemanticJoinEmptyPromotionCoreAdapter =
  EmptyPromotion.canonicalEmptyPromotionReceipt

wikidataSemanticJoinAuthorityNonPromotionCoreAdapter :
  AuthorityCore.AuthorityNonPromotionBundle
wikidataSemanticJoinAuthorityNonPromotionCoreAdapter =
  AuthorityCore.mkClosedAuthorityNonPromotionBundle
    "wikidata animal semantic join authority non-promotion adapter"

wikidataSemanticJoinGenericNonPromotingReceipts :
  List GenericReceipt.GenericReceipt
wikidataSemanticJoinGenericNonPromotingReceipts =
  BridgeCore.bridgeRequirementRowGenericReceipt
    BridgeCore.suppliedCandidateOnlyBridgeRow
  ∷ BridgeCore.bridgeRequirementRowGenericReceipt
      BridgeCore.absentRequiredBridgeRow
  ∷ EmptyPromotion.canonicalEmptyPromotionGenericReceipt
  ∷ AuthorityCore.authorityNonPromotionGenericReceipt
      wikidataSemanticJoinAuthorityNonPromotionCoreAdapter
  ∷ []

wikidataSemanticJoinGenericNonPromotingReceiptsAreNonPromoting :
  GenericReceipt.AllReceiptsNonPromoting
    wikidataSemanticJoinGenericNonPromotingReceipts
wikidataSemanticJoinGenericNonPromotingReceiptsAreNonPromoting =
  GenericReceipt.proveAllReceiptsNonPromoting
    wikidataSemanticJoinGenericNonPromotingReceipts

wikidataSemanticJoinLayerCandidateOnlyCoreCandidateOnly :
  (layer : WikidataAnimalSemanticJoinLayer) →
  CandidateCore.candidateOnly (candidateOnlyCoreAdapter layer) ≡ true
wikidataSemanticJoinLayerCandidateOnlyCoreCandidateOnly layer =
  CandidateCore.candidateOnlyIsTrue
    (candidateOnlyCoreAdapterReceipt layer)

wikidataSemanticJoinLayerCandidateOnlyCorePromotedFalse :
  (layer : WikidataAnimalSemanticJoinLayer) →
  CandidateCore.promoted (candidateOnlyCoreAdapter layer) ≡ false
wikidataSemanticJoinLayerCandidateOnlyCorePromotedFalse layer =
  CandidateCore.candidatePromotedIsFalse
    (candidateOnlyCoreAdapterReceipt layer)

wikidataSemanticJoinLayerCandidateOnlyCoreTruthAuthorityFalse :
  (layer : WikidataAnimalSemanticJoinLayer) →
  CandidateCore.carriesTruthAuthority (candidateOnlyCoreAdapter layer)
  ≡ false
wikidataSemanticJoinLayerCandidateOnlyCoreTruthAuthorityFalse layer =
  CandidateCore.candidateNoTruthAuthority
    (candidateOnlyCoreAdapterReceipt layer)

wikidataSemanticJoinLayerBridgeCoreAuthorityPromotionFalse :
  (layer : WikidataAnimalSemanticJoinLayer) →
  BridgeCore.receiptAuthorityPromotion (bridgeRequirementCoreAdapter layer)
  ≡ false
wikidataSemanticJoinLayerBridgeCoreAuthorityPromotionFalse layer =
  BridgeCore.receiptAuthorityPromotionFalse
    (bridgeRequirementCoreAdapter layer)

wikidataSemanticJoinLayerBridgeCoreTransportMapAuthorityFalse :
  (layer : WikidataAnimalSemanticJoinLayer) →
  BridgeCore.receiptTransportMapAuthority (bridgeRequirementCoreAdapter layer)
  ≡ false
wikidataSemanticJoinLayerBridgeCoreTransportMapAuthorityFalse layer =
  BridgeCore.receiptTransportMapAuthorityFalse
    (bridgeRequirementCoreAdapter layer)

wikidataSemanticJoinLayerBridgeCoreBackgroundBridgeAuthorityFalse :
  (layer : WikidataAnimalSemanticJoinLayer) →
  BridgeCore.receiptBackgroundBridgeAuthority
    (bridgeRequirementCoreAdapter layer)
  ≡ false
wikidataSemanticJoinLayerBridgeCoreBackgroundBridgeAuthorityFalse layer =
  BridgeCore.receiptBackgroundBridgeAuthorityFalse
    (bridgeRequirementCoreAdapter layer)

wikidataSemanticJoinLayerEmptyPromotionCorePromotionsEmpty :
  (layer : WikidataAnimalSemanticJoinLayer) →
  EmptyPromotion.promotions (emptyPromotionCoreAdapter layer) ≡ []
wikidataSemanticJoinLayerEmptyPromotionCorePromotionsEmpty layer =
  EmptyPromotion.emptyPromotionReceiptPromotionsAreEmpty
    (emptyPromotionCoreAdapter layer)

wikidataSemanticJoinLayerAuthorityCoreTruthAuthorityFalse :
  (layer : WikidataAnimalSemanticJoinLayer) →
  AuthorityCore.truthAuthorityFlag (authorityNonPromotionCoreAdapter layer)
  ≡ false
wikidataSemanticJoinLayerAuthorityCoreTruthAuthorityFalse layer =
  AuthorityCore.bundleTruthAuthorityIsFalse
    (authorityNonPromotionCoreAdapter layer)

wikidataSemanticJoinLayerAuthorityCoreRuntimeAuthorityFalse :
  (layer : WikidataAnimalSemanticJoinLayer) →
  AuthorityCore.runtimeAuthorityFlag (authorityNonPromotionCoreAdapter layer)
  ≡ false
wikidataSemanticJoinLayerAuthorityCoreRuntimeAuthorityFalse layer =
  AuthorityCore.bundleRuntimeAuthorityIsFalse
    (authorityNonPromotionCoreAdapter layer)

wikidataSemanticJoinLayerAuthorityCorePromotesAnyAuthorityFalse :
  (layer : WikidataAnimalSemanticJoinLayer) →
  AuthorityCore.promotesAnyAuthority (authorityNonPromotionCoreAdapter layer)
  ≡ false
wikidataSemanticJoinLayerAuthorityCorePromotesAnyAuthorityFalse layer =
  AuthorityCore.bundlePromotesAnyAuthorityIsFalse
    (authorityNonPromotionCoreAdapter layer)

wikidataSemanticJoinLayerGenericReceiptsNonPromoting :
  (layer : WikidataAnimalSemanticJoinLayer) →
  GenericReceipt.AllReceiptsNonPromoting
    (genericNonPromotingReceipts layer)
wikidataSemanticJoinLayerGenericReceiptsNonPromoting layer =
  genericNonPromotingReceiptsAreNonPromoting layer

------------------------------------------------------------------------
-- Canonical toy inhabitants.
------------------------------------------------------------------------

data ToyAnimalOntologyToken : Set where
  toyDogObservation : ToyAnimalOntologyToken
  toyDogLatentPlayBow : ToyAnimalOntologyToken
  toyDogCandidateAffiliativePlay : ToyAnimalOntologyToken
  toyDogQID : ToyAnimalOntologyToken
  toyDogWikipediaPage : ToyAnimalOntologyToken
  toyDogSpeciesDescription : ToyAnimalOntologyToken
  toyDogEthology : ToyAnimalOntologyToken
  toyDogAnatomy : ToyAnimalOntologyToken
  toyDogSensoryBiology : ToyAnimalOntologyToken
  toyDogHabitat : ToyAnimalOntologyToken
  toyDogVocalization : ToyAnimalOntologyToken
  toyDogPosture : ToyAnimalOntologyToken
  toyDogSocialBehaviour : ToyAnimalOntologyToken
  toyDogSourceReceipt : ToyAnimalOntologyToken
  toyDogReviewReceipt : ToyAnimalOntologyToken
  toyDogJoinResidual : ToyAnimalOntologyToken
  toyDogTrace : ToyAnimalOntologyToken

canonicalPublicAnimalOntologyPacket :
  PublicAnimalOntologyPacket
canonicalPublicAnimalOntologyPacket =
  record
    { WikidataID = ToyAnimalOntologyToken
    ; WikipediaPage = ToyAnimalOntologyToken
    ; SpeciesDescription = ToyAnimalOntologyToken
    ; EthologyNote = ToyAnimalOntologyToken
    ; AnatomyNote = ToyAnimalOntologyToken
    ; SensoryBiologyNote = ToyAnimalOntologyToken
    ; HabitatNote = ToyAnimalOntologyToken
    ; VocalizationNote = ToyAnimalOntologyToken
    ; PostureNote = ToyAnimalOntologyToken
    ; SocialBehaviourNote = ToyAnimalOntologyToken
    ; SourceReceipt = ToyAnimalOntologyToken
    ; wikidataID = toyDogQID
    ; wikipediaPage = toyDogWikipediaPage
    ; speciesDescription = toyDogSpeciesDescription
    ; ethology = toyDogEthology
    ; anatomy = toyDogAnatomy
    ; sensoryBiology = toyDogSensoryBiology
    ; habitat = toyDogHabitat
    ; vocalization = toyDogVocalization
    ; posture = toyDogPosture
    ; socialBehaviour = toyDogSocialBehaviour
    ; sourceReceiptFor = λ _ → toyDogSourceReceipt
    ; facetReceiptFor = λ _ → toyDogSourceReceipt
    ; sourceReceiptAdmissible = λ _ → ⊤
    ; packetReading =
        "Toy dog packet: public ontology gives QID, description, and species knowledge facets for review only."
    }

canonicalSituatedAnimalObservationJoin :
  SituatedAnimalObservationJoin
    CrossSpecies.canonicalAnimalexicTranslationSurface
    canonicalPublicAnimalOntologyPacket
canonicalSituatedAnimalObservationJoin =
  record
    { ObservationPacket = ToyAnimalOntologyToken
    ; LatentBehaviourPredicate = ToyAnimalOntologyToken
    ; CandidateMeaning = ToyAnimalOntologyToken
    ; ReviewReceipt = ToyAnimalOntologyToken
    ; JoinResidual = ToyAnimalOntologyToken
    ; animalexicObservation = λ _ → tt
    ; latentPredicate = λ _ → toyDogLatentPlayBow
    ; candidateMeaning = λ _ → toyDogCandidateAffiliativePlay
    ; facetSupport = λ _ _ → ⊤
    ; residualFor = λ _ → toyDogJoinResidual
    ; residualKinds =
        λ _ →
          missingPostureReceipt
          ∷ anthropomorphicProjectionRisk
          ∷ []
    ; disposition = λ _ → joinHeld
    ; reviewReceiptFor = λ _ → toyDogReviewReceipt
    ; reviewReceiptAdmissible = λ _ → ⊤
    ; joinReading =
        "Toy dog observation is held for review against posture, vocalization, social behaviour, and species-context facets."
    }

canonicalPublicOntologySources : List PublicOntologySource
canonicalPublicOntologySources =
  wikidataSource
  ∷ wikipediaSource
  ∷ wikiSpeciesSource
  ∷ ethologySource
  ∷ anatomySource
  ∷ sensoryBiologySource
  ∷ habitatSource
  ∷ []

canonicalAnimalSemanticFacets : List SemanticFacet
canonicalAnimalSemanticFacets =
  taxonFacet
  ∷ speciesDescriptionFacet
  ∷ ethologyFacet
  ∷ anatomyFacet
  ∷ sensoryBiologyFacet
  ∷ habitatFacet
  ∷ vocalizationFacet
  ∷ postureFacet
  ∷ socialBehaviourFacet
  ∷ []

canonicalWikidataAnimalSemanticJoinLayer :
  WikidataAnimalSemanticJoinLayer
canonicalWikidataAnimalSemanticJoinLayer =
  record
    { animalexicSurface =
        CrossSpecies.canonicalAnimalexicTranslationSurface
    ; crossSpeciesBridge =
        CrossSpecies.canonicalCrossSpeciesOntologyTranslationBridge
    ; publicPacket =
        canonicalPublicAnimalOntologyPacket
    ; situatedJoin =
        canonicalSituatedAnimalObservationJoin
    ; publicSources =
        canonicalPublicOntologySources
    ; reviewedFacets =
        canonicalAnimalSemanticFacets
    ; defaultDisposition =
        joinHeld
    ; boundaries =
        canonicalSemanticJoinBoundaries
    ; reviewLayerOnly =
        true
    ; reviewLayerOnlyIsTrue =
        refl
    ; editAuthority =
        false
    ; editAuthorityIsFalse =
        refl
    ; truthAuthority =
        false
    ; truthAuthorityIsFalse =
        refl
    ; blindEditAllowed =
        false
    ; blindEditAllowedIsFalse =
        refl
    ; contextFreeTranslationAllowed =
        false
    ; contextFreeTranslationAllowedIsFalse =
        refl
    ; qualiaIdentityClaim =
        false
    ; qualiaIdentityClaimIsFalse =
        refl
    ; anthropomorphicPromotionAllowed =
        false
    ; anthropomorphicPromotionAllowedIsFalse =
        refl
    ; candidateOnlyCoreAdapter =
        wikidataSemanticJoinCandidateOnlyCoreAdapter
    ; candidateOnlyCoreAdapterReceipt =
        wikidataSemanticJoinCandidateOnlyCoreAdapterReceipt
    ; bridgeRequirementCoreAdapter =
        wikidataSemanticJoinBridgeRequirementCoreAdapter
    ; emptyPromotionCoreAdapter =
        wikidataSemanticJoinEmptyPromotionCoreAdapter
    ; authorityNonPromotionCoreAdapter =
        wikidataSemanticJoinAuthorityNonPromotionCoreAdapter
    ; genericNonPromotingReceipts =
        wikidataSemanticJoinGenericNonPromotingReceipts
    ; genericNonPromotingReceiptsAreNonPromoting =
        wikidataSemanticJoinGenericNonPromotingReceiptsAreNonPromoting
    ; layerReading =
        "Wikidata/Wikipedia species knowledge joins Animalexic candidates as a bounded review layer; it can hold, promote-with-receipts, contradict, or mark unsupported, but it is not edit authority, truth authority, qualia identity, or context-free translation."
    }

canonicalWikidataSemanticJoinNonAuthorityCertificate :
  WikidataSemanticJoinNonAuthorityCertificate
    canonicalWikidataAnimalSemanticJoinLayer
canonicalWikidataSemanticJoinNonAuthorityCertificate =
  record
    { reviewOnly =
        refl
    ; editBlocked =
        refl
    ; truthBlocked =
        refl
    ; blindEditBlocked =
        refl
    ; contextFreeTranslationBlocked =
        refl
    ; qualiaIdentityBlocked =
        refl
    ; anthropomorphicPromotionBlocked =
        refl
    ; candidateOnlyCoreCandidateOnly =
        CandidateCore.candidateOnlyIsTrue
          wikidataSemanticJoinCandidateOnlyCoreAdapterReceipt
    ; candidateOnlyCorePromotedFalse =
        CandidateCore.candidatePromotedIsFalse
          wikidataSemanticJoinCandidateOnlyCoreAdapterReceipt
    ; candidateOnlyCoreTruthAuthorityFalse =
        CandidateCore.candidateNoTruthAuthority
          wikidataSemanticJoinCandidateOnlyCoreAdapterReceipt
    ; bridgeCoreAuthorityPromotionFalse =
        BridgeCore.receiptAuthorityPromotionFalse
          wikidataSemanticJoinBridgeRequirementCoreAdapter
    ; bridgeCoreTransportMapAuthorityFalse =
        BridgeCore.receiptTransportMapAuthorityFalse
          wikidataSemanticJoinBridgeRequirementCoreAdapter
    ; bridgeCoreBackgroundBridgeAuthorityFalse =
        BridgeCore.receiptBackgroundBridgeAuthorityFalse
          wikidataSemanticJoinBridgeRequirementCoreAdapter
    ; emptyPromotionCorePromotionsEmpty =
        EmptyPromotion.emptyPromotionReceiptPromotionsAreEmpty
          wikidataSemanticJoinEmptyPromotionCoreAdapter
    ; authorityCoreTruthAuthorityFalse =
        AuthorityCore.bundleTruthAuthorityIsFalse
          wikidataSemanticJoinAuthorityNonPromotionCoreAdapter
    ; authorityCoreRuntimeAuthorityFalse =
        AuthorityCore.bundleRuntimeAuthorityIsFalse
          wikidataSemanticJoinAuthorityNonPromotionCoreAdapter
    ; authorityCorePromotesAnyAuthorityFalse =
        AuthorityCore.bundlePromotesAnyAuthorityIsFalse
          wikidataSemanticJoinAuthorityNonPromotionCoreAdapter
    ; certificateReading =
        "The canonical toy layer is review-only and blocks blind edit, truth authority, edit authority, qualia identity, context-free translation, and anthropomorphic promotion."
    }
