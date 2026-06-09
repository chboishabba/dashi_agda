module DASHI.Ontology.WikidataAnimalSemanticJoinLayer where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Biology.AnimalexicAnimalUtteranceSurface
open import DASHI.Biology.CrossSpeciesOntologyTranslationBridge as CrossSpecies

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

    certificateReading :
      String

open WikidataSemanticJoinNonAuthorityCertificate public

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
    ; certificateReading =
        "The canonical toy layer is review-only and blocks blind edit, truth authority, edit authority, qualia identity, context-free translation, and anthropomorphic promotion."
    }
