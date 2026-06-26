module DASHI.Biology.CrossSpeciesOntologyTranslationBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.AuthorityNonPromotionCore as AuthorityNA
import DASHI.Core.AdapterCanonicalityCore as AdapterCanon
import DASHI.Core.BridgeRequirementCore as BridgeReq
import DASHI.Core.CandidateOnlyCore as CandidateOnly

open import DASHI.Biology.AnimalexicAnimalUtteranceSurface

------------------------------------------------------------------------
-- Boundary and translation vocabulary.
------------------------------------------------------------------------

data TranslationLayer : Set where
  animalexicObservationLayer : TranslationLayer
  socialContextLayer : TranslationLayer
  ecologicalNicheLayer : TranslationLayer
  memoryTraceLayer : TranslationLayer
  wikiSpeciesTaxonLayer : TranslationLayer
  ontologyAlignmentLayer : TranslationLayer
  contextualTranslationLayer : TranslationLayer

data OntologyTranslationStatus : Set where
  receiptBoundAnalogyOnly : OntologyTranslationStatus
  localContextualAlignmentOnly : OntologyTranslationStatus
  diagnosticCrossSpeciesCandidate : OntologyTranslationStatus
  rejectedContextFreeDictionary : OntologyTranslationStatus

data TranslationResidualKind : Set where
  missingTaxonReceipt : TranslationResidualKind
  missingEcologicalContext : TranslationResidualKind
  missingSocialContext : TranslationResidualKind
  missingMemoryTrace : TranslationResidualKind
  ambiguousBehaviouralClass : TranslationResidualKind
  targetSpeciesProjectionRisk : TranslationResidualKind

data CrossSpeciesTranslationGuard : Set where
  NoQualiaIdentityClaim : CrossSpeciesTranslationGuard
  NoSpeciesIsomorphismClaim : CrossSpeciesTranslationGuard
  NoAnthropomorphicPromotionClaim : CrossSpeciesTranslationGuard
  NoContextFreeTranslationClaim : CrossSpeciesTranslationGuard

data OntologyAuthorityBoundary : Set where
  wikiSpeciesTaxonReferenceOnly : OntologyAuthorityBoundary
  localOntologyNodeOnly : OntologyAuthorityBoundary
  noGlobalSpeciesDictionary : OntologyAuthorityBoundary
  noTaxonomyImpliesBehaviourClaim : OntologyAuthorityBoundary
  noReceiptlessCrossSpeciesPromotion : OntologyAuthorityBoundary

------------------------------------------------------------------------
-- WikiSpecies-style taxon and context carrier.
------------------------------------------------------------------------

record WikiSpeciesContextCarrier : Set₁ where
  field
    Species : Set
    TaxonNode : Set
    EcologicalContext : Set
    SocialContext : Set
    MemoryTrace : Set
    OntologyNode : Set
    TaxonReceipt : Set
    ContextReceipt : Set

    taxonFor :
      Species →
      TaxonNode

    ecologicalContextFor :
      Species →
      EcologicalContext

    socialContextFor :
      Species →
      SocialContext

    memoryTraceFor :
      Species →
      MemoryTrace

    ontologyNodeFor :
      TaxonNode →
      OntologyNode

    taxonReceiptFor :
      TaxonNode →
      TaxonReceipt

    contextReceiptFor :
      Species →
      EcologicalContext →
      SocialContext →
      MemoryTrace →
      ContextReceipt

    taxonReceiptAdmissible :
      TaxonReceipt →
      Set

    contextReceiptAdmissible :
      ContextReceipt →
      Set

    carrierReading : String

open WikiSpeciesContextCarrier public

------------------------------------------------------------------------
-- Cross-species ontology translation surface.
------------------------------------------------------------------------

record CrossSpeciesOntologyTranslationSurface
    (animalexic : AnimalexicAnimalUtteranceSurface)
    (wiki : WikiSpeciesContextCarrier) : Set₁ where
  field
    TranslationCandidate : Set
    ContextualMeaning : Set
    TranslationReceipt : Set
    TranslationResidual : Set

    sourceSpecies :
      Species wiki

    targetSpecies :
      Species wiki

    sourceBehaviouralMeaning :
      BehaviouralMeaning animalexic

    sourceTaxon :
      TaxonNode wiki

    targetTaxon :
      TaxonNode wiki

    sourceEcology :
      EcologicalContext wiki

    targetEcology :
      EcologicalContext wiki

    sourceSocialContext :
      SocialContext wiki

    targetSocialContext :
      SocialContext wiki

    sourceMemoryTrace :
      MemoryTrace wiki

    targetMemoryTrace :
      MemoryTrace wiki

    sourceOntologyNode :
      OntologyNode wiki

    targetOntologyNode :
      OntologyNode wiki

    buildCandidate :
      BehaviouralMeaning animalexic →
      OntologyNode wiki →
      OntologyNode wiki →
      EcologicalContext wiki →
      SocialContext wiki →
      MemoryTrace wiki →
      TranslationCandidate

    contextualize :
      TranslationCandidate →
      ContextualMeaning

    residual :
      TranslationCandidate →
      TranslationResidual

    residualKinds :
      TranslationResidual →
      List TranslationResidualKind

    translationReceiptFor :
      TranslationCandidate →
      TranslationReceipt

    translationReceiptAdmissible :
      TranslationReceipt →
      Set

    status :
      OntologyTranslationStatus

    translationReading : String

open CrossSpeciesOntologyTranslationSurface public

------------------------------------------------------------------------
-- Bounded bridge and non-promotion certificate.
------------------------------------------------------------------------

record CrossSpeciesOntologyTranslationBridge : Set₁ where
  field
    animalexicSurface :
      AnimalexicAnimalUtteranceSurface

    wikiSpeciesCarrier :
      WikiSpeciesContextCarrier

    translationSurface :
      CrossSpeciesOntologyTranslationSurface
        animalexicSurface
        wikiSpeciesCarrier

    translationLayers :
      List TranslationLayer

    authorityBoundaries :
      List OntologyAuthorityBoundary

    guards :
      List CrossSpeciesTranslationGuard

    nonPromoting :
      Bool

    nonPromotingIsTrue :
      nonPromoting ≡ true

    qualiaIdentityClaim :
      Bool

    qualiaIdentityClaimIsFalse :
      qualiaIdentityClaim ≡ false

    speciesIsomorphismClaim :
      Bool

    speciesIsomorphismClaimIsFalse :
      speciesIsomorphismClaim ≡ false

    anthropomorphicPromotionClaim :
      Bool

    anthropomorphicPromotionClaimIsFalse :
      anthropomorphicPromotionClaim ≡ false

    contextFreeTranslationClaim :
      Bool

    contextFreeTranslationClaimIsFalse :
      contextFreeTranslationClaim ≡ false

    safeReading :
      String

open CrossSpeciesOntologyTranslationBridge public

record CrossSpeciesOntologyNonPromotionCertificate
    (bridge : CrossSpeciesOntologyTranslationBridge) : Set where
  field
    nonPromotionHeld :
      nonPromoting bridge ≡ true

    qualiaIdentityBlocked :
      qualiaIdentityClaim bridge ≡ false

    speciesIsomorphismBlocked :
      speciesIsomorphismClaim bridge ≡ false

    anthropomorphicPromotionBlocked :
      anthropomorphicPromotionClaim bridge ≡ false

    contextFreeTranslationBlocked :
      contextFreeTranslationClaim bridge ≡ false

    guardReading :
      String

open CrossSpeciesOntologyNonPromotionCertificate public

------------------------------------------------------------------------
-- Reusable non-authority core adapters.
--
-- These adapters are additive evidence only.  They route the local
-- candidate-only, authority-false, and bridge-false reading through the
-- reusable cores without changing the bridge fields, constructors, booleans,
-- or local false proofs above.

record CrossSpeciesOntologyTranslationCoreAdapters
    (bridge : CrossSpeciesOntologyTranslationBridge) : Set where
  field
    candidateOnlyCoreAdapter :
      CandidateOnly.CandidateOnlyReceipt
        CandidateOnly.canonicalBridgeCandidateOnlyRow

    candidateOnlyCoreAdapterCandidateTrue :
      CandidateOnly.candidateOnly
        CandidateOnly.canonicalBridgeCandidateOnlyRow
      ≡
      true

    candidateOnlyCoreAdapterPromotedFalse :
      CandidateOnly.promoted
        CandidateOnly.canonicalBridgeCandidateOnlyRow
      ≡
      false

    candidateOnlyCoreAdapterNoTruthAuthority :
      CandidateOnly.carriesTruthAuthority
        CandidateOnly.canonicalBridgeCandidateOnlyRow
      ≡
      false

    candidateOnlyCoreAdapterNoSupportAuthority :
      CandidateOnly.carriesSupportAuthority
        CandidateOnly.canonicalBridgeCandidateOnlyRow
      ≡
      false

    candidateOnlyCoreAdapterNoAdmissibilityAuthority :
      CandidateOnly.carriesAdmissibilityAuthority
        CandidateOnly.canonicalBridgeCandidateOnlyRow
      ≡
      false

    candidateOnlyAdapterCanonicality :
      AdapterCanon.AdapterCanonicalityReceipt
        (CandidateOnly.CandidateOnlyReceipt
          CandidateOnly.canonicalBridgeCandidateOnlyRow)
        CandidateOnly.canonicalBridgeCandidateOnlyReceipt

    candidateOnlyAdapterIsCanonical :
      AdapterCanon.adapter
        candidateOnlyAdapterCanonicality
      ≡
      CandidateOnly.canonicalBridgeCandidateOnlyReceipt

    candidateOnlyAdapterCanonicalityAuthorityFalse :
      AdapterCanon.adapterPromotesAuthority
        candidateOnlyAdapterCanonicality
      ≡
      false

    authorityNonPromotionCoreAdapter :
      AuthorityNA.AuthorityNonPromotionBundle

    authorityNonPromotionCoreAdapterTruthFalse :
      AuthorityNA.truthAuthorityFlag
        authorityNonPromotionCoreAdapter
      ≡
      false

    authorityNonPromotionCoreAdapterSupportFalse :
      AuthorityNA.supportAuthorityFlag
        authorityNonPromotionCoreAdapter
      ≡
      false

    authorityNonPromotionCoreAdapterAdmissibilityFalse :
      AuthorityNA.admissibilityAuthorityFlag
        authorityNonPromotionCoreAdapter
      ≡
      false

    authorityNonPromotionCoreAdapterScientificFalse :
      AuthorityNA.scientificAuthorityFlag
        authorityNonPromotionCoreAdapter
      ≡
      false

    authorityNonPromotionCoreAdapterExternalFalse :
      AuthorityNA.externalAuthorityFlag
        authorityNonPromotionCoreAdapter
      ≡
      false

    authorityNonPromotionCoreAdapterEmpiricalFalse :
      AuthorityNA.empiricalAuthorityFlag
        authorityNonPromotionCoreAdapter
      ≡
      false

    authorityNonPromotionCoreAdapterCulturalFalse :
      AuthorityNA.culturalAuthorityFlag
        authorityNonPromotionCoreAdapter
      ≡
      false

    authorityNonPromotionCoreAdapterPromotesFalse :
      AuthorityNA.promotesAnyAuthority
        authorityNonPromotionCoreAdapter
      ≡
      false

    authorityNonPromotionAdapterCanonicality :
      AdapterCanon.AdapterCanonicalityReceipt
        AuthorityNA.AuthorityNonPromotionBundle
        authorityNonPromotionCoreAdapter

    authorityNonPromotionAdapterIsCanonical :
      AdapterCanon.adapter
        authorityNonPromotionAdapterCanonicality
      ≡
      authorityNonPromotionCoreAdapter

    authorityNonPromotionAdapterCanonicalityAuthorityFalse :
      AdapterCanon.adapterPromotesAuthority
        authorityNonPromotionAdapterCanonicality
      ≡
      false

    bridgeRequirementCoreAdapter :
      BridgeReq.BridgeRequirementCoreReceipt

    bridgeRequirementCoreAdapterAuthorityPromotionFalse :
      BridgeReq.receiptAuthorityPromotion
        bridgeRequirementCoreAdapter
      ≡
      false

    bridgeRequirementCoreAdapterTransportMapAuthorityFalse :
      BridgeReq.receiptTransportMapAuthority
        bridgeRequirementCoreAdapter
      ≡
      false

    bridgeRequirementCoreAdapterBackgroundBridgeAuthorityFalse :
      BridgeReq.receiptBackgroundBridgeAuthority
        bridgeRequirementCoreAdapter
      ≡
      false

    bridgeRequirementAdapterCanonicality :
      AdapterCanon.AdapterCanonicalityReceipt
        BridgeReq.BridgeRequirementCoreReceipt
        BridgeReq.canonicalBridgeRequirementCoreReceipt

    bridgeRequirementAdapterIsCanonical :
      AdapterCanon.adapter
        bridgeRequirementAdapterCanonicality
      ≡
      BridgeReq.canonicalBridgeRequirementCoreReceipt

    bridgeRequirementAdapterCanonicalityAuthorityFalse :
      AdapterCanon.adapterPromotesAuthority
        bridgeRequirementAdapterCanonicality
      ≡
      false

    adapterReading :
      String

open CrossSpeciesOntologyTranslationCoreAdapters public

canonicalTranslationLayers : List TranslationLayer
canonicalTranslationLayers =
  animalexicObservationLayer
  ∷ socialContextLayer
  ∷ ecologicalNicheLayer
  ∷ memoryTraceLayer
  ∷ wikiSpeciesTaxonLayer
  ∷ ontologyAlignmentLayer
  ∷ contextualTranslationLayer
  ∷ []

canonicalCrossSpeciesTranslationGuards :
  List CrossSpeciesTranslationGuard
canonicalCrossSpeciesTranslationGuards =
  NoQualiaIdentityClaim
  ∷ NoSpeciesIsomorphismClaim
  ∷ NoAnthropomorphicPromotionClaim
  ∷ NoContextFreeTranslationClaim
  ∷ []

canonicalOntologyAuthorityBoundaries :
  List OntologyAuthorityBoundary
canonicalOntologyAuthorityBoundaries =
  wikiSpeciesTaxonReferenceOnly
  ∷ localOntologyNodeOnly
  ∷ noGlobalSpeciesDictionary
  ∷ noTaxonomyImpliesBehaviourClaim
  ∷ noReceiptlessCrossSpeciesPromotion
  ∷ []

------------------------------------------------------------------------
-- Canonical toy inhabitant.
------------------------------------------------------------------------

canonicalAnimalexicTranslationSurface :
  AnimalexicAnimalUtteranceSurface
canonicalAnimalexicTranslationSurface =
  record
    { Animal = ⊤
    ; Context = ⊤
    ; UtteranceEvent = ⊤
    ; ObservationTrace = ⊤
    ; BodyStateCandidate = ⊤
    ; SocialStateCandidate = ⊤
    ; LatentCandidate = ⊤
    ; BehaviouralMeaning = ⊤
    ; Receipt = ⊤
    ; ProvenanceNode = ⊤
    ; ObserverProtocol = ⊤
    ; observe = λ _ _ _ → tt
    ; observedModalities =
        λ _ →
          acousticTrace
          ∷ postureTrace
          ∷ socialTrace
          ∷ environmentTrace
          ∷ []
    ; candidateBodyState = λ _ → tt
    ; candidateSocialState = λ _ → tt
    ; candidateLatentState = λ _ _ _ → tt
    ; latentAspects =
        λ _ →
          affiliativeOrientation
          ∷ environmentalAttention
          ∷ []
    ; admissibilityReceipt = λ _ _ → tt
    ; provenanceTrail = λ _ → tt ∷ []
    ; observerProtocol = λ _ → tt
    ; promoteBehaviouralMeaning = λ _ _ _ → tt
    ; multimodalReceiptComplete = λ _ _ _ → ⊤
    ; provenanceAdmissible = λ _ → ⊤
    ; boundaryReading =
        noDirectQualiaClaim
        ∷ noSpeciesUniversalDictionary
        ∷ noHumanLanguageEquivalence
        ∷ noSingleChannelCertainty
        ∷ []
    }

canonicalWikiSpeciesContextCarrier :
  WikiSpeciesContextCarrier
canonicalWikiSpeciesContextCarrier =
  record
    { Species = ⊤
    ; TaxonNode = ⊤
    ; EcologicalContext = ⊤
    ; SocialContext = ⊤
    ; MemoryTrace = ⊤
    ; OntologyNode = ⊤
    ; TaxonReceipt = ⊤
    ; ContextReceipt = ⊤
    ; taxonFor = λ _ → tt
    ; ecologicalContextFor = λ _ → tt
    ; socialContextFor = λ _ → tt
    ; memoryTraceFor = λ _ → tt
    ; ontologyNodeFor = λ _ → tt
    ; taxonReceiptFor = λ _ → tt
    ; contextReceiptFor = λ _ _ _ _ → tt
    ; taxonReceiptAdmissible = λ _ → ⊤
    ; contextReceiptAdmissible = λ _ → ⊤
    ; carrierReading =
        "WikiSpecies-style taxonomy supplies receipted species context, not behavior semantics by itself."
    }

canonicalCrossSpeciesOntologyTranslationSurface :
  CrossSpeciesOntologyTranslationSurface
    canonicalAnimalexicTranslationSurface
    canonicalWikiSpeciesContextCarrier
canonicalCrossSpeciesOntologyTranslationSurface =
  record
    { TranslationCandidate = ⊤
    ; ContextualMeaning = ⊤
    ; TranslationReceipt = ⊤
    ; TranslationResidual = ⊤
    ; sourceSpecies = tt
    ; targetSpecies = tt
    ; sourceBehaviouralMeaning = tt
    ; sourceTaxon = tt
    ; targetTaxon = tt
    ; sourceEcology = tt
    ; targetEcology = tt
    ; sourceSocialContext = tt
    ; targetSocialContext = tt
    ; sourceMemoryTrace = tt
    ; targetMemoryTrace = tt
    ; sourceOntologyNode = tt
    ; targetOntologyNode = tt
    ; buildCandidate = λ _ _ _ _ _ _ → tt
    ; contextualize = λ _ → tt
    ; residual = λ _ → tt
    ; residualKinds =
        λ _ →
          targetSpeciesProjectionRisk
          ∷ ambiguousBehaviouralClass
          ∷ []
    ; translationReceiptFor = λ _ → tt
    ; translationReceiptAdmissible = λ _ → ⊤
    ; status = receiptBoundAnalogyOnly
    ; translationReading =
        "Cross-species translation is a receipted contextual analogy over taxon, ecology, social frame, and memory traces."
    }

canonicalCrossSpeciesOntologyTranslationBridge :
  CrossSpeciesOntologyTranslationBridge
canonicalCrossSpeciesOntologyTranslationBridge =
  record
    { animalexicSurface = canonicalAnimalexicTranslationSurface
    ; wikiSpeciesCarrier = canonicalWikiSpeciesContextCarrier
    ; translationSurface =
        canonicalCrossSpeciesOntologyTranslationSurface
    ; translationLayers = canonicalTranslationLayers
    ; authorityBoundaries = canonicalOntologyAuthorityBoundaries
    ; guards = canonicalCrossSpeciesTranslationGuards
    ; nonPromoting = true
    ; nonPromotingIsTrue = refl
    ; qualiaIdentityClaim = false
    ; qualiaIdentityClaimIsFalse = refl
    ; speciesIsomorphismClaim = false
    ; speciesIsomorphismClaimIsFalse = refl
    ; anthropomorphicPromotionClaim = false
    ; anthropomorphicPromotionClaimIsFalse = refl
    ; contextFreeTranslationClaim = false
    ; contextFreeTranslationClaimIsFalse = refl
    ; safeReading =
        "Animalexic/WikiSpecies translation narrows context-bound ontology classes without promoting qualia identity, species isomorphism, anthropomorphic projection, or context-free dictionaries."
    }

canonicalCrossSpeciesOntologyAuthorityNonPromotionBundle :
  AuthorityNA.AuthorityNonPromotionBundle
canonicalCrossSpeciesOntologyAuthorityNonPromotionBundle =
  AuthorityNA.mkClosedAuthorityNonPromotionBundle
    "cross-species ontology translation authority non-promotion bundle"

canonicalCrossSpeciesOntologyTranslationCoreAdapters :
  CrossSpeciesOntologyTranslationCoreAdapters
    canonicalCrossSpeciesOntologyTranslationBridge
canonicalCrossSpeciesOntologyTranslationCoreAdapters =
  record
    { candidateOnlyCoreAdapter =
        CandidateOnly.canonicalBridgeCandidateOnlyReceipt
    ; candidateOnlyCoreAdapterCandidateTrue =
        CandidateOnly.candidateOnlyIsTrue
          CandidateOnly.canonicalBridgeCandidateOnlyReceipt
    ; candidateOnlyCoreAdapterPromotedFalse =
        CandidateOnly.candidatePromotedIsFalse
          CandidateOnly.canonicalBridgeCandidateOnlyReceipt
    ; candidateOnlyCoreAdapterNoTruthAuthority =
        CandidateOnly.candidateNoTruthAuthority
          CandidateOnly.canonicalBridgeCandidateOnlyReceipt
    ; candidateOnlyCoreAdapterNoSupportAuthority =
        CandidateOnly.candidateNoSupportAuthority
          CandidateOnly.canonicalBridgeCandidateOnlyReceipt
    ; candidateOnlyCoreAdapterNoAdmissibilityAuthority =
        CandidateOnly.candidateNoAdmissibilityAuthority
          CandidateOnly.canonicalBridgeCandidateOnlyReceipt
    ; candidateOnlyAdapterCanonicality =
        AdapterCanon.mkCanonicalAdapterReceipt
          "cross-species candidate-only core adapter canonicality"
          "DASHI.Biology.CrossSpeciesOntologyTranslationBridge"
          "CandidateOnly.canonicalBridgeCandidateOnlyReceipt"
          AdapterCanon.receiptAdapterKind
          CandidateOnly.canonicalBridgeCandidateOnlyReceipt
    ; candidateOnlyAdapterIsCanonical =
        AdapterCanon.adapterCanonical
          (AdapterCanon.mkCanonicalAdapterReceipt
            "cross-species candidate-only core adapter canonicality"
            "DASHI.Biology.CrossSpeciesOntologyTranslationBridge"
            "CandidateOnly.canonicalBridgeCandidateOnlyReceipt"
            AdapterCanon.receiptAdapterKind
            CandidateOnly.canonicalBridgeCandidateOnlyReceipt)
    ; candidateOnlyAdapterCanonicalityAuthorityFalse =
        AdapterCanon.adapterAuthorityPromotionFalse
          (AdapterCanon.mkCanonicalAdapterReceipt
            "cross-species candidate-only core adapter canonicality"
            "DASHI.Biology.CrossSpeciesOntologyTranslationBridge"
            "CandidateOnly.canonicalBridgeCandidateOnlyReceipt"
            AdapterCanon.receiptAdapterKind
            CandidateOnly.canonicalBridgeCandidateOnlyReceipt)
    ; authorityNonPromotionCoreAdapter =
        canonicalCrossSpeciesOntologyAuthorityNonPromotionBundle
    ; authorityNonPromotionCoreAdapterTruthFalse =
        AuthorityNA.truthAuthorityFlagIsFalse
          canonicalCrossSpeciesOntologyAuthorityNonPromotionBundle
    ; authorityNonPromotionCoreAdapterSupportFalse =
        AuthorityNA.supportAuthorityFlagIsFalse
          canonicalCrossSpeciesOntologyAuthorityNonPromotionBundle
    ; authorityNonPromotionCoreAdapterAdmissibilityFalse =
        AuthorityNA.admissibilityAuthorityFlagIsFalse
          canonicalCrossSpeciesOntologyAuthorityNonPromotionBundle
    ; authorityNonPromotionCoreAdapterScientificFalse =
        AuthorityNA.scientificAuthorityFlagIsFalse
          canonicalCrossSpeciesOntologyAuthorityNonPromotionBundle
    ; authorityNonPromotionCoreAdapterExternalFalse =
        AuthorityNA.externalAuthorityFlagIsFalse
          canonicalCrossSpeciesOntologyAuthorityNonPromotionBundle
    ; authorityNonPromotionCoreAdapterEmpiricalFalse =
        AuthorityNA.empiricalAuthorityFlagIsFalse
          canonicalCrossSpeciesOntologyAuthorityNonPromotionBundle
    ; authorityNonPromotionCoreAdapterCulturalFalse =
        AuthorityNA.culturalAuthorityFlagIsFalse
          canonicalCrossSpeciesOntologyAuthorityNonPromotionBundle
    ; authorityNonPromotionCoreAdapterPromotesFalse =
        AuthorityNA.promotesAnyAuthorityIsFalse
          canonicalCrossSpeciesOntologyAuthorityNonPromotionBundle
    ; authorityNonPromotionAdapterCanonicality =
        AdapterCanon.mkCanonicalAdapterReceipt
          "cross-species authority non-promotion adapter canonicality"
          "DASHI.Biology.CrossSpeciesOntologyTranslationBridge"
          "canonicalCrossSpeciesOntologyAuthorityNonPromotionBundle"
          AdapterCanon.authorityAdapterKind
          canonicalCrossSpeciesOntologyAuthorityNonPromotionBundle
    ; authorityNonPromotionAdapterIsCanonical =
        AdapterCanon.adapterCanonical
          (AdapterCanon.mkCanonicalAdapterReceipt
            "cross-species authority non-promotion adapter canonicality"
            "DASHI.Biology.CrossSpeciesOntologyTranslationBridge"
            "canonicalCrossSpeciesOntologyAuthorityNonPromotionBundle"
            AdapterCanon.authorityAdapterKind
            canonicalCrossSpeciesOntologyAuthorityNonPromotionBundle)
    ; authorityNonPromotionAdapterCanonicalityAuthorityFalse =
        AdapterCanon.adapterAuthorityPromotionFalse
          (AdapterCanon.mkCanonicalAdapterReceipt
            "cross-species authority non-promotion adapter canonicality"
            "DASHI.Biology.CrossSpeciesOntologyTranslationBridge"
            "canonicalCrossSpeciesOntologyAuthorityNonPromotionBundle"
            AdapterCanon.authorityAdapterKind
            canonicalCrossSpeciesOntologyAuthorityNonPromotionBundle)
    ; bridgeRequirementCoreAdapter =
        BridgeReq.canonicalBridgeRequirementCoreReceipt
    ; bridgeRequirementCoreAdapterAuthorityPromotionFalse =
        BridgeReq.receiptAuthorityPromotionFalse
          BridgeReq.canonicalBridgeRequirementCoreReceipt
    ; bridgeRequirementCoreAdapterTransportMapAuthorityFalse =
        BridgeReq.receiptTransportMapAuthorityFalse
          BridgeReq.canonicalBridgeRequirementCoreReceipt
    ; bridgeRequirementCoreAdapterBackgroundBridgeAuthorityFalse =
        BridgeReq.receiptBackgroundBridgeAuthorityFalse
          BridgeReq.canonicalBridgeRequirementCoreReceipt
    ; bridgeRequirementAdapterCanonicality =
        AdapterCanon.mkCanonicalAdapterReceipt
          "cross-species bridge requirement adapter canonicality"
          "DASHI.Biology.CrossSpeciesOntologyTranslationBridge"
          "BridgeReq.canonicalBridgeRequirementCoreReceipt"
          AdapterCanon.bridgeAdapterKind
          BridgeReq.canonicalBridgeRequirementCoreReceipt
    ; bridgeRequirementAdapterIsCanonical =
        AdapterCanon.adapterCanonical
          (AdapterCanon.mkCanonicalAdapterReceipt
            "cross-species bridge requirement adapter canonicality"
            "DASHI.Biology.CrossSpeciesOntologyTranslationBridge"
            "BridgeReq.canonicalBridgeRequirementCoreReceipt"
            AdapterCanon.bridgeAdapterKind
            BridgeReq.canonicalBridgeRequirementCoreReceipt)
    ; bridgeRequirementAdapterCanonicalityAuthorityFalse =
        AdapterCanon.adapterAuthorityPromotionFalse
          (AdapterCanon.mkCanonicalAdapterReceipt
            "cross-species bridge requirement adapter canonicality"
            "DASHI.Biology.CrossSpeciesOntologyTranslationBridge"
            "BridgeReq.canonicalBridgeRequirementCoreReceipt"
            AdapterCanon.bridgeAdapterKind
            BridgeReq.canonicalBridgeRequirementCoreReceipt)
    ; adapterReading =
        "Reusable core adapters witness candidate-only translation, closed authority flags, and fail-closed bridge authority without changing local cross-species non-promotion proofs."
    }

canonicalCrossSpeciesOntologyNonPromotionCertificate :
  CrossSpeciesOntologyNonPromotionCertificate
    canonicalCrossSpeciesOntologyTranslationBridge
canonicalCrossSpeciesOntologyNonPromotionCertificate =
  record
    { nonPromotionHeld = refl
    ; qualiaIdentityBlocked = refl
    ; speciesIsomorphismBlocked = refl
    ; anthropomorphicPromotionBlocked = refl
    ; contextFreeTranslationBlocked = refl
    ; guardReading =
        "The four requested non-promotion guards are present and block promotion beyond receipt-bound contextual translation."
    }
