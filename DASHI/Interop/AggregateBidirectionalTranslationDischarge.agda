module DASHI.Interop.AggregateBidirectionalTranslationDischarge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)

import DASHI.Computation.PersistentTransportMotifs as Motifs
import DASHI.Core.AuthorityNonPromotionCore as AuthorityCore
import DASHI.Core.BridgeRequirementCore as BridgeCore
import DASHI.Core.CandidateOnlyCore as CandidateCore
import DASHI.Core.EmptyPromotionCore as EmptyCore
import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Ontology.WikidataAnimalSemanticJoinLayer as WikiJoin

------------------------------------------------------------------------
-- Aggregate bidirectional ontology transport vocabulary.
--
-- DASHI permits bounded transport in both directions between domains.
-- The transport preserves residual/projection-defect accounting: an exact
-- isomorphism is admissible only when the bridge supplies a zero-epsilon
-- witness. Otherwise the bridge is analogy or partial translation.

data AggregateOntologyDomain : Set where
  humanOntology : AggregateOntologyDomain
  dogOntology : AggregateOntologyDomain
  octopusOntology : AggregateOntologyDomain
  alienOntology : AggregateOntologyDomain
  rendererOntology : AggregateOntologyDomain
  machineOntology : AggregateOntologyDomain

data TransportBridgeKind : Set where
  boundedAnalogyBridge : TransportBridgeKind
  partialTranslationBridge : TransportBridgeKind
  zeroDefectIsomorphismBridge : TransportBridgeKind
  dischargeOnlyBridge : TransportBridgeKind

data ProjectionDefectKind : Set where
  lexicalResidual : ProjectionDefectKind
  sensoryEmbodimentResidual : ProjectionDefectKind
  ecologicalContextResidual : ProjectionDefectKind
  alienUnknownResidual : ProjectionDefectKind
  rendererSamplingResidual : ProjectionDefectKind
  machineEncodingResidual : ProjectionDefectKind
  quotientLossResidual : ProjectionDefectKind

data AggregateTranslationGuard : Set where
  NoUniversalTranslatorClaim : AggregateTranslationGuard
  NoQualiaIdentityClaim : AggregateTranslationGuard
  NoZeroDefectClaimWithoutWitness : AggregateTranslationGuard
  NoRuntimeOptimizerClaim : AggregateTranslationGuard
  ResidualsRemainExplicit : AggregateTranslationGuard

canonicalAggregateTranslationGuards : List AggregateTranslationGuard
canonicalAggregateTranslationGuards =
  NoUniversalTranslatorClaim
  ∷ NoQualiaIdentityClaim
  ∷ NoZeroDefectClaimWithoutWitness
  ∷ NoRuntimeOptimizerClaim
  ∷ ResidualsRemainExplicit
  ∷ []

canonicalOntologyChain : List AggregateOntologyDomain
canonicalOntologyChain =
  humanOntology
  ∷ dogOntology
  ∷ octopusOntology
  ∷ alienOntology
  ∷ rendererOntology
  ∷ machineOntology
  ∷ []

------------------------------------------------------------------------
-- Bounded bidirectional bridge.

record OntologyTransportSurface : Set₁ where
  field
    sourceDomain : AggregateOntologyDomain
    targetDomain : AggregateOntologyDomain

    SourceCarrier : Set
    TargetCarrier : Set
    SourceQuotient : Set
    TargetQuotient : Set
    TransportResidual : Set
    ProjectionDefect : Set
    Epsilon : Set

    sourceObserve :
      SourceCarrier →
      SourceQuotient

    targetObserve :
      TargetCarrier →
      TargetQuotient

    forwardTransport :
      SourceQuotient →
      TargetQuotient

    backwardTransport :
      TargetQuotient →
      SourceQuotient

    forwardResidual :
      SourceQuotient →
      TargetQuotient →
      TransportResidual

    backwardResidual :
      TargetQuotient →
      SourceQuotient →
      TransportResidual

    defectOf :
      TransportResidual →
      ProjectionDefect

    defectKind :
      ProjectionDefect →
      ProjectionDefectKind

    epsilonOf :
      TransportResidual →
      Epsilon

    epsilonIsZero :
      Epsilon →
      Set

    forwardAdmissible :
      TransportResidual →
      Set

    backwardAdmissible :
      TransportResidual →
      Set

    exactIsomorphismOnlyAtZero :
      (r : TransportResidual) →
      epsilonIsZero (epsilonOf r) →
      Set

    partialTranslationWhenResidual :
      TransportResidual →
      Set

    bridgeKind :
      TransportBridgeKind

    bridgeReading :
      String

open OntologyTransportSurface public

record ZeroDefectIsomorphismWitness
    (surface : OntologyTransportSurface) : Set₁ where
  field
    residual :
      TransportResidual surface

    zeroEpsilon :
      epsilonIsZero surface (epsilonOf surface residual)

    exactWitness :
      exactIsomorphismOnlyAtZero surface residual zeroEpsilon

    witnessReading :
      String

open ZeroDefectIsomorphismWitness public

record PartialTranslationWitness
    (surface : OntologyTransportSurface) : Set₁ where
  field
    residual :
      TransportResidual surface

    defect :
      ProjectionDefect surface

    defectMatchesResidual :
      defectOf surface residual ≡ defect

    forwardGate :
      forwardAdmissible surface residual

    backwardGate :
      backwardAdmissible surface residual

    analogyWitness :
      partialTranslationWhenResidual surface residual

    witnessReading :
      String

open PartialTranslationWitness public

------------------------------------------------------------------------
-- Aggregate discharge across the canonical ontology chain.

record AggregateBidirectionalTranslationDischarge : Set₁ where
  field
    TransportPermit :
      AggregateOntologyDomain →
      AggregateOntologyDomain →
      Set

    permitIsBidirectional :
      (left right : AggregateOntologyDomain) →
      TransportPermit left right →
      TransportPermit right left

    domainChain :
      List AggregateOntologyDomain

    humanDog :
      OntologyTransportSurface

    dogOctopus :
      OntologyTransportSurface

    octopusAlien :
      OntologyTransportSurface

    alienRenderer :
      OntologyTransportSurface

    rendererMachine :
      OntologyTransportSurface

    machineMotifSurface :
      Motifs.PersistentTransportMotifSurface

    machineMotifCertificate :
      Motifs.MotifNonPromotionCertificate machineMotifSurface

    publicSemanticJoinLayer :
      WikiJoin.WikidataAnimalSemanticJoinLayer

    publicSemanticJoinCertificate :
      WikiJoin.WikidataSemanticJoinNonAuthorityCertificate
        publicSemanticJoinLayer

    guards :
      List AggregateTranslationGuard

    guardsAreCanonical :
      guards ≡ canonicalAggregateTranslationGuards

    universalTranslatorClaim :
      Bool

    universalTranslatorClaimIsFalse :
      universalTranslatorClaim ≡ false

    qualiaIdentityClaim :
      Bool

    qualiaIdentityClaimIsFalse :
      qualiaIdentityClaim ≡ false

    zeroDefectClaim :
      Bool

    zeroDefectClaimIsFalse :
      zeroDefectClaim ≡ false

    runtimeOptimizerClaim :
      Bool

    runtimeOptimizerClaimIsFalse :
      runtimeOptimizerClaim ≡ false

    residualsPreserved :
      Bool

    residualsPreservedIsTrue :
      residualsPreserved ≡ true

    dischargeReading :
      String

open AggregateBidirectionalTranslationDischarge public

record AggregateTranslationNonPromotionCertificate
    (discharge : AggregateBidirectionalTranslationDischarge) : Set where
  field
    universalTranslatorBlocked :
      universalTranslatorClaim discharge ≡ false

    qualiaIdentityBlocked :
      qualiaIdentityClaim discharge ≡ false

    zeroDefectBlockedUnlessWitnessed :
      zeroDefectClaim discharge ≡ false

    runtimeOptimizerBlocked :
      runtimeOptimizerClaim discharge ≡ false

    residualAccountingHeld :
      residualsPreserved discharge ≡ true

    certificateReading :
      String

open AggregateTranslationNonPromotionCertificate public

------------------------------------------------------------------------
-- Canonical proof-light toy inhabitants.

data ToyOntologyToken : Set where
  humanToken : ToyOntologyToken
  dogToken : ToyOntologyToken
  octopusToken : ToyOntologyToken
  alienToken : ToyOntologyToken
  rendererToken : ToyOntologyToken
  machineToken : ToyOntologyToken
  quotientToken : ToyOntologyToken
  residualToken : ToyOntologyToken
  defectToken : ToyOntologyToken

data ToyEpsilon : Set where
  epsilon0 : ToyEpsilon
  boundedEpsilon : ToyEpsilon

toyEpsilonIsZero : ToyEpsilon → Set
toyEpsilonIsZero epsilon0 = ⊤
toyEpsilonIsZero boundedEpsilon = ⊥

canonicalBoundedBridge :
  AggregateOntologyDomain →
  AggregateOntologyDomain →
  ProjectionDefectKind →
  String →
  OntologyTransportSurface
canonicalBoundedBridge source target defect-kind reading =
  record
    { sourceDomain =
        source
    ; targetDomain =
        target
    ; SourceCarrier =
        ToyOntologyToken
    ; TargetCarrier =
        ToyOntologyToken
    ; SourceQuotient =
        ToyOntologyToken
    ; TargetQuotient =
        ToyOntologyToken
    ; TransportResidual =
        ToyOntologyToken
    ; ProjectionDefect =
        ToyOntologyToken
    ; Epsilon =
        ToyEpsilon
    ; sourceObserve =
        λ _ → quotientToken
    ; targetObserve =
        λ _ → quotientToken
    ; forwardTransport =
        λ _ → quotientToken
    ; backwardTransport =
        λ _ → quotientToken
    ; forwardResidual =
        λ _ _ → residualToken
    ; backwardResidual =
        λ _ _ → residualToken
    ; defectOf =
        λ _ → defectToken
    ; defectKind =
        λ _ → defect-kind
    ; epsilonOf =
        λ _ → boundedEpsilon
    ; epsilonIsZero =
        toyEpsilonIsZero
    ; forwardAdmissible =
        λ _ → ⊤
    ; backwardAdmissible =
        λ _ → ⊤
    ; exactIsomorphismOnlyAtZero =
        λ _ _ → ⊤
    ; partialTranslationWhenResidual =
        λ _ → ⊤
    ; bridgeKind =
        boundedAnalogyBridge
    ; bridgeReading =
        reading
    }

canonicalHumanDogBridge : OntologyTransportSurface
canonicalHumanDogBridge =
  canonicalBoundedBridge
    humanOntology
    dogOntology
    ecologicalContextResidual
    "Human and dog ontology transport is bidirectional, bounded, and residual-bearing."

canonicalDogOctopusBridge : OntologyTransportSurface
canonicalDogOctopusBridge =
  canonicalBoundedBridge
    dogOntology
    octopusOntology
    sensoryEmbodimentResidual
    "Dog and octopus ontology transport keeps embodiment projection defects explicit."

canonicalOctopusAlienBridge : OntologyTransportSurface
canonicalOctopusAlienBridge =
  canonicalBoundedBridge
    octopusOntology
    alienOntology
    alienUnknownResidual
    "Octopus and alien ontology transport is analogy-only unless a zero-defect witness is supplied."

canonicalAlienRendererBridge : OntologyTransportSurface
canonicalAlienRendererBridge =
  canonicalBoundedBridge
    alienOntology
    rendererOntology
    rendererSamplingResidual
    "Alien and renderer ontology transport exposes sampling and model residuals."

canonicalRendererMachineBridge : OntologyTransportSurface
canonicalRendererMachineBridge =
  canonicalBoundedBridge
    rendererOntology
    machineOntology
    machineEncodingResidual
    "Renderer and machine ontology transport exposes encoding, codec, and execution residuals."

canonicalAggregateBidirectionalTranslationDischarge :
  AggregateBidirectionalTranslationDischarge
canonicalAggregateBidirectionalTranslationDischarge =
  record
    { TransportPermit =
        λ _ _ → ⊤
    ; permitIsBidirectional =
        λ _ _ _ → tt
    ; domainChain =
        canonicalOntologyChain
    ; humanDog =
        canonicalHumanDogBridge
    ; dogOctopus =
        canonicalDogOctopusBridge
    ; octopusAlien =
        canonicalOctopusAlienBridge
    ; alienRenderer =
        canonicalAlienRendererBridge
    ; rendererMachine =
        canonicalRendererMachineBridge
    ; machineMotifSurface =
        Motifs.canonicalPersistentTransportMotifSurface
    ; machineMotifCertificate =
        Motifs.canonicalMotifNonPromotionCertificate
    ; publicSemanticJoinLayer =
        WikiJoin.canonicalWikidataAnimalSemanticJoinLayer
    ; publicSemanticJoinCertificate =
        WikiJoin.canonicalWikidataSemanticJoinNonAuthorityCertificate
    ; guards =
        canonicalAggregateTranslationGuards
    ; guardsAreCanonical =
        refl
    ; universalTranslatorClaim =
        false
    ; universalTranslatorClaimIsFalse =
        refl
    ; qualiaIdentityClaim =
        false
    ; qualiaIdentityClaimIsFalse =
        refl
    ; zeroDefectClaim =
        false
    ; zeroDefectClaimIsFalse =
        refl
    ; runtimeOptimizerClaim =
        false
    ; runtimeOptimizerClaimIsFalse =
        refl
    ; residualsPreserved =
        true
    ; residualsPreservedIsTrue =
        refl
    ; dischargeReading =
        "DASHI permits bidirectional bounded ontology transport across human, animal, alien, renderer, and machine domains while preserving projection defects; exact isomorphism requires a zero-epsilon witness."
    }

canonicalAggregateTranslationNonPromotionCertificate :
  AggregateTranslationNonPromotionCertificate
    canonicalAggregateBidirectionalTranslationDischarge
canonicalAggregateTranslationNonPromotionCertificate =
  record
    { universalTranslatorBlocked =
        refl
    ; qualiaIdentityBlocked =
        refl
    ; zeroDefectBlockedUnlessWitnessed =
        refl
    ; runtimeOptimizerBlocked =
        refl
    ; residualAccountingHeld =
        refl
    ; certificateReading =
        "The aggregate bridge is transport-permissive but non-promoting: residuals are explicit and zero-defect is not asserted."
    }

------------------------------------------------------------------------
-- Reusable core adapters.
--
-- These adapters consume the shared non-promotion cores without replacing
-- the aggregate transport records, toy inhabitants, or bridge semantics.

bridgeRequirementCoreAdapter :
  BridgeCore.BridgeRequirementCoreReceipt
bridgeRequirementCoreAdapter =
  BridgeCore.canonicalBridgeRequirementCoreReceipt

bridgeRequirementCoreAdapterIsCanonical :
  bridgeRequirementCoreAdapter
  ≡
  BridgeCore.canonicalBridgeRequirementCoreReceipt
bridgeRequirementCoreAdapterIsCanonical =
  refl

bridgeRequirementCoreAdapterAuthorityPromotionFalse :
  BridgeCore.receiptAuthorityPromotion bridgeRequirementCoreAdapter
  ≡
  false
bridgeRequirementCoreAdapterAuthorityPromotionFalse =
  BridgeCore.receiptAuthorityPromotionFalse bridgeRequirementCoreAdapter

bridgeRequirementCoreAdapterTransportMapAuthorityFalse :
  BridgeCore.receiptTransportMapAuthority bridgeRequirementCoreAdapter
  ≡
  false
bridgeRequirementCoreAdapterTransportMapAuthorityFalse =
  BridgeCore.receiptTransportMapAuthorityFalse bridgeRequirementCoreAdapter

bridgeRequirementCoreAdapterBackgroundBridgeAuthorityFalse :
  BridgeCore.receiptBackgroundBridgeAuthority bridgeRequirementCoreAdapter
  ≡
  false
bridgeRequirementCoreAdapterBackgroundBridgeAuthorityFalse =
  BridgeCore.receiptBackgroundBridgeAuthorityFalse bridgeRequirementCoreAdapter

candidateOnlyCoreAdapter :
  CandidateCore.CandidateOnlyRow
candidateOnlyCoreAdapter =
  CandidateCore.mkCandidateOnlyRow
    "aggregate translation candidate-only adapter"
    "DASHI.Interop.AggregateBidirectionalTranslationDischarge"
    "candidateOnlyCoreAdapter"
    CandidateCore.bridgeCandidateKind
    CandidateCore.bridgeCandidateOnlyStatus
    "Aggregate translation bridges are candidate-only evidence unless a separate zero-defect witness is supplied."
    "Universal translation, runtime optimization, and authority promotion remain outside this aggregate adapter."

candidateOnlyCoreAdapterReceipt :
  CandidateCore.CandidateOnlyReceipt candidateOnlyCoreAdapter
candidateOnlyCoreAdapterReceipt =
  CandidateCore.canonicalCandidateOnlyReceipt
    candidateOnlyCoreAdapter
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

candidateOnlyCoreAdapterCandidateOnly :
  CandidateCore.candidateOnly candidateOnlyCoreAdapter
  ≡
  true
candidateOnlyCoreAdapterCandidateOnly =
  CandidateCore.candidateOnlyIsTrue candidateOnlyCoreAdapterReceipt

candidateOnlyCoreAdapterPromotedFalse :
  CandidateCore.promoted candidateOnlyCoreAdapter
  ≡
  false
candidateOnlyCoreAdapterPromotedFalse =
  CandidateCore.candidatePromotedIsFalse candidateOnlyCoreAdapterReceipt

candidateOnlyCoreAdapterRuntimeAuthorityFalse :
  CandidateCore.carriesRuntimeAuthority candidateOnlyCoreAdapter
  ≡
  false
candidateOnlyCoreAdapterRuntimeAuthorityFalse =
  CandidateCore.candidateNoRuntimeAuthority candidateOnlyCoreAdapterReceipt

authorityNonPromotionCoreAdapter :
  AuthorityCore.AuthorityNonPromotionBundle
authorityNonPromotionCoreAdapter =
  AuthorityCore.mkClosedAuthorityNonPromotionBundle
    "aggregate translation authority non-promotion adapter"

authorityNonPromotionCoreAdapterCanonicalKindsFalse :
  AuthorityCore.AllAuthorityKindsFalse
    authorityNonPromotionCoreAdapter
    AuthorityCore.canonicalAuthorityKinds
authorityNonPromotionCoreAdapterCanonicalKindsFalse =
  AuthorityCore.proveAllAuthorityKindsFalse
    authorityNonPromotionCoreAdapter
    AuthorityCore.canonicalAuthorityKinds

authorityNonPromotionCoreAdapterGenericReceipt :
  GenericReceipt.GenericReceipt
authorityNonPromotionCoreAdapterGenericReceipt =
  AuthorityCore.authorityNonPromotionGenericReceipt
    authorityNonPromotionCoreAdapter

authorityNonPromotionCoreAdapterRuntimeAuthorityFalse :
  AuthorityCore.runtimeAuthorityFlag authorityNonPromotionCoreAdapter
  ≡
  false
authorityNonPromotionCoreAdapterRuntimeAuthorityFalse =
  AuthorityCore.bundleRuntimeAuthorityIsFalse
    authorityNonPromotionCoreAdapter

authorityNonPromotionCoreAdapterExternalAuthorityFalse :
  AuthorityCore.externalAuthorityFlag authorityNonPromotionCoreAdapter
  ≡
  false
authorityNonPromotionCoreAdapterExternalAuthorityFalse =
  AuthorityCore.bundleExternalAuthorityIsFalse
    authorityNonPromotionCoreAdapter

authorityNonPromotionCoreAdapterPromotesAnyAuthorityFalse :
  AuthorityCore.promotesAnyAuthority authorityNonPromotionCoreAdapter
  ≡
  false
authorityNonPromotionCoreAdapterPromotesAnyAuthorityFalse =
  AuthorityCore.bundlePromotesAnyAuthorityIsFalse
    authorityNonPromotionCoreAdapter

emptyPromotionCoreAdapter :
  EmptyCore.EmptyPromotionBundle
emptyPromotionCoreAdapter =
  EmptyCore.canonicalEmptyPromotionBundle

emptyPromotionCoreAdapterIsCanonical :
  emptyPromotionCoreAdapter
  ≡
  EmptyCore.canonicalEmptyPromotionBundle
emptyPromotionCoreAdapterIsCanonical =
  refl

emptyPromotionCoreAdapterReceiptIsCanonical :
  EmptyCore.emptyPromotionReceipt emptyPromotionCoreAdapter
  ≡
  EmptyCore.canonicalEmptyPromotionReceipt
emptyPromotionCoreAdapterReceiptIsCanonical =
  EmptyCore.canonicalEmptyPromotionBundleReceiptIsCanonical

emptyPromotionCoreAdapterPromotionsAreEmpty :
  EmptyCore.promotions
    (EmptyCore.emptyPromotionReceipt emptyPromotionCoreAdapter)
  ≡
  []
emptyPromotionCoreAdapterPromotionsAreEmpty =
  EmptyCore.canonicalEmptyPromotionBundlePromotionsAreEmpty

emptyPromotionCoreAdapterPromotionImpossible :
  EmptyCore.EmptyPromotionToken →
  ⊥
emptyPromotionCoreAdapterPromotionImpossible =
  EmptyCore.canonicalEmptyPromotionBundlePromotionImpossible

aggregateAdapterUniversalTranslatorBlocked :
  universalTranslatorClaim canonicalAggregateBidirectionalTranslationDischarge
  ≡
  false
aggregateAdapterUniversalTranslatorBlocked =
  universalTranslatorClaimIsFalse
    canonicalAggregateBidirectionalTranslationDischarge

aggregateAdapterRuntimeOptimizerBlocked :
  runtimeOptimizerClaim canonicalAggregateBidirectionalTranslationDischarge
  ≡
  false
aggregateAdapterRuntimeOptimizerBlocked =
  runtimeOptimizerClaimIsFalse
    canonicalAggregateBidirectionalTranslationDischarge

canonicalHumanDogPartialTranslationWitness :
  PartialTranslationWitness canonicalHumanDogBridge
canonicalHumanDogPartialTranslationWitness =
  record
    { residual =
        residualToken
    ; defect =
        defectToken
    ; defectMatchesResidual =
        refl
    ; forwardGate =
        tt
    ; backwardGate =
        tt
    ; analogyWitness =
        tt
    ; witnessReading =
        "The canonical bridge discharges only a bounded partial translation witness."
    }
