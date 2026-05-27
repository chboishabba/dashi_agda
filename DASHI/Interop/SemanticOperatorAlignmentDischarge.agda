module DASHI.Interop.SemanticOperatorAlignmentDischarge where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.OperatorInvariantEquivalence as Operator
import DASHI.Reasoning.MetaphorAlignmentMisunderstanding as Metaphor
import DASHI.Interop.ObservationTransportSpine as Spine

------------------------------------------------------------------------
-- Aggregate discharge for the semantic/operator-alignment thread tail.
--
-- The new tail links:
--
--   cross-domain operator/topology equivalence under explicit invariants
--     -> metaphor / simile alignment as partial operator preservation
--     -> succinct communication as MDL-style invariant preservation
--     -> interpersonal misunderstanding as failed observer-quotient alignment
--
-- This module only records that typed join.  It does not promote exact
-- universal translation, global ontology, substance identity, qualia recovery,
-- or guaranteed perfect understanding.

data SemanticOperatorAlignmentLane : Set where
  operatorInvariantEquivalenceLane : SemanticOperatorAlignmentLane
  metaphorAlignmentLane : SemanticOperatorAlignmentLane
  succinctCommunicationLane : SemanticOperatorAlignmentLane
  misunderstandingQuotientLane : SemanticOperatorAlignmentLane

canonicalSemanticOperatorAlignmentLanes :
  List SemanticOperatorAlignmentLane
canonicalSemanticOperatorAlignmentLanes =
  operatorInvariantEquivalenceLane
  ∷ metaphorAlignmentLane
  ∷ succinctCommunicationLane
  ∷ misunderstandingQuotientLane
  ∷ []

canonicalSemanticOperatorSpineDomains :
  List Spine.ObservationDomain
canonicalSemanticOperatorSpineDomains =
  Spine.operatorInvariantEquivalenceDomain
  ∷ Spine.metaphorAlignmentDomain
  ∷ Spine.succinctCommunicationDomain
  ∷ Spine.misunderstandingQuotientDomain
  ∷ Spine.semanticOperatorAlignmentAggregateDomain
  ∷ []

data OperatorObservationCarrier : Set where
  debateRedoxPartialCarrier : OperatorObservationCarrier
  debateRedoxExactReceiptCarrier : OperatorObservationCarrier

data CommunicationObservationCarrier : Set where
  metaphorAlignmentCarrier : CommunicationObservationCarrier
  succinctCommunicationCarrier : CommunicationObservationCarrier
  misunderstandingCarrier : CommunicationObservationCarrier

operatorCarrierStrength :
  OperatorObservationCarrier →
  Operator.EquivalenceStrength
operatorCarrierStrength debateRedoxPartialCarrier =
  Operator.partialEquivalence
operatorCarrierStrength debateRedoxExactReceiptCarrier =
  Operator.exactEquivalence

communicationCarrierGuards :
  CommunicationObservationCarrier →
  List Metaphor.CommunicationNonClaimGuard
communicationCarrierGuards _ =
  Metaphor.canonicalCommunicationNonClaimGuards

communicationCarrierFailures :
  CommunicationObservationCarrier →
  List Metaphor.MisunderstandingFailureMode
communicationCarrierFailures misunderstandingCarrier =
  Metaphor.canonicalMisunderstandingFailureModes
communicationCarrierFailures _ =
  []

canonicalOperatorInvariantObservationSurface :
  Spine.ObservationTransportSurface
canonicalOperatorInvariantObservationSurface =
  record
    { domain =
        Spine.operatorInvariantEquivalenceDomain
    ; LatentCarrier =
        OperatorObservationCarrier
    ; ObservationQuotient =
        Operator.EquivalenceStrength
    ; AdmissibilityGate =
        Operator.OperatorInvariantNonPromotionBoundary
    ; TransportOperator =
        List Operator.InvariantFamilyKind
    ; Artifact =
        OperatorObservationCarrier
    ; observe =
        operatorCarrierStrength
    ; gate =
        λ _ → Operator.canonicalOperatorInvariantNonPromotionBoundary
    ; transport =
        λ carrier _ _ → carrier
    ; promotionBoundary =
        Spine.nonPromotingObservation
    ; nonClaims =
        Spine.canonicalObservationNonClaims
    ; plainReading =
        "operator equivalence is observed through selected invariant families"
    }

canonicalCommunicationObservationSurface :
  Spine.ObservationTransportSurface
canonicalCommunicationObservationSurface =
  record
    { domain =
        Spine.metaphorAlignmentDomain
    ; LatentCarrier =
        CommunicationObservationCarrier
    ; ObservationQuotient =
        List Metaphor.CommunicationNonClaimGuard
    ; AdmissibilityGate =
        List Metaphor.MisunderstandingFailureMode
    ; TransportOperator =
        Metaphor.AlignmentStatus
    ; Artifact =
        CommunicationObservationCarrier
    ; observe =
        communicationCarrierGuards
    ; gate =
        λ _ → communicationCarrierFailures misunderstandingCarrier
    ; transport =
        λ carrier _ _ → carrier
    ; promotionBoundary =
        Spine.nonPromotingObservation
    ; nonClaims =
        Spine.canonicalObservationNonClaims
    ; plainReading =
        "communication alignment is observed through audience-context and failure-mode quotients"
    }

data SemanticOperatorAlignmentGuard : Set where
  NoGlobalOntologyPromotion : SemanticOperatorAlignmentGuard
  NoSubstanceIdentityPromotion : SemanticOperatorAlignmentGuard
  NoUntypedExactEquivalencePromotion : SemanticOperatorAlignmentGuard
  NoUniversalReducibilityPromotion : SemanticOperatorAlignmentGuard
  NoGuaranteedPerfectUnderstandingPromotion : SemanticOperatorAlignmentGuard
  NoQualiaRecoveryPromotion : SemanticOperatorAlignmentGuard
  NoUniversalExactTranslationPromotion : SemanticOperatorAlignmentGuard
  NoContextFreeOptimalCommunicationPromotion : SemanticOperatorAlignmentGuard

canonicalSemanticOperatorAlignmentGuards :
  List SemanticOperatorAlignmentGuard
canonicalSemanticOperatorAlignmentGuards =
  NoGlobalOntologyPromotion
  ∷ NoSubstanceIdentityPromotion
  ∷ NoUntypedExactEquivalencePromotion
  ∷ NoUniversalReducibilityPromotion
  ∷ NoGuaranteedPerfectUnderstandingPromotion
  ∷ NoQualiaRecoveryPromotion
  ∷ NoUniversalExactTranslationPromotion
  ∷ NoContextFreeOptimalCommunicationPromotion
  ∷ []

record SemanticOperatorAlignmentThreadDischarge : Set₁ where
  field
    operatorBoundary :
      Operator.OperatorInvariantNonPromotionBoundary

    debateRedoxPartial :
      Operator.CrossDomainInvariantInstantiation

    debateRedoxExactUnderReceipt :
      Operator.CrossDomainInvariantInstantiation

    debateRedoxExactnessReceipt :
      Operator.ReceiptGatedExactness debateRedoxExactUnderReceipt

    communicationBoundary :
      Metaphor.CommunicationClaimBoundary

    succinctCommunication :
      Metaphor.MDLStyleSuccinctCommunication
        Metaphor.toyObserverQuotient
        Metaphor.toyObserverContext

    operatorSpineSurface :
      Spine.ObservationTransportSurface

    communicationSpineSurface :
      Spine.ObservationTransportSurface

    spineDomains :
      List Spine.ObservationDomain

    spineDomainsAreCanonical :
      spineDomains ≡ canonicalSemanticOperatorSpineDomains

    lanes :
      List SemanticOperatorAlignmentLane

    lanesAreCanonical :
      lanes ≡ canonicalSemanticOperatorAlignmentLanes

    guards :
      List SemanticOperatorAlignmentGuard

    guardsAreCanonical :
      guards ≡ canonicalSemanticOperatorAlignmentGuards

    globalOntologyClaim :
      Bool

    globalOntologyClaimIsFalse :
      globalOntologyClaim ≡ false

    untypedExactEquivalenceClaim :
      Bool

    untypedExactEquivalenceClaimIsFalse :
      untypedExactEquivalenceClaim ≡ false

    universalTranslationClaim :
      Bool

    universalTranslationClaimIsFalse :
      universalTranslationClaim ≡ false

    perfectUnderstandingClaim :
      Bool

    perfectUnderstandingClaimIsFalse :
      perfectUnderstandingClaim ≡ false

    qualiaRecoveryClaim :
      Bool

    qualiaRecoveryClaimIsFalse :
      qualiaRecoveryClaim ≡ false

    contextFreeOptimalCommunicationClaim :
      Bool

    contextFreeOptimalCommunicationClaimIsFalse :
      contextFreeOptimalCommunicationClaim ≡ false

    aggregateReading :
      String

open SemanticOperatorAlignmentThreadDischarge public

record SemanticOperatorAlignmentNonPromotionCertificate
    (discharge : SemanticOperatorAlignmentThreadDischarge) : Set where
  field
    operatorGlobalOntologyBlocked :
      Operator.globalOntologyClaim (operatorBoundary discharge) ≡ false

    operatorSubstanceIdentityBlocked :
      Operator.substanceIdentityClaim (operatorBoundary discharge) ≡ false

    operatorUntypedExactEquivalenceBlocked :
      Operator.untypedExactEquivalenceClaim (operatorBoundary discharge) ≡ false

    operatorUniversalReducibilityBlocked :
      Operator.universalReducibilityClaim (operatorBoundary discharge) ≡ false

    aggregateGlobalOntologyBlocked :
      globalOntologyClaim discharge ≡ false

    aggregateUntypedExactEquivalenceBlocked :
      untypedExactEquivalenceClaim discharge ≡ false

    aggregateUniversalTranslationBlocked :
      universalTranslationClaim discharge ≡ false

    aggregatePerfectUnderstandingBlocked :
      perfectUnderstandingClaim discharge ≡ false

    aggregateQualiaRecoveryBlocked :
      qualiaRecoveryClaim discharge ≡ false

    aggregateContextFreeOptimalCommunicationBlocked :
      contextFreeOptimalCommunicationClaim discharge ≡ false

    certificateReading :
      String

open SemanticOperatorAlignmentNonPromotionCertificate public

canonicalSemanticOperatorAlignmentThreadDischarge :
  SemanticOperatorAlignmentThreadDischarge
canonicalSemanticOperatorAlignmentThreadDischarge =
  record
    { operatorBoundary =
        Operator.canonicalOperatorInvariantNonPromotionBoundary
    ; debateRedoxPartial =
        Operator.toyDebateRedoxPartialInstantiation
    ; debateRedoxExactUnderReceipt =
        Operator.toyDebateRedoxExactUnderReceiptInstantiation
    ; debateRedoxExactnessReceipt =
        Operator.toyDebateRedoxReceiptGatedExactness
    ; communicationBoundary =
        Metaphor.canonicalCommunicationClaimBoundary
          "Communication alignment is observer-context scoped and non-promoting."
    ; succinctCommunication =
        Metaphor.toySuccinctCommunication
    ; operatorSpineSurface =
        canonicalOperatorInvariantObservationSurface
    ; communicationSpineSurface =
        canonicalCommunicationObservationSurface
    ; spineDomains =
        canonicalSemanticOperatorSpineDomains
    ; spineDomainsAreCanonical =
        refl
    ; lanes =
        canonicalSemanticOperatorAlignmentLanes
    ; lanesAreCanonical =
        refl
    ; guards =
        canonicalSemanticOperatorAlignmentGuards
    ; guardsAreCanonical =
        refl
    ; globalOntologyClaim =
        false
    ; globalOntologyClaimIsFalse =
        refl
    ; untypedExactEquivalenceClaim =
        false
    ; untypedExactEquivalenceClaimIsFalse =
        refl
    ; universalTranslationClaim =
        false
    ; universalTranslationClaimIsFalse =
        refl
    ; perfectUnderstandingClaim =
        false
    ; perfectUnderstandingClaimIsFalse =
        refl
    ; qualiaRecoveryClaim =
        false
    ; qualiaRecoveryClaimIsFalse =
        refl
    ; contextFreeOptimalCommunicationClaim =
        false
    ; contextFreeOptimalCommunicationClaimIsFalse =
        refl
    ; aggregateReading =
        "The semantic/operator-alignment tail is discharged as invariant-scoped cross-domain operator equivalence plus observer-context metaphor, succinctness, and misunderstanding quotients.  The aggregate is non-promoting."
    }

canonicalSemanticOperatorAlignmentNonPromotionCertificate :
  SemanticOperatorAlignmentNonPromotionCertificate
    canonicalSemanticOperatorAlignmentThreadDischarge
canonicalSemanticOperatorAlignmentNonPromotionCertificate =
  record
    { operatorGlobalOntologyBlocked =
        refl
    ; operatorSubstanceIdentityBlocked =
        refl
    ; operatorUntypedExactEquivalenceBlocked =
        refl
    ; operatorUniversalReducibilityBlocked =
        refl
    ; aggregateGlobalOntologyBlocked =
        refl
    ; aggregateUntypedExactEquivalenceBlocked =
        refl
    ; aggregateUniversalTranslationBlocked =
        refl
    ; aggregatePerfectUnderstandingBlocked =
        refl
    ; aggregateQualiaRecoveryBlocked =
        refl
    ; aggregateContextFreeOptimalCommunicationBlocked =
        refl
    ; certificateReading =
        "The aggregate certificate preserves operator and communication non-promotion boundaries."
    }
