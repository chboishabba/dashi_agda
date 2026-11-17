module DASHI.Interop.BackgroundDistributionBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.RoleGrammarCore as RoleCore
import DASHI.Core.AdapterCanonicalityCore as AdapterCanonicalityCore
import DASHI.Core.AuthorityNonPromotionCore as AuthorityNonPromotionCore
import DASHI.Core.BridgeRequirementCore as BridgeRequirementCore
import DASHI.Core.CandidateOnlyCore as CandidateOnlyCore
import DASHI.Core.FormalLensQualificationCore as FormalLensCore

------------------------------------------------------------------------
-- Background distributional bridge receipt.
--
-- This module records implicit/background cross-domain distributional
-- bridge vocabulary as a receipt surface only.  It distinguishes explicit
-- transport receipts and well-established causal chains from weak
-- proof-by-omission / god-of-gaps readings.  It does not assert empirical
-- truth for any example lane, including the economy-to-person-behaviour
-- observable example.

data BridgeStrength : Set where
  explicitTransportReceiptStrongest :
    BridgeStrength

  wellEstablishedCausalChain :
    BridgeStrength

  backgroundDistributionalAssociation :
    BridgeStrength

  proofByOmissionGodOfGapsWeakest :
    BridgeStrength

data ResidualName : Set where
  EXACT :
    ResidualName

  PARTIAL :
    ResidualName

  NO_TYPED_MEET :
    ResidualName

  CONTRADICTION :
    ResidualName

data ObservableName : Set where
  receiptObservable :
    ObservableName

  mechanismObservable :
    ObservableName

  economyObservable :
    ObservableName

  personBehaviourObservable :
    ObservableName

  claimNarrativeObservable :
    ObservableName

record Falsifier : Set where
  constructor falsifier
  field
    falsifierName :
      String

    falsifierCondition :
      String

    falsifierResidual :
      ResidualName

open Falsifier public

record OutlierCondition : Set where
  constructor outlierCondition
  field
    outlierName :
      String

    outlierDescription :
      String

    outlierResidual :
      ResidualName

open OutlierCondition public

record BackgroundDistributionalBridge : Set where
  constructor backgroundDistributionalBridge
  field
    bdbName :
      String

    bdbSource :
      ObservableName

    bdbTarget :
      ObservableName

    bdbStrength :
      BridgeStrength

    bdbResidual :
      ResidualName

    bdbStrongestTransportReceipt :
      Bool

    bdbCausalChainEstablished :
      Bool

    bdbImplicitBackgroundOnly :
      Bool

    bdbProofByOmissionOrGodOfGaps :
      Bool

    bdbFalsifiers :
      List Falsifier

    bdbOutlierCondition :
      OutlierCondition

    bdbPromoted :
      Bool

    bdbPromotedIsFalse :
      bdbPromoted ≡ false

    bdbNoEmpiricalTruthClaim :
      Bool

    bdbNoEmpiricalTruthClaimIsTrue :
      bdbNoEmpiricalTruthClaim ≡ true

    bdbReceiptNote :
      String

open BackgroundDistributionalBridge public

------------------------------------------------------------------------
-- Core-aligned bridge candidate/profile layer.
--
-- DASHI.Interop.RoleGrammarCore is expected to carry these generic role
-- grammar concepts.  This adapter keeps the public BackgroundDistributionBridge
-- names stable while moving repeated strength/candidate/gate facts behind one
-- reusable construction surface.

observableCoreDomain :
  ObservableName →
  RoleCore.DomainLabel
observableCoreDomain receiptObservable =
  RoleCore.genericDomain
observableCoreDomain mechanismObservable =
  RoleCore.genericDomain
observableCoreDomain economyObservable =
  RoleCore.economyDomain
observableCoreDomain personBehaviourObservable =
  RoleCore.personBehaviourDomain
observableCoreDomain claimNarrativeObservable =
  RoleCore.namedDomain "ClaimNarrative"

backgroundStrengthCoreBridgeStrength :
  BridgeStrength →
  RoleCore.BridgeStrength
backgroundStrengthCoreBridgeStrength explicitTransportReceiptStrongest =
  RoleCore.exactBridge
backgroundStrengthCoreBridgeStrength wellEstablishedCausalChain =
  RoleCore.exactBridge
backgroundStrengthCoreBridgeStrength backgroundDistributionalAssociation =
  RoleCore.partialBridge
backgroundStrengthCoreBridgeStrength proofByOmissionGodOfGapsWeakest =
  RoleCore.weakBridge

backgroundStrengthCoreAuthorityClass :
  BridgeStrength →
  RoleCore.AuthorityClass
backgroundStrengthCoreAuthorityClass explicitTransportReceiptStrongest =
  RoleCore.bridgeReceiptClass
backgroundStrengthCoreAuthorityClass wellEstablishedCausalChain =
  RoleCore.bridgeReceiptClass
backgroundStrengthCoreAuthorityClass backgroundDistributionalAssociation =
  RoleCore.candidateOnlyClass
backgroundStrengthCoreAuthorityClass proofByOmissionGodOfGapsWeakest =
  RoleCore.candidateOnlyClass

backgroundStrengthCoreAdmissionStatus :
  BridgeStrength →
  RoleCore.AdmissionStatus
backgroundStrengthCoreAdmissionStatus explicitTransportReceiptStrongest =
  RoleCore.candidateAdmission
backgroundStrengthCoreAdmissionStatus wellEstablishedCausalChain =
  RoleCore.candidateAdmission
backgroundStrengthCoreAdmissionStatus backgroundDistributionalAssociation =
  RoleCore.blockedPendingBridgeAdmission
backgroundStrengthCoreAdmissionStatus proofByOmissionGodOfGapsWeakest =
  RoleCore.blockedPendingBridgeAdmission

backgroundStrengthCoreBridgeHasNoExternalAuthority :
  ∀ strength →
  RoleCore.bridgeStrengthExternalAuthority
    (backgroundStrengthCoreBridgeStrength strength)
  ≡
  false
backgroundStrengthCoreBridgeHasNoExternalAuthority strength =
  RoleCore.bridgeStrengthDoesNotCreateExternalAuthority
    (backgroundStrengthCoreBridgeStrength strength)

backgroundStrengthCoreAuthorityHasNoExternalAuthority :
  ∀ strength →
  RoleCore.authorityClassExternalAuthority
    (backgroundStrengthCoreAuthorityClass strength)
  ≡
  false
backgroundStrengthCoreAuthorityHasNoExternalAuthority strength =
  RoleCore.authorityClassDoesNotCreateExternalAuthority
    (backgroundStrengthCoreAuthorityClass strength)

backgroundStrengthCoreAdmissionHasNoExternalAuthority :
  ∀ strength →
  RoleCore.admissionExternalAuthority
    (backgroundStrengthCoreAdmissionStatus strength)
  ≡
  false
backgroundStrengthCoreAdmissionHasNoExternalAuthority strength =
  RoleCore.admissionDoesNotCreateExternalAuthority
    (backgroundStrengthCoreAdmissionStatus strength)

bridgeStrengthHasStrongestTransportReceipt :
  BridgeStrength →
  Bool
bridgeStrengthHasStrongestTransportReceipt explicitTransportReceiptStrongest =
  true
bridgeStrengthHasStrongestTransportReceipt wellEstablishedCausalChain =
  false
bridgeStrengthHasStrongestTransportReceipt backgroundDistributionalAssociation =
  false
bridgeStrengthHasStrongestTransportReceipt proofByOmissionGodOfGapsWeakest =
  false

bridgeStrengthHasEstablishedCausalChain :
  BridgeStrength →
  Bool
bridgeStrengthHasEstablishedCausalChain explicitTransportReceiptStrongest =
  true
bridgeStrengthHasEstablishedCausalChain wellEstablishedCausalChain =
  true
bridgeStrengthHasEstablishedCausalChain backgroundDistributionalAssociation =
  false
bridgeStrengthHasEstablishedCausalChain proofByOmissionGodOfGapsWeakest =
  false

bridgeStrengthIsImplicitBackgroundOnly :
  BridgeStrength →
  Bool
bridgeStrengthIsImplicitBackgroundOnly explicitTransportReceiptStrongest =
  false
bridgeStrengthIsImplicitBackgroundOnly wellEstablishedCausalChain =
  false
bridgeStrengthIsImplicitBackgroundOnly backgroundDistributionalAssociation =
  true
bridgeStrengthIsImplicitBackgroundOnly proofByOmissionGodOfGapsWeakest =
  true

bridgeStrengthIsProofByOmissionOrGodOfGaps :
  BridgeStrength →
  Bool
bridgeStrengthIsProofByOmissionOrGodOfGaps explicitTransportReceiptStrongest =
  false
bridgeStrengthIsProofByOmissionOrGodOfGaps wellEstablishedCausalChain =
  false
bridgeStrengthIsProofByOmissionOrGodOfGaps backgroundDistributionalAssociation =
  false
bridgeStrengthIsProofByOmissionOrGodOfGaps proofByOmissionGodOfGapsWeakest =
  true

record BackgroundBridgeCandidateProfile : Set where
  constructor backgroundBridgeCandidateProfile
  field
    candidateName :
      String

    candidateSource :
      ObservableName

    candidateTarget :
      ObservableName

    candidateStrength :
      BridgeStrength

    candidateResidual :
      ResidualName

    candidateFalsifiers :
      List Falsifier

    candidateOutlierCondition :
      OutlierCondition

    candidateReceiptNote :
      String

open BackgroundBridgeCandidateProfile public

------------------------------------------------------------------------
-- Reusable core adapters.
--
-- These adapters consume the shared candidate-only/non-promotion cores while
-- preserving the local BackgroundDistributionalBridge/Profile surface.

bridgeRequirementCoreAdapter :
  BackgroundBridgeCandidateProfile →
  BridgeRequirementCore.BridgeRequirementRow
bridgeRequirementCoreAdapter candidate =
  BridgeRequirementCore.canonicalBridgeRequirementRow
    (candidateName candidate)
    (candidateReceiptNote candidate)
    BridgeRequirementCore.bridgeSuppliedCandidateOnly
    true
    true
    true

bridgeRequirementCoreAdapterReceipt :
  (candidate : BackgroundBridgeCandidateProfile) →
  BridgeRequirementCore.BridgeRequirementRowReceipt
    (bridgeRequirementCoreAdapter candidate)
bridgeRequirementCoreAdapterReceipt candidate =
  BridgeRequirementCore.canonicalBridgeRequirementRowReceipt
    (bridgeRequirementCoreAdapter candidate)
    refl
    refl
    refl

bridgeRequirementCoreAdapterBridgeAuthorityFalse :
  (candidate : BackgroundBridgeCandidateProfile) →
  BridgeRequirementCore.rowBackgroundBridgeAuthority
    (bridgeRequirementCoreAdapter candidate)
  ≡
  false
bridgeRequirementCoreAdapterBridgeAuthorityFalse candidate =
  BridgeRequirementCore.rowBackgroundBridgeAuthorityFalse
    (bridgeRequirementCoreAdapterReceipt candidate)

bridgeRequirementCoreAdapterAuthorityPromotionFalse :
  (candidate : BackgroundBridgeCandidateProfile) →
  BridgeRequirementCore.rowAuthorityPromotion
    (bridgeRequirementCoreAdapter candidate)
  ≡
  false
bridgeRequirementCoreAdapterAuthorityPromotionFalse candidate =
  BridgeRequirementCore.rowAuthorityPromotionFalse
    (bridgeRequirementCoreAdapterReceipt candidate)

bridgeRequirementCoreAdapterTransportMapAuthorityFalse :
  (candidate : BackgroundBridgeCandidateProfile) →
  BridgeRequirementCore.rowTransportMapAuthority
    (bridgeRequirementCoreAdapter candidate)
  ≡
  false
bridgeRequirementCoreAdapterTransportMapAuthorityFalse candidate =
  BridgeRequirementCore.rowTransportMapAuthorityFalse
    (bridgeRequirementCoreAdapterReceipt candidate)

candidateOnlyCoreAdapter :
  BackgroundBridgeCandidateProfile →
  CandidateOnlyCore.CandidateOnlyRow
candidateOnlyCoreAdapter candidate =
  CandidateOnlyCore.mkCandidateOnlyRow
    (candidateName candidate)
    "DASHI.Interop.BackgroundDistributionBridge"
    "BackgroundBridgeCandidateProfile"
    CandidateOnlyCore.bridgeCandidateKind
    CandidateOnlyCore.bridgeCandidateOnlyStatus
    "background distributional bridge profiles are candidate-only receipt surfaces"
    "empirical truth, bridge authority, and promotion require separate accepted authority artifacts"

candidateOnlyCoreAdapterReceipt :
  (candidate : BackgroundBridgeCandidateProfile) →
  CandidateOnlyCore.CandidateOnlyReceipt
    (candidateOnlyCoreAdapter candidate)
candidateOnlyCoreAdapterReceipt candidate =
  CandidateOnlyCore.canonicalCandidateOnlyReceipt
    (candidateOnlyCoreAdapter candidate)
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

candidateOnlyCoreAdapterPromotedFalse :
  (candidate : BackgroundBridgeCandidateProfile) →
  CandidateOnlyCore.promoted
    (candidateOnlyCoreAdapter candidate)
  ≡
  false
candidateOnlyCoreAdapterPromotedFalse candidate =
  CandidateOnlyCore.candidatePromotedIsFalse
    (candidateOnlyCoreAdapterReceipt candidate)

candidateOnlyCoreAdapterTruthAuthorityFalse :
  (candidate : BackgroundBridgeCandidateProfile) →
  CandidateOnlyCore.carriesTruthAuthority
    (candidateOnlyCoreAdapter candidate)
  ≡
  false
candidateOnlyCoreAdapterTruthAuthorityFalse candidate =
  CandidateOnlyCore.candidateNoTruthAuthority
    (candidateOnlyCoreAdapterReceipt candidate)

authorityNonPromotionCoreAdapter :
  BackgroundBridgeCandidateProfile →
  AuthorityNonPromotionCore.AuthorityNonPromotionBundle
authorityNonPromotionCoreAdapter candidate =
  AuthorityNonPromotionCore.mkClosedAuthorityNonPromotionBundle
    (candidateName candidate)

authorityNonPromotionCoreAdapterEmpiricalAuthorityFalse :
  (candidate : BackgroundBridgeCandidateProfile) →
  AuthorityNonPromotionCore.empiricalAuthorityFlag
    (authorityNonPromotionCoreAdapter candidate)
  ≡
  false
authorityNonPromotionCoreAdapterEmpiricalAuthorityFalse candidate =
  AuthorityNonPromotionCore.bundleEmpiricalAuthorityIsFalse
    (authorityNonPromotionCoreAdapter candidate)

authorityNonPromotionCoreAdapterExternalAuthorityFalse :
  (candidate : BackgroundBridgeCandidateProfile) →
  AuthorityNonPromotionCore.externalAuthorityFlag
    (authorityNonPromotionCoreAdapter candidate)
  ≡
  false
authorityNonPromotionCoreAdapterExternalAuthorityFalse candidate =
  AuthorityNonPromotionCore.bundleExternalAuthorityIsFalse
    (authorityNonPromotionCoreAdapter candidate)

authorityNonPromotionCoreAdapterPromotesAnyAuthorityFalse :
  (candidate : BackgroundBridgeCandidateProfile) →
  AuthorityNonPromotionCore.promotesAnyAuthority
    (authorityNonPromotionCoreAdapter candidate)
  ≡
  false
authorityNonPromotionCoreAdapterPromotesAnyAuthorityFalse candidate =
  AuthorityNonPromotionCore.bundlePromotesAnyAuthorityIsFalse
    (authorityNonPromotionCoreAdapter candidate)

------------------------------------------------------------------------
-- Formal-lens qualification compatibility surface.
--
-- This local surface consumes FormalLensQualificationCore and routes every
-- authority bit through existing reusable fail-closed cores.  It is
-- candidate-only evidence: no probability theorem authority, empirical
-- adequacy, background distribution authority, transport authority, external
-- authority, or promotion is introduced here.

FormalLens : Set
FormalLens =
  FormalLensCore.FormalLens

backgroundFormalLensQualificationCanonicalLenses :
  List FormalLens
backgroundFormalLensQualificationCanonicalLenses =
  FormalLensCore.Probabilistic
  ∷ FormalLensCore.Information
  ∷ FormalLensCore.Category
  ∷ FormalLensCore.Functional
  ∷ []

record BackgroundFormalLensQualificationSurface
    (candidate : BackgroundBridgeCandidateProfile) : Set where
  constructor backgroundFormalLensQualificationSurface
  field
    formalLensQualifiedLenses :
      List FormalLens

    formalLensQualifiedLensesAreCanonical :
      formalLensQualifiedLenses
      ≡
      backgroundFormalLensQualificationCanonicalLenses

    formalLensProbabilisticReading :
      Bool

    formalLensProbabilisticReadingIsTrue :
      formalLensProbabilisticReading ≡ true

    formalLensInformationReading :
      Bool

    formalLensInformationReadingIsTrue :
      formalLensInformationReading ≡ true

    formalLensCategoryReading :
      Bool

    formalLensCategoryReadingIsTrue :
      formalLensCategoryReading ≡ true

    formalLensFunctionalReading :
      Bool

    formalLensFunctionalReadingIsTrue :
      formalLensFunctionalReading ≡ true

    formalLensGradientFlowReading :
      Bool

    formalLensGradientFlowReadingIsFalse :
      formalLensGradientFlowReading ≡ false

    formalLensSymbolicRationalReading :
      Bool

    formalLensSymbolicRationalReadingIsFalse :
      formalLensSymbolicRationalReading ≡ false

    formalLensCandidateOnlyAdapter :
      CandidateOnlyCore.CandidateOnlyRow

    formalLensCandidateOnlyAdapterReceipt :
      CandidateOnlyCore.CandidateOnlyReceipt
        formalLensCandidateOnlyAdapter

    formalLensCandidateOnlyIsTrue :
      CandidateOnlyCore.candidateOnly
        formalLensCandidateOnlyAdapter
      ≡
      true

    formalLensCandidateOnlyPromotedFalse :
      CandidateOnlyCore.promoted
        formalLensCandidateOnlyAdapter
      ≡
      false

    formalLensCandidateOnlyTruthAuthorityFalse :
      CandidateOnlyCore.carriesTruthAuthority
        formalLensCandidateOnlyAdapter
      ≡
      false

    formalLensCandidateOnlySupportAuthorityFalse :
      CandidateOnlyCore.carriesSupportAuthority
        formalLensCandidateOnlyAdapter
      ≡
      false

    formalLensCandidateOnlyAdmissibilityAuthorityFalse :
      CandidateOnlyCore.carriesAdmissibilityAuthority
        formalLensCandidateOnlyAdapter
      ≡
      false

    formalLensCandidateOnlyTheoremAuthorityFalse :
      CandidateOnlyCore.carriesTheoremAuthority
        formalLensCandidateOnlyAdapter
      ≡
      false

    formalLensAuthorityFailClosedAdapter :
      AuthorityNonPromotionCore.AuthorityNonPromotionBundle

    formalLensTruthAuthorityFalse :
      AuthorityNonPromotionCore.truthAuthorityFlag
        formalLensAuthorityFailClosedAdapter
      ≡
      false

    formalLensSupportAuthorityFalse :
      AuthorityNonPromotionCore.supportAuthorityFlag
        formalLensAuthorityFailClosedAdapter
      ≡
      false

    formalLensAdmissibilityAuthorityFalse :
      AuthorityNonPromotionCore.admissibilityAuthorityFlag
        formalLensAuthorityFailClosedAdapter
      ≡
      false

    formalLensTheoremAuthorityFalse :
      AuthorityNonPromotionCore.theoremAuthorityFlag
        formalLensAuthorityFailClosedAdapter
      ≡
      false

    formalLensEmpiricalAuthorityFalse :
      AuthorityNonPromotionCore.empiricalAuthorityFlag
        formalLensAuthorityFailClosedAdapter
      ≡
      false

    formalLensExternalAuthorityFalse :
      AuthorityNonPromotionCore.externalAuthorityFlag
        formalLensAuthorityFailClosedAdapter
      ≡
      false

    formalLensPromotesAnyAuthorityFalse :
      AuthorityNonPromotionCore.promotesAnyAuthority
        formalLensAuthorityFailClosedAdapter
      ≡
      false

    formalLensBridgeRequirementAdapter :
      BridgeRequirementCore.BridgeRequirementRow

    formalLensBridgeRequirementAdapterReceipt :
      BridgeRequirementCore.BridgeRequirementRowReceipt
        formalLensBridgeRequirementAdapter

    formalLensBackgroundDistributionAuthorityFalse :
      BridgeRequirementCore.rowBackgroundBridgeAuthority
        formalLensBridgeRequirementAdapter
      ≡
      false

    formalLensTransportAuthorityFalse :
      BridgeRequirementCore.rowTransportMapAuthority
        formalLensBridgeRequirementAdapter
      ≡
      false

    formalLensBridgeAuthorityPromotionFalse :
      BridgeRequirementCore.rowAuthorityPromotion
        formalLensBridgeRequirementAdapter
      ≡
      false

    formalLensAdapterCanonicality :
      AdapterCanonicalityCore.AdapterCanonicalityReceipt
        (List FormalLens)
        backgroundFormalLensQualificationCanonicalLenses

    formalLensAdapterIsCanonical :
      AdapterCanonicalityCore.adapter
        formalLensAdapterCanonicality
      ≡
      backgroundFormalLensQualificationCanonicalLenses

    formalLensAdapterCanonicalityAuthorityFalse :
      AdapterCanonicalityCore.adapterPromotesAuthority
        formalLensAdapterCanonicality
      ≡
      false

    formalLensProbabilityTheoremAuthority :
      Bool

    formalLensProbabilityTheoremAuthorityIsFalse :
      formalLensProbabilityTheoremAuthority ≡ false

    formalLensEmpiricalAdequacyAuthority :
      Bool

    formalLensEmpiricalAdequacyAuthorityIsFalse :
      formalLensEmpiricalAdequacyAuthority ≡ false

    formalLensBackgroundDistributionAuthority :
      Bool

    formalLensBackgroundDistributionAuthorityIsFalse :
      formalLensBackgroundDistributionAuthority ≡ false

    formalLensTransportAuthority :
      Bool

    formalLensTransportAuthorityIsFalse :
      formalLensTransportAuthority ≡ false

    formalLensExternalAuthority :
      Bool

    formalLensExternalAuthorityIsFalse :
      formalLensExternalAuthority ≡ false

    formalLensPromoted :
      Bool

    formalLensPromotedIsFalse :
      formalLensPromoted ≡ false

    formalLensQualificationReading :
      String

open BackgroundFormalLensQualificationSurface public

backgroundFormalLensQualificationAdapterCanonicality :
  AdapterCanonicalityCore.AdapterCanonicalityReceipt
    (List FormalLens)
    backgroundFormalLensQualificationCanonicalLenses
backgroundFormalLensQualificationAdapterCanonicality =
  AdapterCanonicalityCore.mkCanonicalAdapterReceipt
    "background distribution formal-lens qualification canonicality"
    "DASHI.Interop.BackgroundDistributionBridge"
    "backgroundFormalLensQualificationCanonicalLenses"
    AdapterCanonicalityCore.receiptAdapterKind
    backgroundFormalLensQualificationCanonicalLenses

backgroundFormalLensQualification :
  (candidate : BackgroundBridgeCandidateProfile) →
  BackgroundFormalLensQualificationSurface candidate
backgroundFormalLensQualification candidate =
  backgroundFormalLensQualificationSurface
    backgroundFormalLensQualificationCanonicalLenses
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    (candidateOnlyCoreAdapter candidate)
    (candidateOnlyCoreAdapterReceipt candidate)
    (CandidateOnlyCore.candidateOnlyIsTrue
      (candidateOnlyCoreAdapterReceipt candidate))
    (CandidateOnlyCore.candidatePromotedIsFalse
      (candidateOnlyCoreAdapterReceipt candidate))
    (CandidateOnlyCore.candidateNoTruthAuthority
      (candidateOnlyCoreAdapterReceipt candidate))
    (CandidateOnlyCore.candidateNoSupportAuthority
      (candidateOnlyCoreAdapterReceipt candidate))
    (CandidateOnlyCore.candidateNoAdmissibilityAuthority
      (candidateOnlyCoreAdapterReceipt candidate))
    (CandidateOnlyCore.candidateNoTheoremAuthority
      (candidateOnlyCoreAdapterReceipt candidate))
    (authorityNonPromotionCoreAdapter candidate)
    (AuthorityNonPromotionCore.bundleTruthAuthorityIsFalse
      (authorityNonPromotionCoreAdapter candidate))
    (AuthorityNonPromotionCore.bundleSupportAuthorityIsFalse
      (authorityNonPromotionCoreAdapter candidate))
    (AuthorityNonPromotionCore.bundleAdmissibilityAuthorityIsFalse
      (authorityNonPromotionCoreAdapter candidate))
    (AuthorityNonPromotionCore.bundleTheoremAuthorityIsFalse
      (authorityNonPromotionCoreAdapter candidate))
    (AuthorityNonPromotionCore.bundleEmpiricalAuthorityIsFalse
      (authorityNonPromotionCoreAdapter candidate))
    (AuthorityNonPromotionCore.bundleExternalAuthorityIsFalse
      (authorityNonPromotionCoreAdapter candidate))
    (AuthorityNonPromotionCore.bundlePromotesAnyAuthorityIsFalse
      (authorityNonPromotionCoreAdapter candidate))
    (bridgeRequirementCoreAdapter candidate)
    (bridgeRequirementCoreAdapterReceipt candidate)
    (BridgeRequirementCore.rowBackgroundBridgeAuthorityFalse
      (bridgeRequirementCoreAdapterReceipt candidate))
    (BridgeRequirementCore.rowTransportMapAuthorityFalse
      (bridgeRequirementCoreAdapterReceipt candidate))
    (BridgeRequirementCore.rowAuthorityPromotionFalse
      (bridgeRequirementCoreAdapterReceipt candidate))
    backgroundFormalLensQualificationAdapterCanonicality
    (AdapterCanonicalityCore.adapterCanonical
      backgroundFormalLensQualificationAdapterCanonicality)
    (AdapterCanonicalityCore.adapterAuthorityPromotionFalse
      backgroundFormalLensQualificationAdapterCanonicality)
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    "BackgroundDistributionBridge is formal-lens-qualified only as probabilistic, information, category, and functional reading; the adapter is candidate-only and authority fail-closed."

backgroundCandidateSourceCoreTypedTerm :
  BackgroundBridgeCandidateProfile →
  RoleCore.GenericTypedTerm String
backgroundCandidateSourceCoreTypedTerm candidate =
  RoleCore.genericTypedTerm
    zero
    (candidateName candidate)
    (candidateName candidate)
    (candidateName candidate)
    (observableCoreDomain (candidateSource candidate))
    RoleCore.observableRole
    RoleCore.candidateStatus
    RoleCore.candidateOnlyClass
    (RoleCore.domainBridgeStrength (observableCoreDomain (candidateSource candidate)))
    RoleCore.candidateAdmission
    (candidateReceiptNote candidate)
    "BackgroundDistributionBridge source observable is represented as a RoleGrammarCore candidate observable."

backgroundCandidateTargetCoreTypedTerm :
  BackgroundBridgeCandidateProfile →
  RoleCore.GenericTypedTerm String
backgroundCandidateTargetCoreTypedTerm candidate =
  RoleCore.genericTypedTerm
    zero
    (candidateName candidate)
    (candidateName candidate)
    (candidateName candidate)
    (observableCoreDomain (candidateTarget candidate))
    RoleCore.observableRole
    RoleCore.candidateStatus
    RoleCore.candidateOnlyClass
    (RoleCore.domainBridgeStrength (observableCoreDomain (candidateTarget candidate)))
    RoleCore.candidateAdmission
    (candidateReceiptNote candidate)
    "BackgroundDistributionBridge target observable is represented as a RoleGrammarCore candidate observable."

backgroundCandidateCoreTypedTerm :
  BackgroundBridgeCandidateProfile →
  RoleCore.GenericTypedTerm String
backgroundCandidateCoreTypedTerm candidate =
  RoleCore.genericTypedTerm
    zero
    (candidateName candidate)
    (candidateName candidate)
    (candidateName candidate)
    (observableCoreDomain (candidateSource candidate))
    RoleCore.bridgeReceiptRole
    RoleCore.candidateStatus
    (backgroundStrengthCoreAuthorityClass (candidateStrength candidate))
    (backgroundStrengthCoreBridgeStrength (candidateStrength candidate))
    (backgroundStrengthCoreAdmissionStatus (candidateStrength candidate))
    (candidateReceiptNote candidate)
    "BackgroundDistributionBridge candidate profile delegates generic role/admission/authority classification to RoleGrammarCore."

backgroundCandidateCoreTermHasNoExternalAuthority :
  (candidate : BackgroundBridgeCandidateProfile) →
  RoleCore.typedTermExternalAuthority
    (backgroundCandidateCoreTypedTerm candidate)
  ≡
  false
backgroundCandidateCoreTermHasNoExternalAuthority candidate =
  RoleCore.typedTermHasNoExternalAuthority
    (backgroundCandidateCoreTypedTerm candidate)

backgroundCandidateCoreBridgeHasNoExternalAuthority :
  (candidate : BackgroundBridgeCandidateProfile) →
  RoleCore.typedTermBridgeExternalAuthority
    (backgroundCandidateCoreTypedTerm candidate)
  ≡
  false
backgroundCandidateCoreBridgeHasNoExternalAuthority candidate =
  RoleCore.typedTermBridgeHasNoExternalAuthority
    (backgroundCandidateCoreTypedTerm candidate)

backgroundCandidateSourceHasNoExternalAuthority :
  (candidate : BackgroundBridgeCandidateProfile) →
  RoleCore.typedTermExternalAuthority
    (backgroundCandidateSourceCoreTypedTerm candidate)
  ≡
  false
backgroundCandidateSourceHasNoExternalAuthority candidate =
  RoleCore.typedTermHasNoExternalAuthority
    (backgroundCandidateSourceCoreTypedTerm candidate)

backgroundCandidateTargetHasNoExternalAuthority :
  (candidate : BackgroundBridgeCandidateProfile) →
  RoleCore.typedTermExternalAuthority
    (backgroundCandidateTargetCoreTypedTerm candidate)
  ≡
  false
backgroundCandidateTargetHasNoExternalAuthority candidate =
  RoleCore.typedTermHasNoExternalAuthority
    (backgroundCandidateTargetCoreTypedTerm candidate)

backgroundCandidateToBridge :
  BackgroundBridgeCandidateProfile →
  BackgroundDistributionalBridge
backgroundCandidateToBridge candidate =
  backgroundDistributionalBridge
    (candidateName candidate)
    (candidateSource candidate)
    (candidateTarget candidate)
    (candidateStrength candidate)
    (candidateResidual candidate)
    (bridgeStrengthHasStrongestTransportReceipt (candidateStrength candidate))
    (bridgeStrengthHasEstablishedCausalChain (candidateStrength candidate))
    (bridgeStrengthIsImplicitBackgroundOnly (candidateStrength candidate))
    (bridgeStrengthIsProofByOmissionOrGodOfGaps (candidateStrength candidate))
    (candidateFalsifiers candidate)
    (candidateOutlierCondition candidate)
    false
    refl
    true
    refl
    (candidateReceiptNote candidate)

data BackgroundBridgeGateName : Set where
  noEmpiricalTruthPromotionGate :
    BackgroundBridgeGateName

  noCausationFromBackgroundDistributionGate :
    BackgroundBridgeGateName

  noPolicyAuthorityPromotionGate :
    BackgroundBridgeGateName

  noPersonBehaviourTruthPromotionGate :
    BackgroundBridgeGateName

record BackgroundBridgePromotionGate : Set where
  constructor backgroundBridgePromotionGate
  field
    gateName :
      BackgroundBridgeGateName

    gateBridge :
      BackgroundDistributionalBridge

    gatePromoted :
      Bool

    gatePromotedIsFalse :
      gatePromoted ≡ false

    gateReason :
      String

open BackgroundBridgePromotionGate public

backgroundBridgeAuthorityGate :
  BackgroundBridgeGateName →
  BackgroundDistributionalBridge →
  String →
  BackgroundBridgePromotionGate
backgroundBridgeAuthorityGate gate bridge reason =
  backgroundBridgePromotionGate
    gate
    bridge
    false
    refl
    reason

------------------------------------------------------------------------
-- Named falsifiers and outlier conditions.

missingTransportReceiptFalsifier : Falsifier
missingTransportReceiptFalsifier =
  falsifier
    "missing-explicit-transport-receipt"
    "No typed transport receipt connects the source observable to the target observable."
    NO_TYPED_MEET

counterMechanismFalsifier : Falsifier
counterMechanismFalsifier =
  falsifier
    "counter-mechanism-or-confounder"
    "A named confounder or counter-mechanism explains the target observable without the proposed bridge."
    PARTIAL

empiricalContradictionFalsifier : Falsifier
empiricalContradictionFalsifier =
  falsifier
    "empirical-contradiction"
    "The proposed bridge predicts a receipt row that conflicts with the observed target row."
    CONTRADICTION

noNamedResidualOutlierCondition : OutlierCondition
noNamedResidualOutlierCondition =
  outlierCondition
    "no-named-residual"
    "The bridge has not named the residual class that could absorb or explain outliers."
    NO_TYPED_MEET

backgroundOutlierCondition : OutlierCondition
backgroundOutlierCondition =
  outlierCondition
    "background-distribution-outlier"
    "Distributional fit leaves named source-to-target outliers rather than an explicit individual-level transport receipt."
    PARTIAL

proofByOmissionResidualOutlierCondition : OutlierCondition
proofByOmissionResidualOutlierCondition =
  outlierCondition
    "proof-by-omission-god-of-gaps-residual"
    "The missing mechanism is treated as support; the residual is therefore explicit and remains PARTIAL."
    PARTIAL

------------------------------------------------------------------------
-- Canonical bridges.

explicitTransportReceiptCandidateProfile :
  BackgroundBridgeCandidateProfile
explicitTransportReceiptCandidateProfile =
  backgroundBridgeCandidateProfile
    "explicit-transport-receipt-strongest"
    receiptObservable
    mechanismObservable
    explicitTransportReceiptStrongest
    EXACT
    (empiricalContradictionFalsifier ∷ [])
    noNamedResidualOutlierCondition
    "Strongest receipt class: an explicit typed transport receipt is present; this module still does not promote an empirical claim."

explicitTransportReceiptBridge :
  BackgroundDistributionalBridge
explicitTransportReceiptBridge =
  backgroundCandidateToBridge explicitTransportReceiptCandidateProfile

wellEstablishedCausalChainCandidateProfile :
  BackgroundBridgeCandidateProfile
wellEstablishedCausalChainCandidateProfile =
  backgroundBridgeCandidateProfile
    "well-established-causal-chain"
    mechanismObservable
    personBehaviourObservable
    wellEstablishedCausalChain
    EXACT
    (counterMechanismFalsifier ∷ empiricalContradictionFalsifier ∷ [])
    backgroundOutlierCondition
    "Named causal-chain receipt class; it records the shape of causal transport without asserting a domain truth claim."

wellEstablishedCausalChainBridge :
  BackgroundDistributionalBridge
wellEstablishedCausalChainBridge =
  backgroundCandidateToBridge wellEstablishedCausalChainCandidateProfile

economyToPersonBehaviourDistributionalCandidateProfile :
  BackgroundBridgeCandidateProfile
economyToPersonBehaviourDistributionalCandidateProfile =
  backgroundBridgeCandidateProfile
    "economy-observable-to-person-behaviour-observable-example"
    economyObservable
    personBehaviourObservable
    backgroundDistributionalAssociation
    PARTIAL
    (missingTransportReceiptFalsifier ∷ counterMechanismFalsifier ∷ empiricalContradictionFalsifier ∷ [])
    backgroundOutlierCondition
    "Example lane only: Economy.Observable -> PersonBehaviour.Observable records a possible background distributional bridge shape, not an empirical truth claim."

economyToPersonBehaviourDistributionalExample :
  BackgroundDistributionalBridge
economyToPersonBehaviourDistributionalExample =
  backgroundCandidateToBridge economyToPersonBehaviourDistributionalCandidateProfile

proofByOmissionGodOfGapsCandidateProfile :
  BackgroundBridgeCandidateProfile
proofByOmissionGodOfGapsCandidateProfile =
  backgroundBridgeCandidateProfile
    "proof-by-omission-god-of-gaps-weakest-partial"
    claimNarrativeObservable
    personBehaviourObservable
    proofByOmissionGodOfGapsWeakest
    PARTIAL
    (missingTransportReceiptFalsifier ∷ counterMechanismFalsifier ∷ empiricalContradictionFalsifier ∷ [])
    proofByOmissionResidualOutlierCondition
    "Weakest receipt class: absence of a named mechanism is not support; the residual/outlier condition is named and remains PARTIAL."

proofByOmissionGodOfGapsBridge :
  BackgroundDistributionalBridge
proofByOmissionGodOfGapsBridge =
  backgroundCandidateToBridge proofByOmissionGodOfGapsCandidateProfile

canonicalBackgroundDistributionalBridges :
  List BackgroundDistributionalBridge
canonicalBackgroundDistributionalBridges =
  explicitTransportReceiptBridge
  ∷ wellEstablishedCausalChainBridge
  ∷ economyToPersonBehaviourDistributionalExample
  ∷ proofByOmissionGodOfGapsBridge
  ∷ []

------------------------------------------------------------------------
-- Explicit gates.

economyExampleNoEmpiricalTruthGate :
  BackgroundBridgePromotionGate
economyExampleNoEmpiricalTruthGate =
  backgroundBridgeAuthorityGate
    noEmpiricalTruthPromotionGate
    economyToPersonBehaviourDistributionalExample
    "The economy-to-person-behaviour bridge is an example receipt surface only."

backgroundDistributionNoCausationGate :
  BackgroundBridgePromotionGate
backgroundDistributionNoCausationGate =
  backgroundBridgeAuthorityGate
    noCausationFromBackgroundDistributionGate
    economyToPersonBehaviourDistributionalExample
    "Background distributional association does not promote causal transport."

godOfGapsNoPromotionGate :
  BackgroundBridgePromotionGate
godOfGapsNoPromotionGate =
  backgroundBridgeAuthorityGate
    noPersonBehaviourTruthPromotionGate
    proofByOmissionGodOfGapsBridge
    "Proof-by-omission and god-of-gaps readings remain weakest PARTIAL receipts."

policyAuthorityNoPromotionGate :
  BackgroundBridgePromotionGate
policyAuthorityNoPromotionGate =
  backgroundBridgeAuthorityGate
    noPolicyAuthorityPromotionGate
    economyToPersonBehaviourDistributionalExample
    "No policy authority is promoted from a background distributional bridge."

canonicalBackgroundBridgePromotionGates :
  List BackgroundBridgePromotionGate
canonicalBackgroundBridgePromotionGates =
  economyExampleNoEmpiricalTruthGate
  ∷ backgroundDistributionNoCausationGate
  ∷ godOfGapsNoPromotionGate
  ∷ policyAuthorityNoPromotionGate
  ∷ []

------------------------------------------------------------------------
-- Formal-lens example witnesses.

economyExampleFormalLensQualification :
  BackgroundFormalLensQualificationSurface
    economyToPersonBehaviourDistributionalCandidateProfile
economyExampleFormalLensQualification =
  backgroundFormalLensQualification
    economyToPersonBehaviourDistributionalCandidateProfile

economyExampleFormalLensProbabilisticReadingIsTrue :
  formalLensProbabilisticReading
    economyExampleFormalLensQualification
  ≡
  true
economyExampleFormalLensProbabilisticReadingIsTrue =
  refl

economyExampleFormalLensInformationReadingIsTrue :
  formalLensInformationReading
    economyExampleFormalLensQualification
  ≡
  true
economyExampleFormalLensInformationReadingIsTrue =
  refl

economyExampleFormalLensCategoryReadingIsTrue :
  formalLensCategoryReading
    economyExampleFormalLensQualification
  ≡
  true
economyExampleFormalLensCategoryReadingIsTrue =
  refl

economyExampleFormalLensFunctionalReadingIsTrue :
  formalLensFunctionalReading
    economyExampleFormalLensQualification
  ≡
  true
economyExampleFormalLensFunctionalReadingIsTrue =
  refl

economyExampleFormalLensPromotedIsFalse :
  formalLensPromoted
    economyExampleFormalLensQualification
  ≡
  false
economyExampleFormalLensPromotedIsFalse =
  refl

economyExampleFormalLensProbabilityTheoremAuthorityIsFalse :
  formalLensProbabilityTheoremAuthority
    economyExampleFormalLensQualification
  ≡
  false
economyExampleFormalLensProbabilityTheoremAuthorityIsFalse =
  refl

economyExampleFormalLensEmpiricalAdequacyAuthorityIsFalse :
  formalLensEmpiricalAdequacyAuthority
    economyExampleFormalLensQualification
  ≡
  false
economyExampleFormalLensEmpiricalAdequacyAuthorityIsFalse =
  refl

economyExampleFormalLensBackgroundDistributionAuthorityIsFalse :
  formalLensBackgroundDistributionAuthority
    economyExampleFormalLensQualification
  ≡
  false
economyExampleFormalLensBackgroundDistributionAuthorityIsFalse =
  refl

economyExampleFormalLensTransportAuthorityIsFalse :
  formalLensTransportAuthority
    economyExampleFormalLensQualification
  ≡
  false
economyExampleFormalLensTransportAuthorityIsFalse =
  refl

economyExampleFormalLensExternalAuthorityIsFalse :
  formalLensExternalAuthority
    economyExampleFormalLensQualification
  ≡
  false
economyExampleFormalLensExternalAuthorityIsFalse =
  refl

------------------------------------------------------------------------
-- Receipt equalities.

explicitTransportReceiptBridgeIsStrongest :
  bdbStrength explicitTransportReceiptBridge
  ≡
  explicitTransportReceiptStrongest
explicitTransportReceiptBridgeIsStrongest =
  refl

wellEstablishedCausalChainBridgeIsNamed :
  bdbName wellEstablishedCausalChainBridge
  ≡
  "well-established-causal-chain"
wellEstablishedCausalChainBridgeIsNamed =
  refl

economyExampleSourceIsEconomyObservable :
  bdbSource economyToPersonBehaviourDistributionalExample
  ≡
  economyObservable
economyExampleSourceIsEconomyObservable =
  refl

economyExampleTargetIsPersonBehaviourObservable :
  bdbTarget economyToPersonBehaviourDistributionalExample
  ≡
  personBehaviourObservable
economyExampleTargetIsPersonBehaviourObservable =
  refl

economyExampleDoesNotPromoteEmpiricalTruth :
  bdbPromoted economyToPersonBehaviourDistributionalExample
  ≡
  false
economyExampleDoesNotPromoteEmpiricalTruth =
  refl

proofByOmissionGodOfGapsIsWeakest :
  bdbStrength proofByOmissionGodOfGapsBridge
  ≡
  proofByOmissionGodOfGapsWeakest
proofByOmissionGodOfGapsIsWeakest =
  refl

proofByOmissionGodOfGapsResidualIsPARTIAL :
  bdbResidual proofByOmissionGodOfGapsBridge
  ≡
  PARTIAL
proofByOmissionGodOfGapsResidualIsPARTIAL =
  refl

proofByOmissionGodOfGapsPromotedIsFalse :
  bdbPromoted proofByOmissionGodOfGapsBridge
  ≡
  false
proofByOmissionGodOfGapsPromotedIsFalse =
  refl

proofByOmissionOutlierIsNamedResidual :
  outlierName (bdbOutlierCondition proofByOmissionGodOfGapsBridge)
  ≡
  "proof-by-omission-god-of-gaps-residual"
proofByOmissionOutlierIsNamedResidual =
  refl

allCanonicalBackgroundBridgeGatesPromotedFalse :
  List BackgroundBridgePromotionGate
allCanonicalBackgroundBridgeGatesPromotedFalse =
  canonicalBackgroundBridgePromotionGates

backgroundDistributionBridgeORCSLPGF :
  String
backgroundDistributionBridgeORCSLPGF =
  "O: BackgroundDistributionBridge; R: implicit/background distributional bridge receipts; C: BridgeStrength, ResidualName, Falsifier, OutlierCondition, promoted=false gates; S: explicit transport strongest, well-established causal chain named, proof-by-omission/god-of-gaps weakest PARTIAL; L: Economy.Observable -> PersonBehaviour.Observable is example-only and no empirical truth claim; P: no promotion, no causation, no policy authority gates; G: create isolated Interop receipt module only; F: Agda surface uses Bool/String/List/refl with no holes or assumed declarations."
