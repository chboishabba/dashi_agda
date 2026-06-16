module DASHI.Core.HiddenLiftProjectionCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Core.AdapterCanonicalityCore as Adapter
import DASHI.Core.AuthorityNonPromotionCore as Authority
import DASHI.Core.BridgeRequirementCore as Bridge
import DASHI.Core.CandidateOnlyCore as Candidate
import DASHI.Core.FormalLensQualificationCore as Lens
import DASHI.Core.FormalLensVocabularyCore as Vocabulary
import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Generic hidden-lift / public-projection vocabulary.
--
-- This module is intentionally descriptive only.  It records the shape of a
-- private structured state, the public quotient/projection, a public operator,
-- and the hidden lift witness, while keeping every authority and security
-- claim fail-closed.

data PrivateCoordinateSpace : Set where
  structuredPrivateState :
    PrivateCoordinateSpace

  fiberIndexedPrivateState :
    PrivateCoordinateSpace

  residueIndexedPrivateState :
    PrivateCoordinateSpace

  namedPrivateCoordinateSpace :
    String →
    PrivateCoordinateSpace

data PublicQuotientSpace : Set where
  publicQuotientProjection :
    PublicQuotientSpace

  publicQuotientShadow :
    PublicQuotientSpace

  namedPublicQuotientSpace :
    String →
    PublicQuotientSpace

data ProjectionShadow : Set where
  shadowedProjection :
    ProjectionShadow

  shadowOnlyProjection :
    ProjectionShadow

  namedProjectionShadow :
    String →
    ProjectionShadow

data PublicOperator : Set where
  quotientOperator :
    PublicOperator

  publicMapOperator :
    PublicOperator

  namedPublicOperator :
    String →
    PublicOperator

data HiddenLiftWitness : Set where
  hiddenLiftWitnessCandidateOnly :
    HiddenLiftWitness

  hiddenLiftWitnessHidden :
    HiddenLiftWitness

  namedHiddenLiftWitness :
    String →
    HiddenLiftWitness

------------------------------------------------------------------------
-- Vocabulary layer.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

canonicalHiddenLiftProjectionVocabularyKinds :
  List Vocabulary.FormalLensKind
canonicalHiddenLiftProjectionVocabularyKinds =
  Vocabulary.Cryptographic
  ∷ Vocabulary.TrapdoorProjection
  ∷ Vocabulary.SecretWitness
  ∷ Vocabulary.QuotientResidue
  ∷ Vocabulary.HiddenLift
  ∷ Vocabulary.Commitment
  ∷ []

canonicalHiddenLiftProjectionVocabularyKindCount : Nat
canonicalHiddenLiftProjectionVocabularyKindCount =
  listCount canonicalHiddenLiftProjectionVocabularyKinds

record HiddenLiftProjectionVocabularyReceipt : Set where
  constructor mkHiddenLiftProjectionVocabularyReceipt
  field
    vocabularyKinds :
      List Vocabulary.FormalLensKind

    vocabularyKindsAreCanonical :
      vocabularyKinds ≡ canonicalHiddenLiftProjectionVocabularyKinds

    vocabularyKindCount :
      Nat

    vocabularyKindCountIsCanonical :
      vocabularyKindCount ≡ canonicalHiddenLiftProjectionVocabularyKindCount

    vocabularyCandidateOnly :
      Bool

    vocabularyCandidateOnlyIsTrue :
      vocabularyCandidateOnly ≡ true

    vocabularyPromoted :
      Bool

    vocabularyPromotedIsFalse :
      vocabularyPromoted ≡ false

open HiddenLiftProjectionVocabularyReceipt public

canonicalHiddenLiftProjectionVocabularyReceipt :
  HiddenLiftProjectionVocabularyReceipt
canonicalHiddenLiftProjectionVocabularyReceipt =
  mkHiddenLiftProjectionVocabularyReceipt
    canonicalHiddenLiftProjectionVocabularyKinds
    refl
    canonicalHiddenLiftProjectionVocabularyKindCount
    refl
    true
    refl
    false
    refl

record HiddenLiftProjectionSurface : Set where
  constructor mkHiddenLiftProjectionSurface
  field
    surfaceLabel :
      String

    surfaceOwner :
      String

    surfaceName :
      String

    privateCoordinateSpace :
      PrivateCoordinateSpace

    publicQuotientSpace :
      PublicQuotientSpace

    projectionShadow :
      ProjectionShadow

    publicOperator :
      PublicOperator

    hiddenLiftWitness :
      HiddenLiftWitness

    surfaceLens :
      Lens.FormalLens

    surfaceRole :
      Lens.QualificationRole

    surfaceBoundary :
      Lens.ResidualBoundaryLabel

    surfaceStatement :
      String

    surfaceRemainingGap :
      String

    surfaceCandidateOnly :
      Bool

    surfacePromoted :
      Bool

    surfaceAuthorityPromotion :
      Bool

open HiddenLiftProjectionSurface public

hiddenLiftProjectionVocabularyKinds :
  HiddenLiftProjectionSurface →
  List Vocabulary.FormalLensKind
hiddenLiftProjectionVocabularyKinds _ =
  canonicalHiddenLiftProjectionVocabularyKinds

hiddenLiftProjectionVocabularyKindCount :
  HiddenLiftProjectionSurface →
  Nat
hiddenLiftProjectionVocabularyKindCount _ =
  canonicalHiddenLiftProjectionVocabularyKindCount

record CorrectnessReceipt : Set where
  constructor mkCorrectnessReceipt
  field
    correctnessLabel :
      String

    correctnessStatement :
      String

    correctnessCandidateOnly :
      Bool

    correctnessPromoted :
      Bool

    correctnessAuthorityPromotion :
      Bool

    correctnessCandidateOnlyIsTrue :
      correctnessCandidateOnly ≡ true

    correctnessPromotedIsFalse :
      correctnessPromoted ≡ false

    correctnessAuthorityPromotionIsFalse :
      correctnessAuthorityPromotion ≡ false

open CorrectnessReceipt public

record SecurityGap : Set where
  constructor mkSecurityGap
  field
    securityGapLabel :
      String

    securityGapStatement :
      String

    noSecurityProof :
      Bool

    noInversionHardnessProof :
      Bool

    noCryptographicSoundness :
      Bool

    noProtocolAuthority :
      Bool

    noSecurityProofIsTrue :
      noSecurityProof ≡ true

    noInversionHardnessProofIsTrue :
      noInversionHardnessProof ≡ true

    noCryptographicSoundnessIsTrue :
      noCryptographicSoundness ≡ true

    noProtocolAuthorityIsTrue :
      noProtocolAuthority ≡ true

open SecurityGap public

record FiberCollapseBoundary : Set where
  constructor mkFiberCollapseBoundary
  field
    fiberCollapseBoundaryLabel :
      String

    fiberCollapseBoundaryStatement :
      String

    fiberCollapseBoundaryOpen :
      Bool

    vulnerabilityBoundaryOpen :
      Bool

    fiberCollapseBoundaryOpenIsTrue :
      fiberCollapseBoundaryOpen ≡ true

    vulnerabilityBoundaryOpenIsTrue :
      vulnerabilityBoundaryOpen ≡ true

open FiberCollapseBoundary public

record HiddenLiftProjectionEvidence : Set where
  constructor mkHiddenLiftProjectionEvidence
  field
    candidateOnlyRow :
      Candidate.CandidateOnlyRow

    candidateOnlyReceipt :
      Candidate.CandidateOnlyReceipt candidateOnlyRow

    authorityBundle :
      Authority.AuthorityNonPromotionBundle

    bridgeCoreReceipt :
      Bridge.BridgeRequirementCoreReceipt

    projectionShadowAdapterReceipt :
      Adapter.AdapterCanonicalityReceipt
        ProjectionShadow
        shadowedProjection

    genericReceipt :
      GenericReceipt.GenericReceipt

open HiddenLiftProjectionEvidence public

record HiddenLiftProjectionReceipt
  (surface : HiddenLiftProjectionSurface) :
  Set where
  constructor mkHiddenLiftProjectionReceipt
  field
    surfaceCandidateOnlyIsTrue :
      surfaceCandidateOnly surface ≡ true

    surfacePromotedIsFalse :
      surfacePromoted surface ≡ false

    surfaceAuthorityPromotionIsFalse :
      surfaceAuthorityPromotion surface ≡ false

    correctnessReceipt :
      CorrectnessReceipt

    securityGap :
      SecurityGap

    fiberCollapseBoundary :
      FiberCollapseBoundary

    evidence :
      HiddenLiftProjectionEvidence

open HiddenLiftProjectionReceipt public

------------------------------------------------------------------------
-- Canonical candidate, bridge, adapter, and receipt values.

canonicalHiddenLiftProjectionCandidateRow :
  Candidate.CandidateOnlyRow
canonicalHiddenLiftProjectionCandidateRow =
  Candidate.mkCandidateOnlyRow
    "hidden lift projection candidate"
    "DASHI.Core.HiddenLiftProjectionCore"
    "canonicalHiddenLiftProjectionCandidateRow"
    Candidate.operatorCandidateKind
    Candidate.operatorCandidateOnlyStatus
    "private structured state, public quotient space, public operator, and hidden lift witness are tracked as candidate-only vocabulary"
    "no RSA-specific authority, inversion-hardness proof, or cryptographic soundness is supplied"

canonicalHiddenLiftProjectionCandidateReceipt :
  Candidate.CandidateOnlyReceipt
    canonicalHiddenLiftProjectionCandidateRow
canonicalHiddenLiftProjectionCandidateReceipt =
  Candidate.mkCandidateOnlyReceipt
    canonicalHiddenLiftProjectionCandidateRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalHiddenLiftProjectionAuthorityBundle :
  Authority.AuthorityNonPromotionBundle
canonicalHiddenLiftProjectionAuthorityBundle =
  Authority.canonicalAuthorityNonPromotionBundle

canonicalHiddenLiftProjectionBridgeRow :
  Bridge.BridgeRequirementRow
canonicalHiddenLiftProjectionBridgeRow =
  Bridge.canonicalBridgeRequirementRow
    "private structured state"
    "public quotient/projection"
    Bridge.bridgeSuppliedCandidateOnly
    true
    true
    true

canonicalHiddenLiftProjectionBridgeReceipt :
  Bridge.BridgeRequirementRowReceipt
    canonicalHiddenLiftProjectionBridgeRow
canonicalHiddenLiftProjectionBridgeReceipt =
  Bridge.bridgeRequirementRowReceipt refl refl refl

canonicalHiddenLiftProjectionBridgeCoreReceipt :
  Bridge.BridgeRequirementCoreReceipt
canonicalHiddenLiftProjectionBridgeCoreReceipt =
  Bridge.canonicalBridgeRequirementCoreReceipt

canonicalProjectionShadowAdapterReceipt :
  Adapter.AdapterCanonicalityReceipt
    ProjectionShadow
    shadowedProjection
canonicalProjectionShadowAdapterReceipt =
  Adapter.mkCanonicalAdapterReceipt
    "hidden lift projection shadow adapter"
    "DASHI.Core.HiddenLiftProjectionCore"
    "shadowedProjection"
    Adapter.genericAdapterKind
    shadowedProjection

canonicalHiddenLiftProjectionGenericReceipt :
  GenericReceipt.GenericReceipt
canonicalHiddenLiftProjectionGenericReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "hidden lift projection core"
    "DASHI.Core.HiddenLiftProjectionCore"
    "canonicalHiddenLiftProjectionSurface"
    "private structured state, public quotient space, projection shadow, public operator, hidden lift witness, correctness receipt, and fail-closed security boundary are centralized"
    "this module does not provide RSA-specific security proof, inversion-hardness proof, cryptographic soundness, or protocol authority"
    "agda -i . DASHI/Core/HiddenLiftProjectionCore.agda"

canonicalHiddenLiftProjectionSurface :
  HiddenLiftProjectionSurface
canonicalHiddenLiftProjectionSurface =
  mkHiddenLiftProjectionSurface
    "hidden lift projection core"
    "DASHI.Core.HiddenLiftProjectionCore"
    "canonicalHiddenLiftProjectionSurface"
    structuredPrivateState
    publicQuotientProjection
    shadowedProjection
    quotientOperator
    hiddenLiftWitnessCandidateOnly
    Lens.Information
    Lens.sourceLensRole
    Lens.explicitResidualBoundary
    "private structured state is described through a public quotient and a public operator"
    "security claims stay outside this core"
    true
    false
    false

canonicalHiddenLiftProjectionVocabularyKindsForSurface :
  List Vocabulary.FormalLensKind
canonicalHiddenLiftProjectionVocabularyKindsForSurface =
  hiddenLiftProjectionVocabularyKinds canonicalHiddenLiftProjectionSurface

canonicalHiddenLiftProjectionVocabularyKindCountForSurface :
  Nat
canonicalHiddenLiftProjectionVocabularyKindCountForSurface =
  hiddenLiftProjectionVocabularyKindCount canonicalHiddenLiftProjectionSurface

canonicalHiddenLiftProjectionCorrectnessReceipt :
  CorrectnessReceipt
canonicalHiddenLiftProjectionCorrectnessReceipt =
  mkCorrectnessReceipt
    "hidden lift projection correctness receipt"
    "the receipt records candidate-only shape compatibility and closes authority promotion"
    true
    false
    false
    refl
    refl
    refl

canonicalHiddenLiftProjectionSecurityGap :
  SecurityGap
canonicalHiddenLiftProjectionSecurityGap =
  mkSecurityGap
    "hidden lift projection security gap"
    "no security proof, inversion-hardness proof, cryptographic soundness, or protocol authority is supplied"
    true
    true
    true
    true
    refl
    refl
    refl
    refl

canonicalHiddenLiftProjectionFiberCollapseBoundary :
  FiberCollapseBoundary
canonicalHiddenLiftProjectionFiberCollapseBoundary =
  mkFiberCollapseBoundary
    "hidden lift projection fiber-collapse boundary"
    "fiber collapse and vulnerability are recorded as a boundary surface only"
    true
    true
    refl
    refl

canonicalHiddenLiftProjectionEvidence :
  HiddenLiftProjectionEvidence
canonicalHiddenLiftProjectionEvidence =
  mkHiddenLiftProjectionEvidence
    canonicalHiddenLiftProjectionCandidateRow
    canonicalHiddenLiftProjectionCandidateReceipt
    canonicalHiddenLiftProjectionAuthorityBundle
    canonicalHiddenLiftProjectionBridgeCoreReceipt
    canonicalProjectionShadowAdapterReceipt
    canonicalHiddenLiftProjectionGenericReceipt

canonicalHiddenLiftProjectionReceipt :
  HiddenLiftProjectionReceipt canonicalHiddenLiftProjectionSurface
canonicalHiddenLiftProjectionReceipt =
  mkHiddenLiftProjectionReceipt
    refl
    refl
    refl
    canonicalHiddenLiftProjectionCorrectnessReceipt
    canonicalHiddenLiftProjectionSecurityGap
    canonicalHiddenLiftProjectionFiberCollapseBoundary
    canonicalHiddenLiftProjectionEvidence
