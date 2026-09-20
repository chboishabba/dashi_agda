module DASHI.Law.SensibLawNativeLegalFollowCLIExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.WaltonsEstoppelOperationalPipelineExact as Waltons
import DASHI.Law.SensibLawOALCLegalFollowAttributionSnowballExact as OALC
import DASHI.Law.SensibLawOALCJudgmentCitationSnowballExact as Judgment
import DASHI.Law.WaltonsReviewedPropositionPaymentExact as Review

------------------------------------------------------------------------
-- NATIVE LEGALFOLLOW CLI OWNERSHIP
--
-- Rust orchestration may sequence already-typed owners.  It does not become a
-- new semantic authority.  JSON remains an inspection/review/persistence
-- surface; Python compatibility entrypoints may delegate to the native CLI but
-- own no LegalFollow, acquisition, review, payment, WrongType, treatment or
-- genealogy semantics.
------------------------------------------------------------------------

data NativeLegalFollowCommand : Set where
  acquireCase : NativeLegalFollowCommand
  materialiseReviewQueue : NativeLegalFollowCommand
  prepareParagraphReview : NativeLegalFollowCommand
  compileParagraphReview : NativeLegalFollowCommand
  inspectWrongTypeFrontier : NativeLegalFollowCommand
  planCitedByTraversal : NativeLegalFollowCommand
  importCitedByCandidates : NativeLegalFollowCommand
  reacquireCitedByCase : NativeLegalFollowCommand
  prepareTreatmentReview : NativeLegalFollowCommand
  compileTreatmentReview : NativeLegalFollowCommand
  buildTreatmentGenealogy : NativeLegalFollowCommand
  acquireCullenLegislation : NativeLegalFollowCommand
  materialiseCullenSectionSlices : NativeLegalFollowCommand
  runCullenPnfParser : NativeLegalFollowCommand
  planAustralianContractsLandscape : NativeLegalFollowCommand
  inspectAustralianContractsLandscape : NativeLegalFollowCommand
  acquireAustralianContractsLandscapeSources : NativeLegalFollowCommand
  expandAustralianContractsLandscape : NativeLegalFollowCommand
  prepareContractAuthorityIdentityReview : NativeLegalFollowCommand
  finalizeContractAuthorityIdentityReview : NativeLegalFollowCommand
  compileContractAuthorityIdentityReview : NativeLegalFollowCommand
  compileReviewedContractPropositionHops : NativeLegalFollowCommand
  compileReviewedContractTreatmentHops : NativeLegalFollowCommand
  syncWaltonsReviewedHopsToS14 : NativeLegalFollowCommand
  runAustralianContractsThreeHopAdaptiveFixture : NativeLegalFollowCommand
  prepareWaltonsLiveOalcPipeline : NativeLegalFollowCommand
  resumeWaltonsAfterParagraphReview : NativeLegalFollowCommand
  resumeWaltonsWithCitedByProviderResults : NativeLegalFollowCommand
  resumeWaltonsAfterAuthorityIdentityReview : NativeLegalFollowCommand
  resumeWaltonsAfterTreatmentReview : NativeLegalFollowCommand

data OrchestrationOwner : Set where
  nativeRustCli : OrchestrationOwner
  pythonCompatibilityShim : OrchestrationOwner
  jsonReviewSurface : OrchestrationOwner

canonicalOrchestrationOwner : OrchestrationOwner
canonicalOrchestrationOwner = nativeRustCli

pythonCompatibilityOwnerIsNotCanonical :
  canonicalOrchestrationOwner ≡ pythonCompatibilityShim → ⊥
pythonCompatibilityOwnerIsNotCanonical ()

jsonReviewSurfaceIsNotCanonical :
  canonicalOrchestrationOwner ≡ jsonReviewSurface → ⊥
jsonReviewSurfaceIsNotCanonical ()

------------------------------------------------------------------------
-- Existing semantic owners remain upstream/downstream.
------------------------------------------------------------------------

WaltonsPipelineBoundary : Set
WaltonsPipelineBoundary = Waltons.WaltonsOperationalPipelineBoundary

waltonsPipelineBoundaryPaid : WaltonsPipelineBoundary
waltonsPipelineBoundaryPaid =
  Waltons.canonicalWaltonsOperationalPipelineBoundary

OalcBoundary : Set
OalcBoundary = OALC.OalcLegalFollowAttributionBoundary

oalcBoundaryPaid : OalcBoundary
oalcBoundaryPaid =
  OALC.canonicalOalcLegalFollowAttributionBoundary

JudgmentBoundary : Set
JudgmentBoundary = Judgment.OalcJudgmentCitationSnowballBoundary

judgmentBoundaryPaid : JudgmentBoundary
judgmentBoundaryPaid =
  Judgment.canonicalOalcJudgmentCitationSnowballBoundary

ReviewBoundary : Set
ReviewBoundary = Review.WaltonsReviewedPropositionPaymentBoundary

reviewBoundaryPaid : ReviewBoundary
reviewBoundaryPaid =
  Review.canonicalWaltonsReviewedPropositionPaymentBoundary

------------------------------------------------------------------------
-- Parser subprocesses may produce observations, but never own legal semantics.
------------------------------------------------------------------------

data ParserProducerRole : Set where
  sourceObservationProducer : ParserProducerRole

spacyParserRole : ParserProducerRole
spacyParserRole = sourceObservationProducer

data SpacyParserAutomaticallyLegalAuthority : Set where
data SpacyParserAutomaticallyLegalConstruction : Set where
data SectionSliceAutomaticallyHistoricalLaw : Set where

spacyDoesNotCreateLegalAuthority :
  SpacyParserAutomaticallyLegalAuthority → ⊥
spacyDoesNotCreateLegalAuthority ()

spacyDoesNotCreateLegalConstruction :
  SpacyParserAutomaticallyLegalConstruction → ⊥
spacyDoesNotCreateLegalConstruction ()

latestKnownSectionDoesNotBecomeHistoricalLaw :
  SectionSliceAutomaticallyHistoricalLaw → ⊥
latestKnownSectionDoesNotBecomeHistoricalLaw ()

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data NativeCliAutomaticallyLegalAuthority : Set where
data PythonWrapperOwnsLegalSemantics : Set where
data JsonArtifactIsSemanticCommandAbi : Set where
data JsonReviewFileAutomaticallyReviewerDecision : Set where
data JsonReceiptAutomaticallyClaimTruth : Set where
data CliSequenceAutomaticallyPaysOpenResidual : Set where
data PinnedOalcStreamingAutomaticallyLegalTruth : Set where
data ReviewedHopJsonBecomesCanonicalSemanticTransport : Set where

nativeCliDoesNotCreateAuthority :
  NativeCliAutomaticallyLegalAuthority → ⊥
nativeCliDoesNotCreateAuthority ()

pythonWrapperDoesNotOwnLegalSemantics :
  PythonWrapperOwnsLegalSemantics → ⊥
pythonWrapperDoesNotOwnLegalSemantics ()

jsonIsNotSemanticCommandAbi :
  JsonArtifactIsSemanticCommandAbi → ⊥
jsonIsNotSemanticCommandAbi ()

jsonReviewDoesNotCreateDecision :
  JsonReviewFileAutomaticallyReviewerDecision → ⊥
jsonReviewDoesNotCreateDecision ()

jsonReceiptDoesNotCreateTruth :
  JsonReceiptAutomaticallyClaimTruth → ⊥
jsonReceiptDoesNotCreateTruth ()

cliSequenceDoesNotPayResidual :
  CliSequenceAutomaticallyPaysOpenResidual → ⊥
cliSequenceDoesNotPayResidual ()

pinnedStreamDoesNotCreateLegalTruth :
  PinnedOalcStreamingAutomaticallyLegalTruth → ⊥
pinnedStreamDoesNotCreateLegalTruth ()

reviewedHopJsonDoesNotBecomeCanonicalSemanticTransport :
  ReviewedHopJsonBecomesCanonicalSemanticTransport → ⊥
reviewedHopJsonDoesNotBecomeCanonicalSemanticTransport ()

record NativeLegalFollowCliBoundary : Set where
  constructor nativeLegalFollowCliBoundary
  field
    rustOwnsCanonicalOrchestration : Bool
    rustOwnsCanonicalOrchestrationIsTrue :
      rustOwnsCanonicalOrchestration ≡ true

    pythonIsCompatibilityOnly : Bool
    pythonIsCompatibilityOnlyIsTrue :
      pythonIsCompatibilityOnly ≡ true

    pythonOwnsLegalSemantics : Bool
    pythonOwnsLegalSemanticsIsFalse :
      pythonOwnsLegalSemantics ≡ false

    jsonIsReviewAndReceiptSurface : Bool
    jsonIsReviewAndReceiptSurfaceIsTrue :
      jsonIsReviewAndReceiptSurface ≡ true

    jsonIsSemanticCommandTransport : Bool
    jsonIsSemanticCommandTransportIsFalse :
      jsonIsSemanticCommandTransport ≡ false

    nativePinnedOalcStreamExists : Bool
    nativePinnedOalcStreamExistsIsTrue :
      nativePinnedOalcStreamExists ≡ true

    cullenLegalOrchestrationIsNativeRust : Bool
    cullenLegalOrchestrationIsNativeRustIsTrue :
      cullenLegalOrchestrationIsNativeRust ≡ true

    contractsLandscapeOrchestrationIsNativeRust : Bool
    contractsLandscapeOrchestrationIsNativeRustIsTrue :
      contractsLandscapeOrchestrationIsNativeRust ≡ true

    reviewedContractHopCompilationIsNativeRust : Bool
    reviewedContractHopCompilationIsNativeRustIsTrue :
      reviewedContractHopCompilationIsNativeRust ≡ true

    reviewedHopTransportIsTypedRust : Bool
    reviewedHopTransportIsTypedRustIsTrue :
      reviewedHopTransportIsTypedRust ≡ true

    reviewedHopJsonIsCanonicalSemanticTransport : Bool
    reviewedHopJsonIsCanonicalSemanticTransportIsFalse :
      reviewedHopJsonIsCanonicalSemanticTransport ≡ false

    spacyIsParserProducerOnly : Bool
    spacyIsParserProducerOnlyIsTrue :
      spacyIsParserProducerOnly ≡ true

    nativeCliCreatesLegalAuthority : Bool
    nativeCliCreatesLegalAuthorityIsFalse :
      nativeCliCreatesLegalAuthority ≡ false

canonicalNativeLegalFollowCliBoundary :
  NativeLegalFollowCliBoundary
canonicalNativeLegalFollowCliBoundary =
  nativeLegalFollowCliBoundary
    true refl
    true refl
    false refl
    true refl
    false refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    true refl
    false refl
