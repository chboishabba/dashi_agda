module DASHI.Reasoning.SFMVerifiedClaimPresentation where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- SOLFUNMEME / SFM verified-claim presentation layer.
--
-- AI proposal, kernel checking, exact encoding, diagnostic projection and
-- human explanation are represented as distinct authority surfaces.
------------------------------------------------------------------------

data KernelStatus : Set where
  kernelChecked kernelRejected kernelUnchecked kernelBlocked : KernelStatus

data ViewKind : Set where
  exactReversibleView lossyDiagnosticView schematicView decorativeView : ViewKind

data InterpretationStatus : Set where
  formalConsequence supportedInference analogy speculation satire : InterpretationStatus

data ProductMaturity : Set where
  idea prototype verifiedComponent reproduciblePipeline integratedProduct independentlyValidated : ProductMaturity

record FormalArtifact : Set where
  field
    artifactName : String
    signatureName : String
    assumptionSummary : String
    formalClaim : String
    proofObjectReference : String
    sourceModule : String
    sourceHash : String

record VerificationReceipt : Set where
  field
    artifact : FormalArtifact
    checker : String
    checkerVersion : String
    checkedClaim : String
    checkedAssumptions : String
    checkedAxioms : String
    dependencyHash : String
    status : KernelStatus
    placeholdersAbsentClaimed : Bool
    receiptId : String

record TheoremCard : Set where
  field
    cardName : String
    displayedClaim : String
    displayedAssumptions : String
    displayedAxioms : String
    displayedDependencies : String
    displayedQuantities : String
    sourceLocation : String
    verificationStatus : KernelStatus
    viewMetadata : String
    maturity : ProductMaturity

record CardFaithfulness
  (receipt : VerificationReceipt)
  (card : TheoremCard) : Set where
  field
    claimPreserved :
      TheoremCard.displayedClaim card ≡
      VerificationReceipt.checkedClaim receipt
    assumptionsPreserved :
      TheoremCard.displayedAssumptions card ≡
      VerificationReceipt.checkedAssumptions receipt
    axiomsPreserved :
      TheoremCard.displayedAxioms card ≡
      VerificationReceipt.checkedAxioms receipt
    statusPreserved :
      TheoremCard.verificationStatus card ≡
      VerificationReceipt.status receipt

record ExactView (Payload View : Set) : Set₁ where
  field
    encode : Payload → View
    decode : View → Payload
    decodeAfterEncode : ∀ payload → decode (encode payload) ≡ payload
    viewName : String
    provenanceVisible : Bool

record LossyView (Payload View : Set) : Set₁ where
  field
    project : Payload → View
    declaredLoss : String
    sourceReceipt : String
    injectiveClaimed : Bool
    diagnosticOnly : Bool

record SchematicView (Payload View : Set) : Set₁ where
  field
    render : Payload → View
    schematicContract : String
    arrowsAreFormalFunctionsClaimed : Bool
    interpretationStatus : InterpretationStatus

record ViewContract : Set where
  field
    kind : ViewKind
    sourceReceipt : String
    injective : Bool
    surjective : Bool
    reversible : Bool
    declaredLoss : String
    displayedAuthority : InterpretationStatus
    statusVisible : Bool

record VerifiedMultiViewIntegrity : Set₁ where
  field
    receipt : VerificationReceipt
    card : TheoremCard
    cardFaithful : CardFaithfulness receipt card
    viewContracts : List ViewContract
    everyFormalClaimTraceable : Bool
    everyExactViewHasRoundTripWitness : Bool
    everyLossyViewDeclaresLoss : Bool
    interpretationsVisiblySeparated : Bool
    displayedAuthorityDoesNotExceedSource : Bool

------------------------------------------------------------------------
-- Meme translation is allowed to generate candidates but not promotions.
------------------------------------------------------------------------

record MemeObject : Set where
  field
    vehicle : String
    intendedPayload : String
    provenance : String
    context : String
    transformationPermission : String
    receptionState : String

record ProductiveMemeTranslation : Set₁ where
  field
    source target : MemeObject
    declaredInvariant : String
    recordedLoss : String
    generatedFormalQuestion : String
    targetVerificationRule : String
    targetVerified : Bool
    literalIdentityClaimed : Bool

record SFMClaimState : Set where
  field
    kernel : KernelStatus
    view : ViewKind
    interpretation : InterpretationStatus
    product : ProductMaturity

record SFMViewAuthorityBoundary : Set where
  field
    aiGenerationEqualsVerification : Bool
    verificationEqualsExplanation : Bool
    exactCodecImpliesIntrinsicSemantics : Bool
    diagnosticPatternPromotesTheorem : Bool
    checkedComponentImpliesIntegratedProduct : Bool
    statusMustRemainVisible : Bool
    noRepresentationOutrunsSource : Bool
    boundaryNote : String

canonicalSFMViewAuthorityBoundary : SFMViewAuthorityBoundary
canonicalSFMViewAuthorityBoundary = record
  { aiGenerationEqualsVerification = false
  ; verificationEqualsExplanation = false
  ; exactCodecImpliesIntrinsicSemantics = false
  ; diagnosticPatternPromotesTheorem = false
  ; checkedComponentImpliesIntegratedProduct = false
  ; statusMustRemainVisible = true
  ; noRepresentationOutrunsSource = true
  ; boundaryNote =
      "AI proposes, kernels verify and SFM presents; reversible containers, diagnostic projections and interpretations keep distinct receipts."
  }

canonicalSFMFormalismReceipt : GenericReceipt.GenericReceipt
canonicalSFMFormalismReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "SFM verified-claim presentation formalism"
    "DASHI.Reasoning.SFMVerifiedClaimPresentation"
    "formal artefact / verification receipt / theorem card / multi-view contract"
    "separates generation, checking, exact views, lossy views, interpretation and product maturity"
    "concrete checker adapters, deterministic renderers and end-to-end theorem-card extraction remain downstream implementations"
    "agda -i . DASHI/Reasoning/SFMVerifiedClaimPresentation.agda"

canonicalSFMFormalismReceiptNonPromoting :
  GenericReceipt.promotesClaim canonicalSFMFormalismReceipt ≡ false
canonicalSFMFormalismReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse canonicalSFMFormalismReceipt
