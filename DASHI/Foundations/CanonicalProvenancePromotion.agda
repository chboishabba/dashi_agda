module DASHI.Foundations.CanonicalProvenancePromotion where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Canonical transport layer.
--
-- This file deliberately separates byte identity, semantic equivalence,
-- provenance, proof relations, residuals, receipts, and promotion.  No
-- signature, CID, parser success, or compression score is promoted to truth.

record Codec : Set where
  constructor mkCodec
  field
    name : String
    code : Nat

record Digest : Set where
  constructor mkDigest
  field
    algorithm : String
    bytes : String

record CID : Set where
  constructor cidv1
  field
    version : Nat
    contentCodec : Codec
    contentDigest : Digest

record CanonicalObject {ℓ : Level} (A : Set ℓ) : Set (lsuc ℓ) where
  constructor canonicalObject
  field
    value : A
    canonicalCodec : Codec
    canonicalBytes : String
    identity : CID

record RepresentationEquivalence
  {a b : Level}
  {A : Set a}
  {B : Set b}
  (left : CanonicalObject A)
  (right : CanonicalObject B)
  : Set (a ⊔ b) where
  constructor representationEquivalence
  field
    relationID : String
    witnessCID : CID

------------------------------------------------------------------------
-- Signed envelope and typed provenance edges.

record Principal : Set where
  constructor principal
  field
    identifier : String
    keyIdentifier : String

record SignatureDescriptor : Set where
  constructor signatureDescriptor
  field
    signer : Principal
    algorithm : String
    signedProjectionCID : CID
    signatureCID : CID

record ProofDescriptor : Set where
  constructor proofDescriptor
  field
    scheme : String
    relationID : String
    proofCID : CID
    publicInputsCID : CID
    verificationKeyCID : CID

record UncertaintyDescriptor : Set where
  constructor uncertaintyDescriptor
  field
    kind : String
    carrier : String
    estimate : String
    bounds : String
    calibration : String
    source : String
    method : String

record ClaimReference : Set where
  constructor claimReference
  field
    bodyCID : CID
    bodyCodec : Codec

record MessageEnvelope : Set where
  constructor messageEnvelope
  field
    messageType : String
    sender : Principal
    recipients : List String
    timestamp : String
    parents : List CID
    claim : ClaimReference
    proofs : List ProofDescriptor
    uncertainty : List UncertaintyDescriptor
    signatures : List SignatureDescriptor
    envelopeCID : CID

-- The relation carried by an edge is explicit.  A Merkle parent link alone
-- establishes a declared dependency, not the truth of that dependency.
data ProvenanceRelation : Set where
  derivedFrom : ProvenanceRelation
  cites : ProvenanceRelation
  revises : ProvenanceRelation
  contradicts : ProvenanceRelation
  aggregates : ProvenanceRelation
  projects : ProvenanceRelation
  receipts : ProvenanceRelation

record ProvenanceEdge : Set where
  constructor provenanceEdge
  field
    sourceCID : CID
    targetCID : CID
    relation : ProvenanceRelation
    witness : CID

------------------------------------------------------------------------
-- ITIR interpretation and residual lattice.

record PredicatePNF : Set where
  constructor predicatePNF
  field
    quantifiers : List String
    variables : List String
    authorities : List CID
    conditions : List String
    negations : List String
    scopeAndModality : List String

data Residual : Set where
  exact : Residual
  partial : Residual
  noTypedMeet : Residual
  contradiction : Residual

data Severity : Set where
  informational : Severity
  warning : Severity
  blocking : Severity
  inconsistent : Severity

severity : Residual → Severity
severity exact = informational
severity partial = warning
severity noTypedMeet = blocking
severity contradiction = inconsistent

record TypedInterpretation : Set where
  constructor typedInterpretation
  field
    source : CID
    normalForm : PredicatePNF
    authoritySurface : List CID
    residual : Residual

------------------------------------------------------------------------
-- Projection/fibre and canonical quotient interfaces.

record Projection {h o : Level} (H : Set h) (O : Set o) : Set (h ⊔ o) where
  constructor projection
  field
    observe : H → O

record FibreWitness
  {h o : Level}
  {H : Set h}
  {O : Set o}
  (π : Projection H O)
  (observable : O)
  : Set (h ⊔ o) where
  constructor fibreWitness
  field
    hidden : H
    projectsTo : Projection.observe π hidden ≡ observable

record Normalizer {ℓ : Level} (A : Set ℓ) : Set (lsuc ℓ) where
  constructor normalizer
  field
    normalize : A → A
    idempotent : (x : A) → normalize (normalize x) ≡ normalize x

------------------------------------------------------------------------
-- Receipts and promotion.

data ReceiptStatus : Set where
  witnessed : ReceiptStatus
  admissible : ReceiptStatus
  contractSatisfying : ReceiptStatus
  promotionReady : ReceiptStatus
  rejected : ReceiptStatus
  quarantined : ReceiptStatus

record Receipt : Set where
  constructor receipt
  field
    inputs : List CID
    operation : String
    environment : List String
    outputs : List CID
    traceCID : CID
    checks : List String
    status : ReceiptStatus

record PromotionObligations : Set where
  constructor promotionObligations
  field
    canonicalIdentityClosed : Bool
    admissibilityClosed : Bool
    residualClosed : Bool
    witnessesClosed : Bool
    validationClosed : Bool

allClosed : PromotionObligations → Bool
allClosed (promotionObligations true true true true true) = true
allClosed _ = false

data PromotionStatus : Set where
  raw : PromotionStatus
  parsed : PromotionStatus
  typed : PromotionStatus
  witnessedStatus : PromotionStatus
  admissibleStatus : PromotionStatus
  promoted : PromotionStatus
  rejectedStatus : PromotionStatus
  quarantinedStatus : PromotionStatus

promote : PromotionObligations → PromotionStatus
promote obligations with allClosed obligations
... | true = promoted
... | false = quarantinedStatus

allFiveObligationsPromote :
  promote (promotionObligations true true true true true) ≡ promoted
allFiveObligationsPromote = refl

missingCanonicalIdentityDoesNotPromote :
  promote (promotionObligations false true true true true) ≡ quarantinedStatus
missingCanonicalIdentityDoesNotPromote = refl

missingAdmissibilityDoesNotPromote :
  promote (promotionObligations true false true true true) ≡ quarantinedStatus
missingAdmissibilityDoesNotPromote = refl

missingResidualClosureDoesNotPromote :
  promote (promotionObligations true true false true true) ≡ quarantinedStatus
missingResidualClosureDoesNotPromote = refl

missingWitnessClosureDoesNotPromote :
  promote (promotionObligations true true true false true) ≡ quarantinedStatus
missingWitnessClosureDoesNotPromote = refl

missingValidationDoesNotPromote :
  promote (promotionObligations true true true true false) ≡ quarantinedStatus
missingValidationDoesNotPromote = refl

------------------------------------------------------------------------
-- Explicit boundary flags consumed by downstream bridge files.

data FormalismBoundaryFlag : Set where
  canonicalBytesAreCodecRelative : FormalismBoundaryFlag
  crossCodecSamenessRequiresWitness : FormalismBoundaryFlag
  cidIsNotAuthorship : FormalismBoundaryFlag
  signatureIsNotTruth : FormalismBoundaryFlag
  provenanceLinkIsNotRelationTruth : FormalismBoundaryFlag
  proofProvesOnlyNamedRelation : FormalismBoundaryFlag
  residualIsNotProbability : FormalismBoundaryFlag
  receiptIsNotTruthProof : FormalismBoundaryFlag
  mdlIsNotTruth : FormalismBoundaryFlag
  promotionRequiresClosure : FormalismBoundaryFlag

formalismBoundary : List FormalismBoundaryFlag
formalismBoundary =
  canonicalBytesAreCodecRelative
  ∷ crossCodecSamenessRequiresWitness
  ∷ cidIsNotAuthorship
  ∷ signatureIsNotTruth
  ∷ provenanceLinkIsNotRelationTruth
  ∷ proofProvesOnlyNamedRelation
  ∷ residualIsNotProbability
  ∷ receiptIsNotTruthProof
  ∷ mdlIsNotTruth
  ∷ promotionRequiresClosure
  ∷ []

record CanonicalProvenancePromotionKernel : Set₁ where
  field
    residualSeverity : Residual → Severity
    promotionDecision : PromotionObligations → PromotionStatus
    boundaryFlags : List FormalismBoundaryFlag
    fullyClosedPromotes :
      promotionDecision (promotionObligations true true true true true)
        ≡ promoted

canonicalProvenancePromotionKernel : CanonicalProvenancePromotionKernel
canonicalProvenancePromotionKernel = record
  { residualSeverity = severity
  ; promotionDecision = promote
  ; boundaryFlags = formalismBoundary
  ; fullyClosedPromotes = refl
  }
