module DASHI.Cognition.PNF.ITIRRelationalInterlinguaConsumerFibreExact where

-- ITIR general shared relational interlingua, domain-agnostic.
-- Witnesses originate from the existing PNF and source-revision owners.
-- The indexed comparison is a *query-relative candidate comparison*,
-- not a new ontology, world-truth admission, or lossless parser theorem.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

data Family : Set where
  wikidata wikipedia legal biomedical transcript chat
    structuredKnowledge animalObservation other : Family

data Polarity : Set where
  supports counters undetermined : Polarity

data RelationStatus : Set where
  exactCandidateShape licensedCompatible compatibleQualification
    polarityConflictCandidate partialResidual missingTypedMeet
    undeterminedComparison : RelationStatus

data ResidualKind : Set where
  missingRole unalignedFiller unalignedPredicate unalignedType
    scopeMismatch timeMismatch modalityMismatch quantifierMismatch
    attributionMismatch ontologyMismatch languageMismatch
    missingProvenance unresolvedPolarity : ResidualKind

record SourceObservation : Set where
  constructor source-observation
  field
    sourceRevisionRef : String
    spanRef : String
    observationRef : String
    producerRef : String
    family : Family
    predicateCandidateRef : String
    roleBindingRefs : List String
    candidateTypeRefs : List String
    contextRefs : List String
    provenanceRefs : List String
    polarity : Polarity
    candidateOnly : Bool
    candidateOnlyTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    authorityFalse : createsSemanticAuthority ≡ false
    claimTruthPromoted : Bool
    truthFalse : claimTruthPromoted ≡ false

open SourceObservation public

-- An alignment licence is specific to a consumer. A direct matching
-- identifier or shared extension does not supply the licence.
record ConsumerLicence : Set where
  constructor consumer-licence
  field
    consumerRef : String
    operationRef : String
    alignmentWitnessRef : String
    licensingReceiptRef : String

open ConsumerLicence public

record RelationalResidual : Set where
  constructor relational-residual
  field
    kind : ResidualKind
    leftCoordinateRef : String
    rightCoordinateRef : String
    missingObligationRef : String

open RelationalResidual public

-- One typed comparison fibre. The status is not a total order:
-- support, counter-support, missingness and reviewability coexist.
record ConsumerComparison
  (left right : SourceObservation) (consumer : ConsumerLicence)
  : Set where
  constructor consumer-comparison
  field
    status : RelationStatus
    checkedRoleRefs : List String
    usedAlignmentWitnessRefs : List String
    residuals : List RelationalResidual
    supportRefs : List String
    counterSupportRefs : List String
    unknownRefs : List String
    createsSourceIdentity : Bool
    sourceIdentityFalse : createsSourceIdentity ≡ false
    createsPropositionTruth : Bool
    propositionTruthFalse : createsPropositionTruth ≡ false
    createsIndependentWitness : Bool
    independenceFalse : createsIndependentWitness ≡ false
    appliesRepair : Bool
    repairFalse : appliesRepair ≡ false

open ConsumerComparison public

-- In the real pipeline, the shared ordinary-language and structured
-- presentations inhabit separate source-indexed fibres. A consumer may
-- inspect the comparison; no projection can promote its truth flags.
comparisonNeverMergesSources :
  ∀ {left right consumer}
  (c : ConsumerComparison left right consumer) →
  ConsumerComparison.createsSourceIdentity c ≡ false
comparisonNeverMergesSources = ConsumerComparison.sourceIdentityFalse

comparisonNeverPaysTruth :
  ∀ {left right consumer}
  (c : ConsumerComparison left right consumer) →
  ConsumerComparison.createsPropositionTruth c ≡ false
comparisonNeverPaysTruth = ConsumerComparison.propositionTruthFalse

comparisonNeverPaysIndependence :
  ∀ {left right consumer}
  (c : ConsumerComparison left right consumer) →
  ConsumerComparison.createsIndependentWitness c ≡ false
comparisonNeverPaysIndependence = ConsumerComparison.independenceFalse

-- No implicit constructor exists for the following forbidden transports.
-- These empty types are policy boundaries, NOT empirical proofs that
-- all Rust callers enforce them. Runtime ownership checks are separate.
data IdenticalWordsProveSamePredicate : Set where
data SameMemberSetProvesSameOntologyType : Set where
data SharedQidProvesArticleParity : Set where
data CommonPnfFingerprintProvesClaimTruth : Set where
data NegativeReportErasesPositiveSource : Set where
data CandidateReviewAuthorizesDomainRepair : Set where

wordsDoNotPayPredicate : IdenticalWordsProveSamePredicate → ⊥
wordsDoNotPayPredicate ()

extensionalSimilarityNotTypeEquivalence :
  SameMemberSetProvesSameOntologyType → ⊥
extensionalSimilarityNotTypeEquivalence ()

qidNotParity : SharedQidProvesArticleParity → ⊥
qidNotParity ()

pnfCandidateNotTruth : CommonPnfFingerprintProvesClaimTruth → ⊥
pnfCandidateNotTruth ()

preserveCounterSupport : NegativeReportErasesPositiveSource → ⊥
preserveCounterSupport ()

reviewNotRepairAuthority : CandidateReviewAuthorizesDomainRepair → ⊥
reviewNotRepairAuthority ()
