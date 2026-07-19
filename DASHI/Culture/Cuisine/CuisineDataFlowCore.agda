module DASHI.Culture.Cuisine.CuisineDataFlowCore where

open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source -> span -> atom -> normalized atom -> surface -> contradiction
-- handling -> promotion.  Promotion is proof-bearing and fail-closed.
------------------------------------------------------------------------

data EvidenceLane : Set where
  cookbookLane          : EvidenceLane
  archiveLane           : EvidenceLane
  oralHistoryLane       : EvidenceLane
  practitionerLane      : EvidenceLane
  communityLane         : EvidenceLane
  sensoryPanelLane      : EvidenceLane
  instrumentalLane      : EvidenceLane
  nutritionDatabaseLane : EvidenceLane
  agriculturalLane      : EvidenceLane
  scholarlyLane         : EvidenceLane
  dinerMemoryLane       : EvidenceLane

record SourceReceipt : Set where
  field
    receiptId    : String
    title        : String
    locator      : String
    date         : String
    evidenceLane : EvidenceLane
    licence      : String

open SourceReceipt public

record ExtractedSpan (receipt : SourceReceipt) : Set where
  field
    spanText    : String
    spanLocator : String

open ExtractedSpan public

data PredicateRole : Set where
  containsRole          : PredicateRole
  excludesRole          : PredicateRole
  derivesFromRole       : PredicateRole
  transformsRole        : PredicateRole
  evokesRole            : PredicateRole
  hasProfileRole        : PredicateRole
  hasNutrientRole       : PredicateRole
  sourcedFromRole       : PredicateRole
  variantOfRole         : PredicateRole
  belongsToMovementRole : PredicateRole

record PredicateAtom : Set where
  field
    subject   : String
    predicate : PredicateRole
    object    : String
    sourceId  : String

open PredicateAtom public

record NormalizedAtom : Set where
  field
    rawAtom           : PredicateAtom
    normalizedSubject : String
    normalizedObject  : String
    ontologyLocator   : String

open NormalizedAtom public

data SurfaceKind : Set where
  identitySurface    : SurfaceKind
  techniqueSurface   : SurfaceKind
  recipeRouteSurface : SurfaceKind
  lineageSurface     : SurfaceKind
  nutritionSurface   : SurfaceKind
  provenanceSurface  : SurfaceKind
  qualitativeSurface : SurfaceKind
  movementSurface    : SurfaceKind
  safetySurface      : SurfaceKind
  authoritySurface   : SurfaceKind
  variantSurface     : SurfaceKind

record SurfaceClaim : Set where
  field
    surface   : SurfaceKind
    atom      : NormalizedAtom
    claimText : String

open SurfaceClaim public

data RelationBetweenClaims : Set where
  agrees             : RelationBetweenClaims
  refines            : RelationBetweenClaims
  contextualizes     : RelationBetweenClaims
  conflicts          : RelationBetweenClaims
  unresolvedRelation : RelationBetweenClaims

record ClaimRelation : Set where
  field
    leftClaim  : SurfaceClaim
    rightClaim : SurfaceClaim
    relation   : RelationBetweenClaims
    note       : String

open ClaimRelation public

record PromotionPolicy : Set₁ where
  field
    AcceptsSource          : SurfaceClaim → SourceReceipt → Set
    NormalizationValid     : SurfaceClaim → Set
    ContradictionsResolved : SurfaceClaim → List ClaimRelation → Set

open PromotionPolicy public

record PromotionEvidence
    (policy : PromotionPolicy)
    (claim : SurfaceClaim) : Set₁ where
  field
    sourceReceipt         : SourceReceipt
    relatedClaims         : List ClaimRelation
    sourceAccepted        : AcceptsSource policy claim sourceReceipt
    normalizationChecked  : NormalizationValid policy claim
    contradictionsHandled : ContradictionsResolved policy claim relatedClaims

open PromotionEvidence public

record PromotedClaim (policy : PromotionPolicy) : Set₁ where
  constructor promoteClaim
  field
    promotedSurfaceClaim : SurfaceClaim
    promotionEvidence    : PromotionEvidence policy promotedSurfaceClaim

open PromotedClaim public

promote :
  (policy : PromotionPolicy) →
  (claim : SurfaceClaim) →
  PromotionEvidence policy claim →
  PromotedClaim policy
promote policy claim evidence = promoteClaim claim evidence

recoverPromotionEvidence :
  {policy : PromotionPolicy} →
  (promoted : PromotedClaim policy) →
  PromotionEvidence policy (promotedSurfaceClaim promoted)
recoverPromotionEvidence = promotionEvidence

record CuisinePipeline : Set₁ where
  field
    ingest           : SourceReceipt → Set
    extract          : (receipt : SourceReceipt) → ingest receipt → ExtractedSpan receipt
    atomize          : {receipt : SourceReceipt} → ExtractedSpan receipt → PredicateAtom
    normalize        : PredicateAtom → NormalizedAtom
    constructSurface : NormalizedAtom → SurfaceClaim
    compareClaims    : SurfaceClaim → SurfaceClaim → ClaimRelation

open CuisinePipeline public

------------------------------------------------------------------------
-- Qualitative evidence plurality is explicit: panel, instrument, memory,
-- practice, and community testimony can support different claim types.
------------------------------------------------------------------------

record MultimodalQualitativeBundle : Set where
  field
    sensoryPanelReceipts : List SourceReceipt
    instrumentalReceipts : List SourceReceipt
    practitionerReceipts : List SourceReceipt
    memoryReceipts       : List SourceReceipt
    communityReceipts    : List SourceReceipt

open MultimodalQualitativeBundle public
