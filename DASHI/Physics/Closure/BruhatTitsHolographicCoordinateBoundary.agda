module DASHI.Physics.Closure.BruhatTitsHolographicCoordinateBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Bruhat-Tits / holographic-coordinate boundary receipt.
--
-- This module records a finite coordinate and regularization boundary for
-- a toy Bruhat-Tits tree projection.  The tree is used as coordinate
-- bookkeeping for a finite cutoff and not as a physical ontology.
-- Literature rows are source context only; they do not promote any DASHI
-- physical, holographic QFT, or Clay claim.

data Depth : Set where
  depth0 :
    Depth

  depth1 :
    Depth

  depth2 :
    Depth

canonicalDepths : List Depth
canonicalDepths =
  depth0
  ∷ depth1
  ∷ depth2
  ∷ []

depthCount : Nat
depthCount =
  3

data Branch : Set where
  trunk :
    Branch

  left :
    Branch

  right :
    Branch

data BoundaryPoint : Set where
  boundaryTrunk :
    BoundaryPoint

  boundaryLeft :
    BoundaryPoint

  boundaryRight :
    BoundaryPoint

canonicalBoundaryPoints : List BoundaryPoint
canonicalBoundaryPoints =
  boundaryTrunk
  ∷ boundaryLeft
  ∷ boundaryRight
  ∷ []

record BulkCell : Set where
  constructor mkBulkCell
  field
    cellDepth :
      Depth

    cellBranch :
      Branch

    cellLabel :
      String

open BulkCell public

rootCell : BulkCell
rootCell =
  mkBulkCell depth0 trunk "root cutoff cell"

leftBulkCell : BulkCell
leftBulkCell =
  mkBulkCell depth1 left "left depth-one cell"

rightBulkCell : BulkCell
rightBulkCell =
  mkBulkCell depth1 right "right depth-one cell"

leftDeepCell : BulkCell
leftDeepCell =
  mkBulkCell depth2 left "left depth-two regularized cell"

rightDeepCell : BulkCell
rightDeepCell =
  mkBulkCell depth2 right "right depth-two regularized cell"

canonicalBulkCells : List BulkCell
canonicalBulkCells =
  rootCell
  ∷ leftBulkCell
  ∷ rightBulkCell
  ∷ leftDeepCell
  ∷ rightDeepCell
  ∷ []

bulkCellCount : Nat
bulkCellCount =
  5

toyBoundaryProjection : BulkCell → BoundaryPoint
toyBoundaryProjection (mkBulkCell depth0 trunk _) =
  boundaryTrunk
toyBoundaryProjection (mkBulkCell depth1 trunk _) =
  boundaryTrunk
toyBoundaryProjection (mkBulkCell depth2 trunk _) =
  boundaryTrunk
toyBoundaryProjection (mkBulkCell _ left _) =
  boundaryLeft
toyBoundaryProjection (mkBulkCell _ right _) =
  boundaryRight

rootProjectsToTrunk :
  toyBoundaryProjection rootCell ≡ boundaryTrunk
rootProjectsToTrunk =
  refl

leftProjectsToLeftBoundary :
  toyBoundaryProjection leftDeepCell ≡ boundaryLeft
leftProjectsToLeftBoundary =
  refl

rightProjectsToRightBoundary :
  toyBoundaryProjection rightDeepCell ≡ boundaryRight
rightProjectsToRightBoundary =
  refl

data CoordinateBoundaryRole : Set where
  finiteCutoffCoordinate :
    CoordinateBoundaryRole

  regularizationBoundary :
    CoordinateBoundaryRole

  toyProjectionBoundary :
    CoordinateBoundaryRole

canonicalCoordinateBoundaryRoles :
  List CoordinateBoundaryRole
canonicalCoordinateBoundaryRoles =
  finiteCutoffCoordinate
  ∷ regularizationBoundary
  ∷ toyProjectionBoundary
  ∷ []

data LiteratureContextRole : Set where
  qftOnBruhatTitsSubspacesContext :
    LiteratureContextRole

  pAdicAdSCFTContext :
    LiteratureContextRole

  holographicDictionaryContext :
    LiteratureContextRole

data SourceUse : Set where
  contextOnly :
    SourceUse

record SourceContextRow : Set where
  constructor mkSourceContextRow
  field
    sourceRole :
      LiteratureContextRole

    sourceUse :
      SourceUse

    venueOrIndex :
      String

    sourceIdentifier :
      String

    sourceTitle :
      String

    contextOnlyRecorded :
      Bool

    contextOnlyRecordedIsTrue :
      contextOnlyRecorded ≡ true

    importsPhysicalOntology :
      Bool

    importsPhysicalOntologyIsFalse :
      importsPhysicalOntology ≡ false

    promotesHolographicQFTBridge :
      Bool

    promotesHolographicQFTBridgeIsFalse :
      promotesHolographicQFTBridge ≡ false

open SourceContextRow public

qftSubspaceSourceRow : SourceContextRow
qftSubspaceSourceRow =
  mkSourceContextRow
    qftOnBruhatTitsSubspacesContext
    contextOnly
    "JHEP06(2024)175 / arXiv"
    "JHEP06(2024)175 / arXiv:2402.03730"
    "Effective field theories on subspaces of the Bruhat-Tits tree"
    true
    refl
    false
    refl
    false
    refl

pAdicAdSCFTSourceRow : SourceContextRow
pAdicAdSCFTSourceRow =
  mkSourceContextRow
    pAdicAdSCFTContext
    contextOnly
    "arXiv"
    "arXiv:1605.01061"
    "p-adic AdS/CFT"
    true
    refl
    false
    refl
    false
    refl

holographicDictionarySourceRow : SourceContextRow
holographicDictionarySourceRow =
  mkSourceContextRow
    holographicDictionaryContext
    contextOnly
    "JHEP05(2019)118 / arXiv"
    "JHEP05(2019)118 / arXiv:1812.06059"
    "Wilson line networks in p-adic AdS/CFT"
    true
    refl
    false
    refl
    false
    refl

canonicalSourceContextRows : List SourceContextRow
canonicalSourceContextRows =
  qftSubspaceSourceRow
  ∷ pAdicAdSCFTSourceRow
  ∷ holographicDictionarySourceRow
  ∷ []

sourceContextRowCount : Nat
sourceContextRowCount =
  3

data BruhatTitsCoordinatePromotion : Set where

bruhatTitsCoordinatePromotionImpossibleHere :
  BruhatTitsCoordinatePromotion →
  ⊥
bruhatTitsCoordinatePromotionImpossibleHere ()

record ControlCard : Set where
  field
    O :
      String

    R :
      String

    C :
      String

    S :
      String

    L :
      String

    P :
      String

    G :
      String

    F :
      String

open ControlCard public

canonicalControlCard : ControlCard
canonicalControlCard =
  record
    { O =
        "O: Worker 5 records a local DASHI physics closure receipt under the two-file edit constraint."
    ; R =
        "R: Model the Bruhat-Tits tree only as finite coordinate and regularization boundary."
    ; C =
        "C: DASHI.Physics.Closure.BruhatTitsHolographicCoordinateBoundary"
    ; S =
        "S: toy finite depth, bulk cells, boundary points, and source-context rows are recorded."
    ; L =
        "L: context -> finite coordinate receipt -> Agda typecheck; no ontology or Clay promotion."
    ; P =
        "P: keep the holographic QFT bridge as a non-promoted coordinate analogy."
    ; G =
        "G: promotion remains blocked unless separate external analytic and physical authority is supplied."
    ; F =
        "F: no continuum QFT construction, no physical ontology, and no Clay proof is supplied here."
    }

record BruhatTitsHolographicCoordinateBoundary : Set where
  field
    coordinateBoundaryName :
      String

    boundaryRoles :
      List CoordinateBoundaryRole

    boundaryRolesAreCanonical :
      boundaryRoles ≡ canonicalCoordinateBoundaryRoles

    finiteDepths :
      List Depth

    finiteDepthsAreCanonical :
      finiteDepths ≡ canonicalDepths

    finiteDepthCount :
      Nat

    finiteDepthCountIsThree :
      finiteDepthCount ≡ depthCount

    bulkCells :
      List BulkCell

    bulkCellsAreCanonical :
      bulkCells ≡ canonicalBulkCells

    recordedBulkCellCount :
      Nat

    recordedBulkCellCountIsFive :
      recordedBulkCellCount ≡ bulkCellCount

    boundaryPoints :
      List BoundaryPoint

    boundaryPointsAreCanonical :
      boundaryPoints ≡ canonicalBoundaryPoints

    rootProjection :
      toyBoundaryProjection rootCell ≡ boundaryTrunk

    leftProjection :
      toyBoundaryProjection leftDeepCell ≡ boundaryLeft

    rightProjection :
      toyBoundaryProjection rightDeepCell ≡ boundaryRight

    localityRecordedForToy :
      Bool

    localityRecordedForToyIsTrue :
      localityRecordedForToy ≡ true

    treeUsedAsCoordinateBoundary :
      Bool

    treeUsedAsCoordinateBoundaryIsTrue :
      treeUsedAsCoordinateBoundary ≡ true

    treeUsedAsPhysicalOntology :
      Bool

    treeUsedAsPhysicalOntologyIsFalse :
      treeUsedAsPhysicalOntology ≡ false

    sourceContextRows :
      List SourceContextRow

    sourceContextRowsAreCanonical :
      sourceContextRows ≡ canonicalSourceContextRows

    recordedSourceContextRowCount :
      Nat

    recordedSourceContextRowCountIsThree :
      recordedSourceContextRowCount ≡ sourceContextRowCount

    holographicQFTBridgePromoted :
      Bool

    holographicQFTBridgePromotedIsFalse :
      holographicQFTBridgePromoted ≡ false

    physicalOntologyClaim :
      Bool

    physicalOntologyClaimIsFalse :
      physicalOntologyClaim ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    promotionFlags :
      List BruhatTitsCoordinatePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    controlCard :
      ControlCard

    boundaryNotes :
      List String

open BruhatTitsHolographicCoordinateBoundary public

canonicalBruhatTitsHolographicCoordinateBoundary :
  BruhatTitsHolographicCoordinateBoundary
canonicalBruhatTitsHolographicCoordinateBoundary =
  record
    { coordinateBoundaryName =
        "Bruhat-Tits holographic coordinate boundary, finite toy receipt"
    ; boundaryRoles =
        canonicalCoordinateBoundaryRoles
    ; boundaryRolesAreCanonical =
        refl
    ; finiteDepths =
        canonicalDepths
    ; finiteDepthsAreCanonical =
        refl
    ; finiteDepthCount =
        depthCount
    ; finiteDepthCountIsThree =
        refl
    ; bulkCells =
        canonicalBulkCells
    ; bulkCellsAreCanonical =
        refl
    ; recordedBulkCellCount =
        bulkCellCount
    ; recordedBulkCellCountIsFive =
        refl
    ; boundaryPoints =
        canonicalBoundaryPoints
    ; boundaryPointsAreCanonical =
        refl
    ; rootProjection =
        rootProjectsToTrunk
    ; leftProjection =
        leftProjectsToLeftBoundary
    ; rightProjection =
        rightProjectsToRightBoundary
    ; localityRecordedForToy =
        true
    ; localityRecordedForToyIsTrue =
        refl
    ; treeUsedAsCoordinateBoundary =
        true
    ; treeUsedAsCoordinateBoundaryIsTrue =
        refl
    ; treeUsedAsPhysicalOntology =
        false
    ; treeUsedAsPhysicalOntologyIsFalse =
        refl
    ; sourceContextRows =
        canonicalSourceContextRows
    ; sourceContextRowsAreCanonical =
        refl
    ; recordedSourceContextRowCount =
        sourceContextRowCount
    ; recordedSourceContextRowCountIsThree =
        refl
    ; holographicQFTBridgePromoted =
        false
    ; holographicQFTBridgePromotedIsFalse =
        refl
    ; physicalOntologyClaim =
        false
    ; physicalOntologyClaimIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; controlCard =
        canonicalControlCard
    ; boundaryNotes =
        "finite Depth is an explicit cutoff coordinate, not an infinite geometric completion"
        ∷ "BulkCell to BoundaryPoint is a toy projection with locality recorded true only for this toy model"
        ∷ "JHEP/arXiv source rows are context-only literature alignment rows"
        ∷ "p-adic AdS/CFT is context for the coordinate analogy, not an imported physical ontology"
        ∷ "holographicQFTBridgePromoted=false, physicalOntologyClaim=false, clayPromotion=false"
        ∷ []
    }

btCoordinateBoundaryLocalityToyTrue :
  localityRecordedForToy canonicalBruhatTitsHolographicCoordinateBoundary
  ≡
  true
btCoordinateBoundaryLocalityToyTrue =
  refl

btCoordinateBoundaryNotOntology :
  physicalOntologyClaim canonicalBruhatTitsHolographicCoordinateBoundary
  ≡
  false
btCoordinateBoundaryNotOntology =
  refl

btCoordinateBoundaryHolographicBridgeNotPromoted :
  holographicQFTBridgePromoted canonicalBruhatTitsHolographicCoordinateBoundary
  ≡
  false
btCoordinateBoundaryHolographicBridgeNotPromoted =
  refl

btCoordinateBoundaryClayNotPromoted :
  clayPromotion canonicalBruhatTitsHolographicCoordinateBoundary
  ≡
  false
btCoordinateBoundaryClayNotPromoted =
  refl
