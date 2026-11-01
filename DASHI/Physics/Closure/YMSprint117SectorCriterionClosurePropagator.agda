module DASHI.Physics.Closure.YMSprint117SectorCriterionClosurePropagator where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint116SectorStabilityClosureReducer
  as Reducer116
import DASHI.Physics.Closure.YMSprint115ProjectionSectorStabilityCriterion
  as Sector115
import DASHI.Physics.Closure.YMSprint115ApproximateInverseResidualCriterion
  as Approx115
import DASHI.Physics.Closure.YMSprint114InverseProjectionClosureCriterion
  as Inverse114

------------------------------------------------------------------------
-- Sprint117 sector-criterion closure propagator.
--
-- Sprint116 supplied a conditional sector-stability reducer.  This module
-- consumes that reducer as an explicit feed source and records that the
-- Sprint117 sector-criterion feed has been propagated.  It deliberately does
-- not turn the feed into any unconditional projection-commutator, physical
-- sector, vacuum sector, sector-stability, external projection-sector, or
-- Clay Yang-Mills theorem.

sprintNumber : Nat
sprintNumber = 117

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint117SectorCriterionClosurePropagator.agda"

sprint116SectorReducerSourcePath : String
sprint116SectorReducerSourcePath =
  Reducer116.modulePath

sprint115ProjectionSectorSourcePath : String
sprint115ProjectionSectorSourcePath =
  Reducer116.sprint115ProjectionSectorStabilityCriterionPath

sprint115ApproximateInverseSourcePath : String
sprint115ApproximateInverseSourcePath =
  Reducer116.sprint115ApproximateInverseResidualCriterionPath

sprint114InverseProjectionSourcePath : String
sprint114InverseProjectionSourcePath =
  Reducer116.sprint114InverseProjectionClosureCriterionPath

sectorCriterionClosurePropagatorRecorded : Bool
sectorCriterionClosurePropagatorRecorded = true

sectorReducerFeedImported : Bool
sectorReducerFeedImported = true

stableSprint115SectorInputImported : Bool
stableSprint115SectorInputImported = true

stableSprint115ApproximateInverseInputImported : Bool
stableSprint115ApproximateInverseInputImported = true

stableSprint114InverseProjectionInputImported : Bool
stableSprint114InverseProjectionInputImported = true

sectorCriterionFeedClosedHere : Bool
sectorCriterionFeedClosedHere = true

sectorCriterionClosedHere : Bool
sectorCriterionClosedHere = false

projectionCommutatorStabilityProvedHere : Bool
projectionCommutatorStabilityProvedHere = false

physicalSectorStabilityProvedHere : Bool
physicalSectorStabilityProvedHere = false

vacuumSectorStabilityProvedHere : Bool
vacuumSectorStabilityProvedHere = false

sectorStabilityTheoremProvedHere : Bool
sectorStabilityTheoremProvedHere = false

externalProjectionSectorClosedHere : Bool
externalProjectionSectorClosedHere = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

propagatorStatementText : String
propagatorStatementText =
  "Sprint117 propagator: consume the Sprint116 sector-stability closure reducer as the supplied feed source for the sector-criterion closure lane, recording feed closure without promoting an unconditional sector theorem."

reducerImportText : String
reducerImportText =
  "Reducer import: Sprint116 supplies inhabited projection-commutator, physical-sector, vacuum-sector, leakage-exclusion, quotient-descent, and approximate-inverse handoff feeds through its canonical sector reducer receipt."

sectorFeedPropagationText : String
sectorFeedPropagationText =
  "Sector criterion feed propagation: the Sprint116 supplied sector reducer is threaded into Sprint117 as a closed feed record for downstream closure assembly, while the underlying analytic theorem flags remain false."

stableSectorInputsText : String
stableSectorInputsText =
  "Stable sector inputs: Sprint115 projection-sector criterion, Sprint115 approximate-inverse residual criterion, and Sprint114 inverse/projection closure criterion are retained as qualified source inputs and receipt fields."

nonPromotionBoundaryText : String
nonPromotionBoundaryText =
  "Sprint117 records only sector-criterion feed propagation.  It proves no projection commutator stability theorem, physical sector theorem, vacuum sector theorem, sector-stability theorem, external projection-sector closure theorem, sector criterion theorem, or Clay Yang-Mills promotion."

finalReceiptText : String
finalReceiptText =
  "Receipt: the Sprint117 sector-criterion feed is closed by propagation from the Sprint116 supplied reducer, with every theorem and promotion boundary explicitly fail-closed."

data PropagatorLane : Set where
  sprint116-sector-reducer-lane :
    PropagatorLane
  sprint115-sector-input-lane :
    PropagatorLane
  sprint115-approximate-inverse-input-lane :
    PropagatorLane
  sprint114-inverse-projection-input-lane :
    PropagatorLane
  sector-criterion-feed-propagation-lane :
    PropagatorLane
  theorem-boundary-lane :
    PropagatorLane
  final-receipt-lane :
    PropagatorLane

data PropagatorStatus : Set where
  imported-sprint116-sector-reducer :
    PropagatorStatus
  imported-stable-sprint115-sector-input :
    PropagatorStatus
  imported-stable-sprint115-approximate-inverse-input :
    PropagatorStatus
  imported-stable-sprint114-inverse-projection-input :
    PropagatorStatus
  sector-criterion-feed-propagated :
    PropagatorStatus
  analytic-theorem-remains-open :
    PropagatorStatus
  fail-closed-nonpromotion :
    PropagatorStatus
  receipt-recorded :
    PropagatorStatus

canonicalPropagatorLanes : List PropagatorLane
canonicalPropagatorLanes =
  sprint116-sector-reducer-lane
  ∷ sprint115-sector-input-lane
  ∷ sprint115-approximate-inverse-input-lane
  ∷ sprint114-inverse-projection-input-lane
  ∷ sector-criterion-feed-propagation-lane
  ∷ theorem-boundary-lane
  ∷ final-receipt-lane
  ∷ []

record SourcePathLedger : Set where
  constructor mkSourcePathLedger
  field
    sprint117PropagatorPath :
      String
    sprint116SectorReducerPath :
      String
    sprint115ProjectionSectorPath :
      String
    sprint115ApproximateInversePath :
      String
    sprint114InverseProjectionPath :
      String
    ledgerRecorded :
      Bool
    ledgerRecordedIsTrue :
      ledgerRecorded ≡ true
    status :
      PropagatorStatus

record ImportedSectorReducerSurface : Setω where
  constructor mkImportedSectorReducerSurface
  field
    sprint116Receipt :
      Reducer116.YMSprint116SectorStabilityClosureReducerReceipt
    sprint116ClosureReducer :
      Reducer116.SectorClosureReducer
    sprint116ImportedSurface :
      Reducer116.ImportedReducerSurface
    sprint115ProjectionSectorReceipt :
      Sector115.YMSprint115ProjectionSectorStabilityCriterionReceipt
    sprint115ApproximateInverseReceipt :
      Approx115.YMSprint115ApproximateInverseResidualCriterionReceipt
    sprint114InverseProjectionReceipt :
      Inverse114.YMSprint114InverseProjectionClosureCriterionReceipt
    sprint115ProjectionSectorCriterion :
      Sector115.ProjectionSectorStabilityCriterion
    sprint115ApproximateInverseCriterion :
      Approx115.ApproximateInverseResidualCriterion
    sprint114ProjectionSectorCriterion :
      Inverse114.ProjectionSectorClosureCriterion
    reducerImported :
      Bool
    reducerImportedIsTrue :
      reducerImported ≡ true
    sprint116ReducerInhabited :
      Bool
    sprint116ReducerInhabitedIsTrue :
      sprint116ReducerInhabited ≡ true
    sprint115SectorCriterionInhabited :
      Bool
    sprint115SectorCriterionInhabitedIsTrue :
      sprint115SectorCriterionInhabited ≡ true
    sprint115ApproximateInverseInhabited :
      Bool
    sprint115ApproximateInverseInhabitedIsTrue :
      sprint115ApproximateInverseInhabited ≡ true
    sprint114InverseProjectionInhabited :
      Bool
    sprint114InverseProjectionInhabitedIsTrue :
      sprint114InverseProjectionInhabited ≡ true
    importedProjectionCommutatorTheoremOpen :
      Bool
    importedProjectionCommutatorTheoremOpenIsFalse :
      importedProjectionCommutatorTheoremOpen ≡ false
    importedPhysicalSectorTheoremOpen :
      Bool
    importedPhysicalSectorTheoremOpenIsFalse :
      importedPhysicalSectorTheoremOpen ≡ false
    importedVacuumSectorTheoremOpen :
      Bool
    importedVacuumSectorTheoremOpenIsFalse :
      importedVacuumSectorTheoremOpen ≡ false
    importedSectorTheoremOpen :
      Bool
    importedSectorTheoremOpenIsFalse :
      importedSectorTheoremOpen ≡ false
    importedExternalProjectionSectorOpen :
      Bool
    importedExternalProjectionSectorOpenIsFalse :
      importedExternalProjectionSectorOpen ≡ false
    importedClayPromotionOpen :
      Bool
    importedClayPromotionOpenIsFalse :
      importedClayPromotionOpen ≡ false
    status :
      PropagatorStatus

record SectorCriterionFeedPropagation : Setω where
  constructor mkSectorCriterionFeedPropagation
  field
    statement :
      String
    importedSurface :
      ImportedSectorReducerSurface
    sourceReducer :
      Reducer116.SectorClosureReducer
    projectionCommutatorFeed :
      Reducer116.ProjectionCommutatorFeed
    physicalSectorFeed :
      Reducer116.PhysicalSectorFeed
    vacuumSectorFeed :
      Reducer116.VacuumSectorFeed
    leakageExclusionFeed :
      Reducer116.LeakageExclusionFeed
    quotientDescentFeed :
      Reducer116.QuotientDescentFeed
    approximateInverseHandoff :
      Approx115.ApproximateInverseResidualCriterion
    projectionCommutatorFeedInhabited :
      Bool
    projectionCommutatorFeedInhabitedIsTrue :
      projectionCommutatorFeedInhabited ≡ true
    physicalSectorFeedInhabited :
      Bool
    physicalSectorFeedInhabitedIsTrue :
      physicalSectorFeedInhabited ≡ true
    vacuumSectorFeedInhabited :
      Bool
    vacuumSectorFeedInhabitedIsTrue :
      vacuumSectorFeedInhabited ≡ true
    leakageExclusionFeedInhabited :
      Bool
    leakageExclusionFeedInhabitedIsTrue :
      leakageExclusionFeedInhabited ≡ true
    quotientDescentFeedInhabited :
      Bool
    quotientDescentFeedInhabitedIsTrue :
      quotientDescentFeedInhabited ≡ true
    feedClosedHere :
      Bool
    feedClosedHereIsTrue :
      feedClosedHere ≡ true
    sectorCriterionClosedHereFlag :
      Bool
    sectorCriterionClosedHereIsFalse :
      sectorCriterionClosedHereFlag ≡ false
    externalProjectionSectorClosedHereFlag :
      Bool
    externalProjectionSectorClosedHereIsFalse :
      externalProjectionSectorClosedHereFlag ≡ false
    status :
      PropagatorStatus

record TheoremBoundary : Set where
  constructor mkTheoremBoundary
  field
    boundaryStatement :
      String
    projectionCommutatorStabilityProvedHereFlag :
      Bool
    projectionCommutatorStabilityProvedHereIsFalse :
      projectionCommutatorStabilityProvedHereFlag ≡ false
    physicalSectorStabilityProvedHereFlag :
      Bool
    physicalSectorStabilityProvedHereIsFalse :
      physicalSectorStabilityProvedHereFlag ≡ false
    vacuumSectorStabilityProvedHereFlag :
      Bool
    vacuumSectorStabilityProvedHereIsFalse :
      vacuumSectorStabilityProvedHereFlag ≡ false
    sectorStabilityTheoremProvedHereFlag :
      Bool
    sectorStabilityTheoremProvedHereIsFalse :
      sectorStabilityTheoremProvedHereFlag ≡ false
    sectorCriterionClosedHereFlag :
      Bool
    sectorCriterionClosedHereIsFalse :
      sectorCriterionClosedHereFlag ≡ false
    externalProjectionSectorClosedHereFlag :
      Bool
    externalProjectionSectorClosedHereIsFalse :
      externalProjectionSectorClosedHereFlag ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    status :
      PropagatorStatus

record YMSprint117SectorCriterionClosurePropagatorReceipt : Setω where
  constructor mkYMSprint117SectorCriterionClosurePropagatorReceipt
  field
    sprint :
      Nat
    evidencePath :
      String
    sourcePaths :
      SourcePathLedger
    importedSurface :
      ImportedSectorReducerSurface
    sectorCriterionFeed :
      SectorCriterionFeedPropagation
    theoremBoundary :
      TheoremBoundary
    lanes :
      List PropagatorLane
    evidenceLedger :
      List String
    receiptStatement :
      String
    propagatorRecorded :
      Bool
    propagatorRecordedIsTrue :
      propagatorRecorded ≡ true
    sectorCriterionFeedClosed :
      Bool
    sectorCriterionFeedClosedIsTrue :
      sectorCriterionFeedClosed ≡ true
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    status :
      PropagatorStatus

open SourcePathLedger public
open ImportedSectorReducerSurface public
open SectorCriterionFeedPropagation public
open TheoremBoundary public
open YMSprint117SectorCriterionClosurePropagatorReceipt public

canonicalSourcePathLedger : SourcePathLedger
canonicalSourcePathLedger =
  mkSourcePathLedger
    modulePath
    sprint116SectorReducerSourcePath
    sprint115ProjectionSectorSourcePath
    sprint115ApproximateInverseSourcePath
    sprint114InverseProjectionSourcePath
    sectorCriterionClosurePropagatorRecorded
    refl
    receipt-recorded

canonicalImportedSectorReducerSurface : ImportedSectorReducerSurface
canonicalImportedSectorReducerSurface =
  mkImportedSectorReducerSurface
    Reducer116.canonicalReceipt
    (Reducer116.closureReducer Reducer116.canonicalReceipt)
    (Reducer116.importedSurface Reducer116.canonicalReceipt)
    Sector115.canonicalReceipt
    Approx115.canonicalReceipt
    Inverse114.canonicalReceipt
    (Sector115.projectionSectorStabilityCriterion Sector115.canonicalReceipt)
    (Approx115.approximateInverseResidualCriterion Approx115.canonicalReceipt)
    (Inverse114.projectionSectorCriterion Inverse114.canonicalReceipt)
    sectorReducerFeedImported
    refl
    (Reducer116.reducerInhabited Reducer116.canonicalReceipt)
    Reducer116.canonicalReducerInhabitedIsTrue
    (Sector115.criterionInhabited Sector115.canonicalReceipt)
    Sector115.canonicalCriterionInhabitedIsTrue
    (Approx115.criterionInhabited Approx115.canonicalReceipt)
    Approx115.canonicalCriterionInhabitedIsTrue
    (Inverse114.criterionInhabited Inverse114.canonicalReceipt)
    Inverse114.canonicalCriterionInhabitedIsTrue
    (Reducer116.TheoremBoundary.projectionCommutatorStabilityProvedHereFlag
      (Reducer116.theoremBoundary Reducer116.canonicalReceipt))
    Reducer116.canonicalProjectionCommutatorStabilityProvedHereIsFalse
    (Reducer116.TheoremBoundary.physicalSectorStabilityProvedHereFlag
      (Reducer116.theoremBoundary Reducer116.canonicalReceipt))
    Reducer116.canonicalPhysicalSectorStabilityProvedHereIsFalse
    (Reducer116.TheoremBoundary.vacuumSectorStabilityProvedHereFlag
      (Reducer116.theoremBoundary Reducer116.canonicalReceipt))
    Reducer116.canonicalVacuumSectorStabilityProvedHereIsFalse
    (Reducer116.TheoremBoundary.sectorStabilityTheoremProvedHereFlag
      (Reducer116.theoremBoundary Reducer116.canonicalReceipt))
    Reducer116.canonicalSectorStabilityTheoremProvedHereIsFalse
    (Reducer116.TheoremBoundary.externalProjectionSectorClosedHereFlag
      (Reducer116.theoremBoundary Reducer116.canonicalReceipt))
    Reducer116.canonicalExternalProjectionSectorClosedHereIsFalse
    (Reducer116.clayYangMillsPromotedHere Reducer116.canonicalReceipt)
    Reducer116.canonicalClayYangMillsPromotedIsFalse
    imported-sprint116-sector-reducer

sectorCriterionFeedFrom :
  ImportedSectorReducerSurface ->
  SectorCriterionFeedPropagation
sectorCriterionFeedFrom surface =
  mkSectorCriterionFeedPropagation
    sectorFeedPropagationText
    surface
    (ImportedSectorReducerSurface.sprint116ClosureReducer surface)
    (Reducer116.SectorClosureReducer.projectionCommutatorFeed
      (ImportedSectorReducerSurface.sprint116ClosureReducer surface))
    (Reducer116.SectorClosureReducer.physicalSectorFeed
      (ImportedSectorReducerSurface.sprint116ClosureReducer surface))
    (Reducer116.SectorClosureReducer.vacuumSectorFeed
      (ImportedSectorReducerSurface.sprint116ClosureReducer surface))
    (Reducer116.SectorClosureReducer.leakageExclusionFeed
      (ImportedSectorReducerSurface.sprint116ClosureReducer surface))
    (Reducer116.SectorClosureReducer.quotientDescentFeed
      (ImportedSectorReducerSurface.sprint116ClosureReducer surface))
    (Reducer116.SectorClosureReducer.approximateInverseHandoff
      (ImportedSectorReducerSurface.sprint116ClosureReducer surface))
    (Reducer116.ProjectionCommutatorFeed.feedInhabited
      (Reducer116.SectorClosureReducer.projectionCommutatorFeed
        (ImportedSectorReducerSurface.sprint116ClosureReducer surface)))
    (Reducer116.ProjectionCommutatorFeed.feedInhabitedIsTrue
      (Reducer116.SectorClosureReducer.projectionCommutatorFeed
        (ImportedSectorReducerSurface.sprint116ClosureReducer surface)))
    (Reducer116.PhysicalSectorFeed.feedInhabited
      (Reducer116.SectorClosureReducer.physicalSectorFeed
        (ImportedSectorReducerSurface.sprint116ClosureReducer surface)))
    (Reducer116.PhysicalSectorFeed.feedInhabitedIsTrue
      (Reducer116.SectorClosureReducer.physicalSectorFeed
        (ImportedSectorReducerSurface.sprint116ClosureReducer surface)))
    (Reducer116.VacuumSectorFeed.feedInhabited
      (Reducer116.SectorClosureReducer.vacuumSectorFeed
        (ImportedSectorReducerSurface.sprint116ClosureReducer surface)))
    (Reducer116.VacuumSectorFeed.feedInhabitedIsTrue
      (Reducer116.SectorClosureReducer.vacuumSectorFeed
        (ImportedSectorReducerSurface.sprint116ClosureReducer surface)))
    (Reducer116.LeakageExclusionFeed.feedInhabited
      (Reducer116.SectorClosureReducer.leakageExclusionFeed
        (ImportedSectorReducerSurface.sprint116ClosureReducer surface)))
    (Reducer116.LeakageExclusionFeed.feedInhabitedIsTrue
      (Reducer116.SectorClosureReducer.leakageExclusionFeed
        (ImportedSectorReducerSurface.sprint116ClosureReducer surface)))
    (Reducer116.QuotientDescentFeed.feedInhabited
      (Reducer116.SectorClosureReducer.quotientDescentFeed
        (ImportedSectorReducerSurface.sprint116ClosureReducer surface)))
    (Reducer116.QuotientDescentFeed.feedInhabitedIsTrue
      (Reducer116.SectorClosureReducer.quotientDescentFeed
        (ImportedSectorReducerSurface.sprint116ClosureReducer surface)))
    sectorCriterionFeedClosedHere
    refl
    sectorCriterionClosedHere
    refl
    externalProjectionSectorClosedHere
    refl
    sector-criterion-feed-propagated

canonicalTheoremBoundary : TheoremBoundary
canonicalTheoremBoundary =
  mkTheoremBoundary
    nonPromotionBoundaryText
    projectionCommutatorStabilityProvedHere
    refl
    physicalSectorStabilityProvedHere
    refl
    vacuumSectorStabilityProvedHere
    refl
    sectorStabilityTheoremProvedHere
    refl
    sectorCriterionClosedHere
    refl
    externalProjectionSectorClosedHere
    refl
    clayYangMillsPromoted
    refl
    fail-closed-nonpromotion

receiptFrom :
  ImportedSectorReducerSurface ->
  YMSprint117SectorCriterionClosurePropagatorReceipt
receiptFrom surface =
  mkYMSprint117SectorCriterionClosurePropagatorReceipt
    sprintNumber
    modulePath
    canonicalSourcePathLedger
    surface
    (sectorCriterionFeedFrom surface)
    canonicalTheoremBoundary
    canonicalPropagatorLanes
    (propagatorStatementText
     ∷ reducerImportText
     ∷ sectorFeedPropagationText
     ∷ stableSectorInputsText
     ∷ nonPromotionBoundaryText
     ∷ finalReceiptText
     ∷ sprint116SectorReducerSourcePath
     ∷ sprint115ProjectionSectorSourcePath
     ∷ sprint115ApproximateInverseSourcePath
     ∷ sprint114InverseProjectionSourcePath
     ∷ [])
    finalReceiptText
    sectorCriterionClosurePropagatorRecorded
    refl
    sectorCriterionFeedClosedHere
    refl
    clayYangMillsPromoted
    refl
    receipt-recorded

canonicalYMSprint117SectorCriterionClosurePropagatorReceipt :
  YMSprint117SectorCriterionClosurePropagatorReceipt
canonicalYMSprint117SectorCriterionClosurePropagatorReceipt =
  receiptFrom canonicalImportedSectorReducerSurface

canonicalReceipt : YMSprint117SectorCriterionClosurePropagatorReceipt
canonicalReceipt =
  canonicalYMSprint117SectorCriterionClosurePropagatorReceipt

canonicalPropagatorRecordedIsTrue :
  propagatorRecorded canonicalReceipt ≡ true
canonicalPropagatorRecordedIsTrue =
  refl

canonicalSectorCriterionFeedClosedIsTrue :
  sectorCriterionFeedClosed canonicalReceipt ≡ true
canonicalSectorCriterionFeedClosedIsTrue =
  refl

canonicalFeedRecordClosedIsTrue :
  SectorCriterionFeedPropagation.feedClosedHere
    (sectorCriterionFeed canonicalReceipt) ≡ true
canonicalFeedRecordClosedIsTrue =
  refl

canonicalProjectionCommutatorFeedInhabitedIsTrue :
  SectorCriterionFeedPropagation.projectionCommutatorFeedInhabited
    (sectorCriterionFeed canonicalReceipt) ≡ true
canonicalProjectionCommutatorFeedInhabitedIsTrue =
  refl

canonicalPhysicalSectorFeedInhabitedIsTrue :
  SectorCriterionFeedPropagation.physicalSectorFeedInhabited
    (sectorCriterionFeed canonicalReceipt) ≡ true
canonicalPhysicalSectorFeedInhabitedIsTrue =
  refl

canonicalVacuumSectorFeedInhabitedIsTrue :
  SectorCriterionFeedPropagation.vacuumSectorFeedInhabited
    (sectorCriterionFeed canonicalReceipt) ≡ true
canonicalVacuumSectorFeedInhabitedIsTrue =
  refl

canonicalLeakageExclusionFeedInhabitedIsTrue :
  SectorCriterionFeedPropagation.leakageExclusionFeedInhabited
    (sectorCriterionFeed canonicalReceipt) ≡ true
canonicalLeakageExclusionFeedInhabitedIsTrue =
  refl

canonicalQuotientDescentFeedInhabitedIsTrue :
  SectorCriterionFeedPropagation.quotientDescentFeedInhabited
    (sectorCriterionFeed canonicalReceipt) ≡ true
canonicalQuotientDescentFeedInhabitedIsTrue =
  refl

canonicalSectorCriterionClosedHereIsFalse :
  TheoremBoundary.sectorCriterionClosedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalSectorCriterionClosedHereIsFalse =
  refl

canonicalProjectionCommutatorStabilityProvedHereIsFalse :
  TheoremBoundary.projectionCommutatorStabilityProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalProjectionCommutatorStabilityProvedHereIsFalse =
  refl

canonicalPhysicalSectorStabilityProvedHereIsFalse :
  TheoremBoundary.physicalSectorStabilityProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalPhysicalSectorStabilityProvedHereIsFalse =
  refl

canonicalVacuumSectorStabilityProvedHereIsFalse :
  TheoremBoundary.vacuumSectorStabilityProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalVacuumSectorStabilityProvedHereIsFalse =
  refl

canonicalSectorStabilityTheoremProvedHereIsFalse :
  TheoremBoundary.sectorStabilityTheoremProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalSectorStabilityTheoremProvedHereIsFalse =
  refl

canonicalExternalProjectionSectorClosedHereIsFalse :
  TheoremBoundary.externalProjectionSectorClosedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalExternalProjectionSectorClosedHereIsFalse =
  refl

canonicalClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalClayYangMillsPromotedIsFalse =
  refl
