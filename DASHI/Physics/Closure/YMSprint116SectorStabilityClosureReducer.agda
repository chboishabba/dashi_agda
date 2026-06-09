module DASHI.Physics.Closure.YMSprint116SectorStabilityClosureReducer where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint115ProjectionSectorStabilityCriterion
  as Sector115
import DASHI.Physics.Closure.YMSprint115ApproximateInverseResidualCriterion
  as Approx115
import DASHI.Physics.Closure.YMSprint114InverseProjectionClosureCriterion
  as Inverse114

------------------------------------------------------------------------
-- Sprint116 sector-stability closure reducer.
--
-- This module reduces the remaining Sprint115 sector false flags to an
-- explicit supplied-feed interface.  It records inhabited feeds for the
-- projection commutator, physical sector, vacuum sector, leakage exclusion,
-- quotient descent, approximate inverse sector handoff, and quotient-level
-- sector criterion.  The unconditional theorem flags remain false.

sprintNumber : Nat
sprintNumber = 116

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint116SectorStabilityClosureReducer.agda"

sprint115ProjectionSectorStabilityCriterionPath : String
sprint115ProjectionSectorStabilityCriterionPath =
  "DASHI/Physics/Closure/YMSprint115ProjectionSectorStabilityCriterion.agda"

sprint115ApproximateInverseResidualCriterionPath : String
sprint115ApproximateInverseResidualCriterionPath =
  "DASHI/Physics/Closure/YMSprint115ApproximateInverseResidualCriterion.agda"

sprint114InverseProjectionClosureCriterionPath : String
sprint114InverseProjectionClosureCriterionPath =
  "DASHI/Physics/Closure/YMSprint114InverseProjectionClosureCriterion.agda"

sectorStabilityClosureReducerRecorded : Bool
sectorStabilityClosureReducerRecorded = true

projectionCommutatorFeedInhabited : Bool
projectionCommutatorFeedInhabited = true

physicalSectorFeedInhabited : Bool
physicalSectorFeedInhabited = true

vacuumSectorFeedInhabited : Bool
vacuumSectorFeedInhabited = true

leakageExclusionFeedInhabited : Bool
leakageExclusionFeedInhabited = true

quotientDescentFeedInhabited : Bool
quotientDescentFeedInhabited = true

closureReducerInhabited : Bool
closureReducerInhabited = true

projectionCommutatorStabilityProvedHere : Bool
projectionCommutatorStabilityProvedHere = false

physicalSectorStabilityProvedHere : Bool
physicalSectorStabilityProvedHere = false

vacuumSectorStabilityProvedHere : Bool
vacuumSectorStabilityProvedHere = false

sectorStabilityTheoremProvedHere : Bool
sectorStabilityTheoremProvedHere = false

inverseProjectionClosureTheoremProvedHere : Bool
inverseProjectionClosureTheoremProvedHere = false

externalProjectionSectorClosedHere : Bool
externalProjectionSectorClosedHere = false

sectorCriterionClosedHere : Bool
sectorCriterionClosedHere = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

criterionStatementText : String
criterionStatementText =
  "Sprint116 reducer: supplied projection-commutator, physical-sector, vacuum-sector, leakage-exclusion, quotient-descent, and approximate-inverse handoff feeds reduce the Sprint115 sector false flags to an inhabited conditional closure interface."

projectionCommutatorFeedText : String
projectionCommutatorFeedText =
  "Projection commutator feed: reuse the Sprint115 projection-sector criterion and Sprint114 inverse/projection criterion while consuming supplied E_a/P_a commutator stability."

physicalSectorFeedText : String
physicalSectorFeedText =
  "Physical sector feed: consume the supplied Sprint115 physical-sector invariance record without promoting it to an unconditional theorem."

vacuumSectorFeedText : String
vacuumSectorFeedText =
  "Vacuum sector feed: consume the supplied Sprint115 vacuum-sector invariance record without promoting it to an unconditional theorem."

leakageExclusionFeedText : String
leakageExclusionFeedText =
  "Leakage exclusion feed: consume supplied gauge, vacuum, and non-vacuum leakage exclusions before quotient descent."

quotientDescentFeedText : String
quotientDescentFeedText =
  "Quotient descent feed: consume supplied representative independence and quotient descent, and thread the Sprint114 inverse/projection receipt through the sector reducer."

closureReducerText : String
closureReducerText =
  "Closure reducer: from the supplied sector feeds, the Sprint115 projection-sector receipt, the Sprint115 approximate-inverse receipt, and the Sprint114 inverse/projection receipt, construct an inhabited conditional sector closure package."

failClosedBoundaryText : String
failClosedBoundaryText =
  "Sprint116 records a conditional sector-stability closure reducer only.  It proves no unconditional projection commutator theorem, physical-sector theorem, vacuum-sector theorem, sector-stability theorem, inverse/projection closure theorem, external projection-sector theorem, sector criterion theorem, or Clay Yang-Mills promotion."

data ReducerLane : Set where
  sprint115-projection-sector-input-lane :
    ReducerLane
  sprint115-approximate-inverse-input-lane :
    ReducerLane
  sprint114-inverse-projection-input-lane :
    ReducerLane
  projection-commutator-feed-lane :
    ReducerLane
  physical-sector-feed-lane :
    ReducerLane
  vacuum-sector-feed-lane :
    ReducerLane
  leakage-exclusion-feed-lane :
    ReducerLane
  quotient-descent-feed-lane :
    ReducerLane
  closure-reducer-lane :
    ReducerLane
  theorem-boundary-lane :
    ReducerLane

data ReducerStatus : Set where
  imported-sprint115-projection-sector :
    ReducerStatus
  imported-sprint115-approximate-inverse :
    ReducerStatus
  imported-sprint114-inverse-projection :
    ReducerStatus
  supplied-feed-consumed :
    ReducerStatus
  conditional-sector-reducer-inhabited :
    ReducerStatus
  theorem-remains-open :
    ReducerStatus
  fail-closed-nonpromotion :
    ReducerStatus

canonicalReducerLanes : List ReducerLane
canonicalReducerLanes =
  sprint115-projection-sector-input-lane
  ∷ sprint115-approximate-inverse-input-lane
  ∷ sprint114-inverse-projection-input-lane
  ∷ projection-commutator-feed-lane
  ∷ physical-sector-feed-lane
  ∷ vacuum-sector-feed-lane
  ∷ leakage-exclusion-feed-lane
  ∷ quotient-descent-feed-lane
  ∷ closure-reducer-lane
  ∷ theorem-boundary-lane
  ∷ []

record ImportedReducerSurface : Setω where
  constructor mkImportedReducerSurface
  field
    projectionSectorReceipt :
      Sector115.YMSprint115ProjectionSectorStabilityCriterionReceipt
    approximateInverseReceipt :
      Approx115.YMSprint115ApproximateInverseResidualCriterionReceipt
    inverseProjectionReceipt :
      Inverse114.YMSprint114InverseProjectionClosureCriterionReceipt
    sprint115ProjectionCriterion :
      Sector115.ProjectionSectorStabilityCriterion
    sprint115ApproximateInverseCriterion :
      Approx115.ApproximateInverseResidualCriterion
    sprint114ProjectionSectorCriterion :
      Inverse114.ProjectionSectorClosureCriterion
    projectionSectorCriterionInhabited :
      Bool
    projectionSectorCriterionInhabitedIsTrue :
      projectionSectorCriterionInhabited ≡ true
    approximateInverseCriterionInhabited :
      Bool
    approximateInverseCriterionInhabitedIsTrue :
      approximateInverseCriterionInhabited ≡ true
    inverseProjectionCriterionInhabited :
      Bool
    inverseProjectionCriterionInhabitedIsTrue :
      inverseProjectionCriterionInhabited ≡ true
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
    importedExternalProjectionSectorOpen :
      Bool
    importedExternalProjectionSectorOpenIsFalse :
      importedExternalProjectionSectorOpen ≡ false
    importedInverseProjectionTheoremOpen :
      Bool
    importedInverseProjectionTheoremOpenIsFalse :
      importedInverseProjectionTheoremOpen ≡ false
    status :
      ReducerStatus

record ProjectionCommutatorFeed : Setω where
  constructor mkProjectionCommutatorFeed
  field
    statement :
      String
    sprint115ProjectionCommutator :
      Sector115.ProjectionCommutatorStability
    sprint114ProjectionSectorCriterion :
      Inverse114.ProjectionSectorClosureCriterion
    embeddingProjectionCommutatorStable :
      Bool
    embeddingProjectionCommutatorStableIsTrue :
      embeddingProjectionCommutatorStable ≡ true
    samplingProjectionCommutatorStable :
      Bool
    samplingProjectionCommutatorStableIsTrue :
      samplingProjectionCommutatorStable ≡ true
    feedInhabited :
      Bool
    feedInhabitedIsTrue :
      feedInhabited ≡ true
    theoremProvedHere :
      Bool
    theoremProvedHereIsFalse :
      theoremProvedHere ≡ false
    status :
      ReducerStatus

record PhysicalSectorFeed : Setω where
  constructor mkPhysicalSectorFeed
  field
    statement :
      String
    sprint115PhysicalSector :
      Sector115.PhysicalSectorStability
    physicalSectorInvariant :
      Bool
    physicalSectorInvariantIsTrue :
      physicalSectorInvariant ≡ true
    feedInhabited :
      Bool
    feedInhabitedIsTrue :
      feedInhabited ≡ true
    theoremProvedHere :
      Bool
    theoremProvedHereIsFalse :
      theoremProvedHere ≡ false
    status :
      ReducerStatus

record VacuumSectorFeed : Setω where
  constructor mkVacuumSectorFeed
  field
    statement :
      String
    sprint115VacuumSector :
      Sector115.VacuumSectorStability
    vacuumSectorInvariant :
      Bool
    vacuumSectorInvariantIsTrue :
      vacuumSectorInvariant ≡ true
    feedInhabited :
      Bool
    feedInhabitedIsTrue :
      feedInhabited ≡ true
    theoremProvedHere :
      Bool
    theoremProvedHereIsFalse :
      theoremProvedHere ≡ false
    status :
      ReducerStatus

record LeakageExclusionFeed : Setω where
  constructor mkLeakageExclusionFeed
  field
    statement :
      String
    sprint115LeakageExclusion :
      Sector115.LeakageExclusion
    gaugeSectorLeakageExcluded :
      Bool
    gaugeSectorLeakageExcludedIsTrue :
      gaugeSectorLeakageExcluded ≡ true
    vacuumSectorLeakageExcluded :
      Bool
    vacuumSectorLeakageExcludedIsTrue :
      vacuumSectorLeakageExcluded ≡ true
    nonVacuumSectorLeakageExcluded :
      Bool
    nonVacuumSectorLeakageExcludedIsTrue :
      nonVacuumSectorLeakageExcluded ≡ true
    feedInhabited :
      Bool
    feedInhabitedIsTrue :
      feedInhabited ≡ true
    status :
      ReducerStatus

record QuotientDescentFeed : Setω where
  constructor mkQuotientDescentFeed
  field
    statement :
      String
    sprint115QuotientDescent :
      Sector115.QuotientDescentFeedThrough
    sprint114Receipt :
      Inverse114.YMSprint114InverseProjectionClosureCriterionReceipt
    quotientDescentAvailable :
      Bool
    quotientDescentAvailableIsTrue :
      quotientDescentAvailable ≡ true
    representativeIndependenceAvailable :
      Bool
    representativeIndependenceAvailableIsTrue :
      representativeIndependenceAvailable ≡ true
    sprint114FeedThroughCompatible :
      Bool
    sprint114FeedThroughCompatibleIsTrue :
      sprint114FeedThroughCompatible ≡ true
    feedInhabited :
      Bool
    feedInhabitedIsTrue :
      feedInhabited ≡ true
    status :
      ReducerStatus

record SectorClosureReducer : Setω where
  constructor mkSectorClosureReducer
  field
    importedSurface :
      ImportedReducerSurface
    projectionCommutatorFeed :
      ProjectionCommutatorFeed
    physicalSectorFeed :
      PhysicalSectorFeed
    vacuumSectorFeed :
      VacuumSectorFeed
    leakageExclusionFeed :
      LeakageExclusionFeed
    quotientDescentFeed :
      QuotientDescentFeed
    approximateInverseHandoff :
      Approx115.ApproximateInverseResidualCriterion
    criterionStatement :
      String
    reducerInhabited :
      Bool
    reducerInhabitedIsTrue :
      reducerInhabited ≡ true
    sectorCriterionClosedHereFlag :
      Bool
    sectorCriterionClosedHereIsFalse :
      sectorCriterionClosedHereFlag ≡ false
    externalProjectionSectorClosedHereFlag :
      Bool
    externalProjectionSectorClosedHereIsFalse :
      externalProjectionSectorClosedHereFlag ≡ false
    status :
      ReducerStatus

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
    inverseProjectionClosureTheoremProvedHereFlag :
      Bool
    inverseProjectionClosureTheoremProvedHereIsFalse :
      inverseProjectionClosureTheoremProvedHereFlag ≡ false
    externalProjectionSectorClosedHereFlag :
      Bool
    externalProjectionSectorClosedHereIsFalse :
      externalProjectionSectorClosedHereFlag ≡ false
    sectorCriterionClosedHereFlag :
      Bool
    sectorCriterionClosedHereIsFalse :
      sectorCriterionClosedHereFlag ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    status :
      ReducerStatus

record YMSprint116SectorStabilityClosureReducerReceipt : Setω where
  constructor mkYMSprint116SectorStabilityClosureReducerReceipt
  field
    sprint :
      Nat
    evidencePath :
      String
    importedSurface :
      ImportedReducerSurface
    closureReducer :
      SectorClosureReducer
    theoremBoundary :
      TheoremBoundary
    lanes :
      List ReducerLane
    evidenceLedger :
      List String
    reducerRecorded :
      Bool
    reducerInhabited :
      Bool
    reducerInhabitedIsTrue :
      reducerInhabited ≡ true
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false

open ImportedReducerSurface public
open ProjectionCommutatorFeed public
open PhysicalSectorFeed public
open VacuumSectorFeed public
open LeakageExclusionFeed public
open QuotientDescentFeed public
open SectorClosureReducer public
open TheoremBoundary public
open YMSprint116SectorStabilityClosureReducerReceipt public

canonicalImportedReducerSurface : ImportedReducerSurface
canonicalImportedReducerSurface =
  mkImportedReducerSurface
    Sector115.canonicalReceipt
    Approx115.canonicalReceipt
    Inverse114.canonicalReceipt
    (Sector115.projectionSectorStabilityCriterion Sector115.canonicalReceipt)
    (Approx115.approximateInverseResidualCriterion Approx115.canonicalReceipt)
    (Inverse114.projectionSectorCriterion Inverse114.canonicalReceipt)
    (Sector115.criterionInhabited Sector115.canonicalReceipt)
    Sector115.canonicalCriterionInhabitedIsTrue
    (Approx115.criterionInhabited Approx115.canonicalReceipt)
    Approx115.canonicalCriterionInhabitedIsTrue
    (Inverse114.criterionInhabited Inverse114.canonicalReceipt)
    Inverse114.canonicalCriterionInhabitedIsTrue
    (Sector115.TheoremBoundary.projectionCommutatorStabilityProvedHereFlag
      (Sector115.theoremBoundary Sector115.canonicalReceipt))
    Sector115.canonicalProjectionCommutatorStabilityProvedHereIsFalse
    (Sector115.TheoremBoundary.physicalSectorStabilityProvedHereFlag
      (Sector115.theoremBoundary Sector115.canonicalReceipt))
    Sector115.canonicalPhysicalSectorStabilityProvedHereIsFalse
    (Sector115.TheoremBoundary.vacuumSectorStabilityProvedHereFlag
      (Sector115.theoremBoundary Sector115.canonicalReceipt))
    Sector115.canonicalVacuumSectorStabilityProvedHereIsFalse
    (Approx115.TheoremBoundary.projectionSectorClosedHere
      (Approx115.theoremBoundary Approx115.canonicalReceipt))
    Approx115.canonicalExternalProjectionSectorClosedHereIsFalse
    (Inverse114.TheoremBoundary.inverseProjectionClosureTheoremProvedHereFlag
      (Inverse114.theoremBoundary Inverse114.canonicalReceipt))
    Inverse114.canonicalInverseProjectionClosureTheoremProvedHereIsFalse
    imported-sprint115-projection-sector

projectionCommutatorFeedFrom :
  ImportedReducerSurface ->
  ProjectionCommutatorFeed
projectionCommutatorFeedFrom surface =
  mkProjectionCommutatorFeed
    projectionCommutatorFeedText
    (Sector115.ProjectionSectorStabilityCriterion.projectionCommutatorStability
      (ImportedReducerSurface.sprint115ProjectionCriterion surface))
    (ImportedReducerSurface.sprint114ProjectionSectorCriterion surface)
    (Sector115.ProjectionCommutatorStability.embeddingProjectionCommutatorStable
      (Sector115.ProjectionSectorStabilityCriterion.projectionCommutatorStability
        (ImportedReducerSurface.sprint115ProjectionCriterion surface)))
    (Sector115.ProjectionCommutatorStability.embeddingProjectionCommutatorStableIsTrue
      (Sector115.ProjectionSectorStabilityCriterion.projectionCommutatorStability
        (ImportedReducerSurface.sprint115ProjectionCriterion surface)))
    (Sector115.ProjectionCommutatorStability.samplingProjectionCommutatorStable
      (Sector115.ProjectionSectorStabilityCriterion.projectionCommutatorStability
        (ImportedReducerSurface.sprint115ProjectionCriterion surface)))
    (Sector115.ProjectionCommutatorStability.samplingProjectionCommutatorStableIsTrue
      (Sector115.ProjectionSectorStabilityCriterion.projectionCommutatorStability
        (ImportedReducerSurface.sprint115ProjectionCriterion surface)))
    projectionCommutatorFeedInhabited
    refl
    projectionCommutatorStabilityProvedHere
    refl
    supplied-feed-consumed

physicalSectorFeedFrom :
  ImportedReducerSurface ->
  PhysicalSectorFeed
physicalSectorFeedFrom surface =
  mkPhysicalSectorFeed
    physicalSectorFeedText
    (Sector115.ProjectionSectorStabilityCriterion.physicalSectorStability
      (ImportedReducerSurface.sprint115ProjectionCriterion surface))
    (Sector115.PhysicalSectorStability.physicalSectorInvariant
      (Sector115.ProjectionSectorStabilityCriterion.physicalSectorStability
        (ImportedReducerSurface.sprint115ProjectionCriterion surface)))
    (Sector115.PhysicalSectorStability.physicalSectorInvariantIsTrue
      (Sector115.ProjectionSectorStabilityCriterion.physicalSectorStability
        (ImportedReducerSurface.sprint115ProjectionCriterion surface)))
    physicalSectorFeedInhabited
    refl
    physicalSectorStabilityProvedHere
    refl
    supplied-feed-consumed

vacuumSectorFeedFrom :
  ImportedReducerSurface ->
  VacuumSectorFeed
vacuumSectorFeedFrom surface =
  mkVacuumSectorFeed
    vacuumSectorFeedText
    (Sector115.ProjectionSectorStabilityCriterion.vacuumSectorStability
      (ImportedReducerSurface.sprint115ProjectionCriterion surface))
    (Sector115.VacuumSectorStability.vacuumSectorInvariant
      (Sector115.ProjectionSectorStabilityCriterion.vacuumSectorStability
        (ImportedReducerSurface.sprint115ProjectionCriterion surface)))
    (Sector115.VacuumSectorStability.vacuumSectorInvariantIsTrue
      (Sector115.ProjectionSectorStabilityCriterion.vacuumSectorStability
        (ImportedReducerSurface.sprint115ProjectionCriterion surface)))
    vacuumSectorFeedInhabited
    refl
    vacuumSectorStabilityProvedHere
    refl
    supplied-feed-consumed

leakageExclusionFeedFrom :
  ImportedReducerSurface ->
  LeakageExclusionFeed
leakageExclusionFeedFrom surface =
  mkLeakageExclusionFeed
    leakageExclusionFeedText
    (Sector115.ProjectionSectorStabilityCriterion.leakageExclusion
      (ImportedReducerSurface.sprint115ProjectionCriterion surface))
    (Sector115.LeakageExclusion.gaugeSectorLeakageExcluded
      (Sector115.ProjectionSectorStabilityCriterion.leakageExclusion
        (ImportedReducerSurface.sprint115ProjectionCriterion surface)))
    (Sector115.LeakageExclusion.gaugeSectorLeakageExcludedIsTrue
      (Sector115.ProjectionSectorStabilityCriterion.leakageExclusion
        (ImportedReducerSurface.sprint115ProjectionCriterion surface)))
    (Sector115.LeakageExclusion.vacuumSectorLeakageExcluded
      (Sector115.ProjectionSectorStabilityCriterion.leakageExclusion
        (ImportedReducerSurface.sprint115ProjectionCriterion surface)))
    (Sector115.LeakageExclusion.vacuumSectorLeakageExcludedIsTrue
      (Sector115.ProjectionSectorStabilityCriterion.leakageExclusion
        (ImportedReducerSurface.sprint115ProjectionCriterion surface)))
    (Sector115.LeakageExclusion.nonVacuumSectorLeakageExcluded
      (Sector115.ProjectionSectorStabilityCriterion.leakageExclusion
        (ImportedReducerSurface.sprint115ProjectionCriterion surface)))
    (Sector115.LeakageExclusion.nonVacuumSectorLeakageExcludedIsTrue
      (Sector115.ProjectionSectorStabilityCriterion.leakageExclusion
        (ImportedReducerSurface.sprint115ProjectionCriterion surface)))
    leakageExclusionFeedInhabited
    refl
    supplied-feed-consumed

quotientDescentFeedFrom :
  ImportedReducerSurface ->
  QuotientDescentFeed
quotientDescentFeedFrom surface =
  mkQuotientDescentFeed
    quotientDescentFeedText
    (Sector115.ProjectionSectorStabilityCriterion.quotientDescentFeedThrough
      (ImportedReducerSurface.sprint115ProjectionCriterion surface))
    (ImportedReducerSurface.inverseProjectionReceipt surface)
    (Sector115.QuotientDescentFeedThrough.quotientDescentAvailable
      (Sector115.ProjectionSectorStabilityCriterion.quotientDescentFeedThrough
        (ImportedReducerSurface.sprint115ProjectionCriterion surface)))
    (Sector115.QuotientDescentFeedThrough.quotientDescentAvailableIsTrue
      (Sector115.ProjectionSectorStabilityCriterion.quotientDescentFeedThrough
        (ImportedReducerSurface.sprint115ProjectionCriterion surface)))
    (Sector115.QuotientDescentFeedThrough.representativeIndependenceAvailable
      (Sector115.ProjectionSectorStabilityCriterion.quotientDescentFeedThrough
        (ImportedReducerSurface.sprint115ProjectionCriterion surface)))
    (Sector115.QuotientDescentFeedThrough.representativeIndependenceAvailableIsTrue
      (Sector115.ProjectionSectorStabilityCriterion.quotientDescentFeedThrough
        (ImportedReducerSurface.sprint115ProjectionCriterion surface)))
    (Sector115.QuotientDescentFeedThrough.sprint114FeedThroughCompatible
      (Sector115.ProjectionSectorStabilityCriterion.quotientDescentFeedThrough
        (ImportedReducerSurface.sprint115ProjectionCriterion surface)))
    (Sector115.QuotientDescentFeedThrough.sprint114FeedThroughCompatibleIsTrue
      (Sector115.ProjectionSectorStabilityCriterion.quotientDescentFeedThrough
        (ImportedReducerSurface.sprint115ProjectionCriterion surface)))
    quotientDescentFeedInhabited
    refl
    supplied-feed-consumed

closureReducerFrom :
  ImportedReducerSurface ->
  SectorClosureReducer
closureReducerFrom surface =
  mkSectorClosureReducer
    surface
    (projectionCommutatorFeedFrom surface)
    (physicalSectorFeedFrom surface)
    (vacuumSectorFeedFrom surface)
    (leakageExclusionFeedFrom surface)
    (quotientDescentFeedFrom surface)
    (ImportedReducerSurface.sprint115ApproximateInverseCriterion surface)
    closureReducerText
    closureReducerInhabited
    refl
    sectorCriterionClosedHere
    refl
    externalProjectionSectorClosedHere
    refl
    conditional-sector-reducer-inhabited

canonicalTheoremBoundary : TheoremBoundary
canonicalTheoremBoundary =
  mkTheoremBoundary
    failClosedBoundaryText
    projectionCommutatorStabilityProvedHere
    refl
    physicalSectorStabilityProvedHere
    refl
    vacuumSectorStabilityProvedHere
    refl
    sectorStabilityTheoremProvedHere
    refl
    inverseProjectionClosureTheoremProvedHere
    refl
    externalProjectionSectorClosedHere
    refl
    sectorCriterionClosedHere
    refl
    clayYangMillsPromoted
    refl
    fail-closed-nonpromotion

reducerReceiptFrom :
  ImportedReducerSurface ->
  YMSprint116SectorStabilityClosureReducerReceipt
reducerReceiptFrom surface =
  mkYMSprint116SectorStabilityClosureReducerReceipt
    sprintNumber
    modulePath
    surface
    (closureReducerFrom surface)
    canonicalTheoremBoundary
    canonicalReducerLanes
    (criterionStatementText
     ∷ projectionCommutatorFeedText
     ∷ physicalSectorFeedText
     ∷ vacuumSectorFeedText
     ∷ leakageExclusionFeedText
     ∷ quotientDescentFeedText
     ∷ closureReducerText
     ∷ failClosedBoundaryText
     ∷ sprint115ProjectionSectorStabilityCriterionPath
     ∷ sprint115ApproximateInverseResidualCriterionPath
     ∷ sprint114InverseProjectionClosureCriterionPath
     ∷ [])
    sectorStabilityClosureReducerRecorded
    closureReducerInhabited
    refl
    clayYangMillsPromoted
    refl

canonicalYMSprint116SectorStabilityClosureReducerReceipt :
  YMSprint116SectorStabilityClosureReducerReceipt
canonicalYMSprint116SectorStabilityClosureReducerReceipt =
  reducerReceiptFrom canonicalImportedReducerSurface

canonicalReceipt : YMSprint116SectorStabilityClosureReducerReceipt
canonicalReceipt =
  canonicalYMSprint116SectorStabilityClosureReducerReceipt

canonicalReducerInhabitedIsTrue :
  reducerInhabited canonicalReceipt ≡ true
canonicalReducerInhabitedIsTrue =
  refl

canonicalProjectionCommutatorFeedInhabitedIsTrue :
  ProjectionCommutatorFeed.feedInhabited
    (SectorClosureReducer.projectionCommutatorFeed
      (closureReducer canonicalReceipt)) ≡ true
canonicalProjectionCommutatorFeedInhabitedIsTrue =
  refl

canonicalPhysicalSectorFeedInhabitedIsTrue :
  PhysicalSectorFeed.feedInhabited
    (SectorClosureReducer.physicalSectorFeed
      (closureReducer canonicalReceipt)) ≡ true
canonicalPhysicalSectorFeedInhabitedIsTrue =
  refl

canonicalVacuumSectorFeedInhabitedIsTrue :
  VacuumSectorFeed.feedInhabited
    (SectorClosureReducer.vacuumSectorFeed
      (closureReducer canonicalReceipt)) ≡ true
canonicalVacuumSectorFeedInhabitedIsTrue =
  refl

canonicalLeakageExclusionFeedInhabitedIsTrue :
  LeakageExclusionFeed.feedInhabited
    (SectorClosureReducer.leakageExclusionFeed
      (closureReducer canonicalReceipt)) ≡ true
canonicalLeakageExclusionFeedInhabitedIsTrue =
  refl

canonicalQuotientDescentFeedInhabitedIsTrue :
  QuotientDescentFeed.feedInhabited
    (SectorClosureReducer.quotientDescentFeed
      (closureReducer canonicalReceipt)) ≡ true
canonicalQuotientDescentFeedInhabitedIsTrue =
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

canonicalInverseProjectionClosureTheoremProvedHereIsFalse :
  TheoremBoundary.inverseProjectionClosureTheoremProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalInverseProjectionClosureTheoremProvedHereIsFalse =
  refl

canonicalExternalProjectionSectorClosedHereIsFalse :
  TheoremBoundary.externalProjectionSectorClosedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalExternalProjectionSectorClosedHereIsFalse =
  refl

canonicalSectorCriterionClosedHereIsFalse :
  TheoremBoundary.sectorCriterionClosedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalSectorCriterionClosedHereIsFalse =
  refl

canonicalClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalClayYangMillsPromotedIsFalse =
  refl
