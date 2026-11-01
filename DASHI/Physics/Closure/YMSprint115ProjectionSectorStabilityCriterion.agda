module DASHI.Physics.Closure.YMSprint115ProjectionSectorStabilityCriterion where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint114InverseProjectionClosureCriterion
  as Inverse114
import DASHI.Physics.Closure.YMSprint113InverseProjectionResidualAssembly
  as Residual113

------------------------------------------------------------------------
-- Sprint115 projection-sector stability criterion.
--
-- This module advances the Sprint114 inverse/projection closure criterion
-- into a projection-sector stability criterion.  It packages supplied
-- projection commutator, physical-sector, vacuum-sector, leakage-exclusion,
-- quotient-descent, and feed-through fields into one inhabited criterion.
-- The analytic stability and descent theorems remain explicit open/false
-- flags, and Clay Yang-Mills promotion remains false.

sprintNumber : Nat
sprintNumber = 115

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint115ProjectionSectorStabilityCriterion.agda"

sprint114InverseProjectionClosureCriterionPath : String
sprint114InverseProjectionClosureCriterionPath =
  "DASHI/Physics/Closure/YMSprint114InverseProjectionClosureCriterion.agda"

sprint113InverseProjectionResidualAssemblyPath : String
sprint113InverseProjectionResidualAssemblyPath =
  "DASHI/Physics/Closure/YMSprint113InverseProjectionResidualAssembly.agda"

projectionSectorStabilityCriterionRecorded : Bool
projectionSectorStabilityCriterionRecorded = true

projectionCommutatorStabilityCriterionInhabited : Bool
projectionCommutatorStabilityCriterionInhabited = true

physicalSectorStabilityCriterionInhabited : Bool
physicalSectorStabilityCriterionInhabited = true

vacuumSectorStabilityCriterionInhabited : Bool
vacuumSectorStabilityCriterionInhabited = true

leakageExclusionCriterionInhabited : Bool
leakageExclusionCriterionInhabited = true

quotientDescentFeedThroughCriterionInhabited : Bool
quotientDescentFeedThroughCriterionInhabited = true

conditionalSectorStabilityCriterionInhabited : Bool
conditionalSectorStabilityCriterionInhabited = true

projectionCommutatorStabilityProvedHere : Bool
projectionCommutatorStabilityProvedHere = false

physicalSectorStabilityProvedHere : Bool
physicalSectorStabilityProvedHere = false

vacuumSectorStabilityProvedHere : Bool
vacuumSectorStabilityProvedHere = false

leakageExclusionTheoremProvedHere : Bool
leakageExclusionTheoremProvedHere = false

quotientDescentTheoremProvedHere : Bool
quotientDescentTheoremProvedHere = false

sectorStabilityTheoremProvedHere : Bool
sectorStabilityTheoremProvedHere = false

inverseProjectionClosureTheoremProvedHere : Bool
inverseProjectionClosureTheoremProvedHere = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

criterionStatementText : String
criterionStatementText =
  "Sprint115 projection-sector stability criterion: if projection commutators are supplied stable, physical and vacuum sectors are supplied stable, leakage into gauge/vacuum/non-vacuum complements is excluded, and quotient descent feeds the Sprint114 inverse/projection criterion, then the projection-sector stability criterion is inhabited."

projectionCommutatorStabilityText : String
projectionCommutatorStabilityText =
  "Projection commutator stability: consume supplied control for Pi_phys E_a versus E_a Pi_a,phys and Pi_a,phys P_a versus P_a Pi_phys on the same admissible quotient window."

physicalSectorStabilityText : String
physicalSectorStabilityText =
  "Physical sector stability: consume supplied invariance of the finite and continuum physical sectors under the E_a/P_a comparison convention already assembled in Sprint113 and consumed in Sprint114."

vacuumSectorStabilityText : String
vacuumSectorStabilityText =
  "Vacuum sector stability: consume supplied preservation of the isolated vacuum sector and its non-vacuum complement without changing the common-carrier labels."

leakageExclusionText : String
leakageExclusionText =
  "Leakage exclusion: consume supplied exclusion of gauge-sector, vacuum-sector, and non-vacuum-sector leakage during projection, interpolation, sampling, and quotient descent."

quotientDescentFeedThroughText : String
quotientDescentFeedThroughText =
  "Quotient descent feed-through: consume supplied representative independence and quotient descent so the projection-sector criterion factors through the Sprint114 inverse/projection closure receipt."

nonPromotionBoundaryText : String
nonPromotionBoundaryText =
  "Sprint115 records a conditional projection-sector stability criterion only.  It proves no unconditional projection commutator theorem, sector theorem, leakage theorem, quotient descent theorem, inverse/projection closure theorem, spectral gap theorem, mass gap theorem, or Clay Yang-Mills promotion."

data SectorStabilityLane : Set where
  sprint114-inverse-closure-lane :
    SectorStabilityLane
  sprint113-residual-assembly-lane :
    SectorStabilityLane
  projection-commutator-stability-lane :
    SectorStabilityLane
  physical-sector-stability-lane :
    SectorStabilityLane
  vacuum-sector-stability-lane :
    SectorStabilityLane
  leakage-exclusion-lane :
    SectorStabilityLane
  quotient-descent-feed-through-lane :
    SectorStabilityLane
  conditional-sector-stability-lane :
    SectorStabilityLane
  theorem-boundary-lane :
    SectorStabilityLane

data SectorStabilityStatus : Set where
  imported-sprint114-inverse-closure :
    SectorStabilityStatus
  imported-sprint113-residual-assembly :
    SectorStabilityStatus
  supplied-field-consumed :
    SectorStabilityStatus
  projection-sector-criterion-inhabited :
    SectorStabilityStatus
  analytic-theorem-open :
    SectorStabilityStatus
  fail-closed-nonpromotion :
    SectorStabilityStatus

data SectorStabilityFieldKind : Set where
  embedding-projection-commutator-stable :
    SectorStabilityFieldKind
  sampling-projection-commutator-stable :
    SectorStabilityFieldKind
  physical-sector-invariant :
    SectorStabilityFieldKind
  vacuum-sector-invariant :
    SectorStabilityFieldKind
  gauge-sector-leakage-excluded :
    SectorStabilityFieldKind
  vacuum-sector-leakage-excluded :
    SectorStabilityFieldKind
  non-vacuum-sector-leakage-excluded :
    SectorStabilityFieldKind
  quotient-descent-available :
    SectorStabilityFieldKind
  representative-independence-available :
    SectorStabilityFieldKind
  sprint114-feed-through-compatible :
    SectorStabilityFieldKind

canonicalSectorStabilityLanes : List SectorStabilityLane
canonicalSectorStabilityLanes =
  sprint114-inverse-closure-lane
  ∷ sprint113-residual-assembly-lane
  ∷ projection-commutator-stability-lane
  ∷ physical-sector-stability-lane
  ∷ vacuum-sector-stability-lane
  ∷ leakage-exclusion-lane
  ∷ quotient-descent-feed-through-lane
  ∷ conditional-sector-stability-lane
  ∷ theorem-boundary-lane
  ∷ []

canonicalSectorStabilityFieldKinds : List SectorStabilityFieldKind
canonicalSectorStabilityFieldKinds =
  embedding-projection-commutator-stable
  ∷ sampling-projection-commutator-stable
  ∷ physical-sector-invariant
  ∷ vacuum-sector-invariant
  ∷ gauge-sector-leakage-excluded
  ∷ vacuum-sector-leakage-excluded
  ∷ non-vacuum-sector-leakage-excluded
  ∷ quotient-descent-available
  ∷ representative-independence-available
  ∷ sprint114-feed-through-compatible
  ∷ []

record ImportedProjectionSectorSurface : Setω where
  constructor mkImportedProjectionSectorSurface
  field
    sprint114Receipt :
      Inverse114.YMSprint114InverseProjectionClosureCriterionReceipt
    sprint113Receipt :
      Residual113.YMSprint113InverseProjectionResidualAssemblyReceipt
    sprint114ProjectionSectorCriterion :
      Inverse114.ProjectionSectorClosureCriterion
    sprint113ProjectionAssembly :
      Residual113.ProjectionStabilityAssembly
    sprint113PhysicalSectorAssembly :
      Residual113.SectorStabilityAssembly
    sprint113VacuumSectorAssembly :
      Residual113.SectorStabilityAssembly
    sprint114CriterionInhabited :
      Bool
    sprint114CriterionInhabitedIsTrue :
      sprint114CriterionInhabited ≡ true
    sprint114InverseProjectionTheoremOpen :
      Bool
    sprint114InverseProjectionTheoremOpenIsFalse :
      sprint114InverseProjectionTheoremOpen ≡ false
    sprint113ProjectionTheoremOpen :
      Bool
    sprint113ProjectionTheoremOpenIsFalse :
      sprint113ProjectionTheoremOpen ≡ false
    sprint113PhysicalSectorTheoremOpen :
      Bool
    sprint113PhysicalSectorTheoremOpenIsFalse :
      sprint113PhysicalSectorTheoremOpen ≡ false
    sprint113VacuumSectorTheoremOpen :
      Bool
    sprint113VacuumSectorTheoremOpenIsFalse :
      sprint113VacuumSectorTheoremOpen ≡ false
    status :
      SectorStabilityStatus

record SuppliedProjectionSectorFields : Set where
  constructor mkSuppliedProjectionSectorFields
  field
    embeddingProjectionCommutatorStable :
      Bool
    samplingProjectionCommutatorStable :
      Bool
    physicalSectorInvariant :
      Bool
    vacuumSectorInvariant :
      Bool
    gaugeSectorLeakageExcluded :
      Bool
    vacuumSectorLeakageExcluded :
      Bool
    nonVacuumSectorLeakageExcluded :
      Bool
    quotientDescentAvailable :
      Bool
    representativeIndependenceAvailable :
      Bool
    sprint114FeedThroughCompatible :
      Bool
    embeddingProjectionCommutatorStableIsTrue :
      embeddingProjectionCommutatorStable ≡ true
    samplingProjectionCommutatorStableIsTrue :
      samplingProjectionCommutatorStable ≡ true
    physicalSectorInvariantIsTrue :
      physicalSectorInvariant ≡ true
    vacuumSectorInvariantIsTrue :
      vacuumSectorInvariant ≡ true
    gaugeSectorLeakageExcludedIsTrue :
      gaugeSectorLeakageExcluded ≡ true
    vacuumSectorLeakageExcludedIsTrue :
      vacuumSectorLeakageExcluded ≡ true
    nonVacuumSectorLeakageExcludedIsTrue :
      nonVacuumSectorLeakageExcluded ≡ true
    quotientDescentAvailableIsTrue :
      quotientDescentAvailable ≡ true
    representativeIndependenceAvailableIsTrue :
      representativeIndependenceAvailable ≡ true
    sprint114FeedThroughCompatibleIsTrue :
      sprint114FeedThroughCompatible ≡ true

record ConsumedSectorField : Set where
  constructor mkConsumedSectorField
  field
    kind :
      SectorStabilityFieldKind
    lane :
      SectorStabilityLane
    statement :
      String
    supplied :
      Bool
    suppliedIsTrue :
      supplied ≡ true
    consumedHere :
      Bool
    consumedHereIsTrue :
      consumedHere ≡ true
    status :
      SectorStabilityStatus

record ProjectionCommutatorStability : Setω where
  constructor mkProjectionCommutatorStability
  field
    sprint113ProjectionAssembly :
      Residual113.ProjectionStabilityAssembly
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
    criterionInhabited :
      Bool
    criterionInhabitedIsTrue :
      criterionInhabited ≡ true
    theoremProvedHere :
      Bool
    theoremProvedHereIsFalse :
      theoremProvedHere ≡ false
    status :
      SectorStabilityStatus

record PhysicalSectorStability : Setω where
  constructor mkPhysicalSectorStability
  field
    sprint113PhysicalSectorAssembly :
      Residual113.SectorStabilityAssembly
    physicalSectorInvariant :
      Bool
    physicalSectorInvariantIsTrue :
      physicalSectorInvariant ≡ true
    projectionCommutatorsStable :
      Bool
    projectionCommutatorsStableIsTrue :
      projectionCommutatorsStable ≡ true
    criterionInhabited :
      Bool
    criterionInhabitedIsTrue :
      criterionInhabited ≡ true
    theoremProvedHere :
      Bool
    theoremProvedHereIsFalse :
      theoremProvedHere ≡ false
    status :
      SectorStabilityStatus

record VacuumSectorStability : Setω where
  constructor mkVacuumSectorStability
  field
    sprint113VacuumSectorAssembly :
      Residual113.SectorStabilityAssembly
    vacuumSectorInvariant :
      Bool
    vacuumSectorInvariantIsTrue :
      vacuumSectorInvariant ≡ true
    projectionCommutatorsStable :
      Bool
    projectionCommutatorsStableIsTrue :
      projectionCommutatorsStable ≡ true
    criterionInhabited :
      Bool
    criterionInhabitedIsTrue :
      criterionInhabited ≡ true
    theoremProvedHere :
      Bool
    theoremProvedHereIsFalse :
      theoremProvedHere ≡ false
    status :
      SectorStabilityStatus

record LeakageExclusion : Set where
  constructor mkLeakageExclusion
  field
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
    criterionInhabited :
      Bool
    criterionInhabitedIsTrue :
      criterionInhabited ≡ true
    theoremProvedHere :
      Bool
    theoremProvedHereIsFalse :
      theoremProvedHere ≡ false
    status :
      SectorStabilityStatus

record QuotientDescentFeedThrough : Setω where
  constructor mkQuotientDescentFeedThrough
  field
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
    criterionInhabited :
      Bool
    criterionInhabitedIsTrue :
      criterionInhabited ≡ true
    theoremProvedHere :
      Bool
    theoremProvedHereIsFalse :
      theoremProvedHere ≡ false
    status :
      SectorStabilityStatus

record ProjectionSectorStabilityCriterion : Setω where
  constructor mkProjectionSectorStabilityCriterion
  field
    projectionCommutatorStability :
      ProjectionCommutatorStability
    physicalSectorStability :
      PhysicalSectorStability
    vacuumSectorStability :
      VacuumSectorStability
    leakageExclusion :
      LeakageExclusion
    quotientDescentFeedThrough :
      QuotientDescentFeedThrough
    criterionStatement :
      String
    criterionInhabited :
      Bool
    criterionInhabitedIsTrue :
      criterionInhabited ≡ true
    theoremProvedHere :
      Bool
    theoremProvedHereIsFalse :
      theoremProvedHere ≡ false
    status :
      SectorStabilityStatus

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
    leakageExclusionTheoremProvedHereFlag :
      Bool
    leakageExclusionTheoremProvedHereIsFalse :
      leakageExclusionTheoremProvedHereFlag ≡ false
    quotientDescentTheoremProvedHereFlag :
      Bool
    quotientDescentTheoremProvedHereIsFalse :
      quotientDescentTheoremProvedHereFlag ≡ false
    sectorStabilityTheoremProvedHereFlag :
      Bool
    sectorStabilityTheoremProvedHereIsFalse :
      sectorStabilityTheoremProvedHereFlag ≡ false
    inverseProjectionClosureTheoremProvedHereFlag :
      Bool
    inverseProjectionClosureTheoremProvedHereIsFalse :
      inverseProjectionClosureTheoremProvedHereFlag ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    status :
      SectorStabilityStatus

record YMSprint115ProjectionSectorStabilityCriterionReceipt : Setω where
  constructor mkYMSprint115ProjectionSectorStabilityCriterionReceipt
  field
    sprint :
      Nat
    evidencePath :
      String
    importedSurface :
      ImportedProjectionSectorSurface
    suppliedFields :
      SuppliedProjectionSectorFields
    consumedFields :
      List ConsumedSectorField
    projectionSectorStabilityCriterion :
      ProjectionSectorStabilityCriterion
    theoremBoundary :
      TheoremBoundary
    lanes :
      List SectorStabilityLane
    fieldKinds :
      List SectorStabilityFieldKind
    evidenceLedger :
      List String
    criterionRecorded :
      Bool
    criterionInhabited :
      Bool
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false

open YMSprint115ProjectionSectorStabilityCriterionReceipt public

canonicalImportedProjectionSectorSurface :
  ImportedProjectionSectorSurface
canonicalImportedProjectionSectorSurface =
  mkImportedProjectionSectorSurface
    Inverse114.canonicalReceipt
    Residual113.canonicalReceipt
    (Inverse114.projectionSectorCriterion Inverse114.canonicalReceipt)
    Residual113.canonicalProjectionStability
    Residual113.canonicalPhysicalSectorStability
    Residual113.canonicalVacuumSectorStability
    (Inverse114.criterionInhabited Inverse114.canonicalReceipt)
    Inverse114.canonicalCriterionInhabitedIsTrue
    (Inverse114.TheoremBoundary.inverseProjectionClosureTheoremProvedHereFlag
      (Inverse114.theoremBoundary Inverse114.canonicalReceipt))
    Inverse114.canonicalInverseProjectionClosureTheoremProvedHereIsFalse
    (Residual113.TheoremBoundary.projectionStabilityProvedHereFlag
      (Residual113.theoremBoundary Residual113.canonicalReceipt))
    Residual113.canonicalProjectionStabilityProvedHereIsFalse
    (Residual113.TheoremBoundary.physicalSectorStabilityProvedHereFlag
      (Residual113.theoremBoundary Residual113.canonicalReceipt))
    Residual113.canonicalPhysicalSectorStabilityProvedHereIsFalse
    (Residual113.TheoremBoundary.vacuumSectorStabilityProvedHereFlag
      (Residual113.theoremBoundary Residual113.canonicalReceipt))
    Residual113.canonicalVacuumSectorStabilityProvedHereIsFalse
    imported-sprint114-inverse-closure

canonicalSuppliedProjectionSectorFields :
  SuppliedProjectionSectorFields
canonicalSuppliedProjectionSectorFields =
  mkSuppliedProjectionSectorFields
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

consumedSectorFieldsFrom :
  SuppliedProjectionSectorFields -> List ConsumedSectorField
consumedSectorFieldsFrom fields =
  mkConsumedSectorField
    embedding-projection-commutator-stable
    projection-commutator-stability-lane
    projectionCommutatorStabilityText
    (SuppliedProjectionSectorFields.embeddingProjectionCommutatorStable fields)
    (SuppliedProjectionSectorFields.embeddingProjectionCommutatorStableIsTrue fields)
    projectionCommutatorStabilityCriterionInhabited
    refl
    supplied-field-consumed
  ∷ mkConsumedSectorField
    sampling-projection-commutator-stable
    projection-commutator-stability-lane
    projectionCommutatorStabilityText
    (SuppliedProjectionSectorFields.samplingProjectionCommutatorStable fields)
    (SuppliedProjectionSectorFields.samplingProjectionCommutatorStableIsTrue fields)
    projectionCommutatorStabilityCriterionInhabited
    refl
    supplied-field-consumed
  ∷ mkConsumedSectorField
    physical-sector-invariant
    physical-sector-stability-lane
    physicalSectorStabilityText
    (SuppliedProjectionSectorFields.physicalSectorInvariant fields)
    (SuppliedProjectionSectorFields.physicalSectorInvariantIsTrue fields)
    physicalSectorStabilityCriterionInhabited
    refl
    supplied-field-consumed
  ∷ mkConsumedSectorField
    vacuum-sector-invariant
    vacuum-sector-stability-lane
    vacuumSectorStabilityText
    (SuppliedProjectionSectorFields.vacuumSectorInvariant fields)
    (SuppliedProjectionSectorFields.vacuumSectorInvariantIsTrue fields)
    vacuumSectorStabilityCriterionInhabited
    refl
    supplied-field-consumed
  ∷ mkConsumedSectorField
    gauge-sector-leakage-excluded
    leakage-exclusion-lane
    leakageExclusionText
    (SuppliedProjectionSectorFields.gaugeSectorLeakageExcluded fields)
    (SuppliedProjectionSectorFields.gaugeSectorLeakageExcludedIsTrue fields)
    leakageExclusionCriterionInhabited
    refl
    supplied-field-consumed
  ∷ mkConsumedSectorField
    vacuum-sector-leakage-excluded
    leakage-exclusion-lane
    leakageExclusionText
    (SuppliedProjectionSectorFields.vacuumSectorLeakageExcluded fields)
    (SuppliedProjectionSectorFields.vacuumSectorLeakageExcludedIsTrue fields)
    leakageExclusionCriterionInhabited
    refl
    supplied-field-consumed
  ∷ mkConsumedSectorField
    non-vacuum-sector-leakage-excluded
    leakage-exclusion-lane
    leakageExclusionText
    (SuppliedProjectionSectorFields.nonVacuumSectorLeakageExcluded fields)
    (SuppliedProjectionSectorFields.nonVacuumSectorLeakageExcludedIsTrue fields)
    leakageExclusionCriterionInhabited
    refl
    supplied-field-consumed
  ∷ mkConsumedSectorField
    quotient-descent-available
    quotient-descent-feed-through-lane
    quotientDescentFeedThroughText
    (SuppliedProjectionSectorFields.quotientDescentAvailable fields)
    (SuppliedProjectionSectorFields.quotientDescentAvailableIsTrue fields)
    quotientDescentFeedThroughCriterionInhabited
    refl
    supplied-field-consumed
  ∷ mkConsumedSectorField
    representative-independence-available
    quotient-descent-feed-through-lane
    quotientDescentFeedThroughText
    (SuppliedProjectionSectorFields.representativeIndependenceAvailable fields)
    (SuppliedProjectionSectorFields.representativeIndependenceAvailableIsTrue fields)
    quotientDescentFeedThroughCriterionInhabited
    refl
    supplied-field-consumed
  ∷ mkConsumedSectorField
    sprint114-feed-through-compatible
    quotient-descent-feed-through-lane
    quotientDescentFeedThroughText
    (SuppliedProjectionSectorFields.sprint114FeedThroughCompatible fields)
    (SuppliedProjectionSectorFields.sprint114FeedThroughCompatibleIsTrue fields)
    quotientDescentFeedThroughCriterionInhabited
    refl
    supplied-field-consumed
  ∷ []

projectionCommutatorStabilityFrom :
  ImportedProjectionSectorSurface ->
  SuppliedProjectionSectorFields ->
  ProjectionCommutatorStability
projectionCommutatorStabilityFrom surface fields =
  mkProjectionCommutatorStability
    (ImportedProjectionSectorSurface.sprint113ProjectionAssembly surface)
    (ImportedProjectionSectorSurface.sprint114ProjectionSectorCriterion surface)
    (SuppliedProjectionSectorFields.embeddingProjectionCommutatorStable fields)
    (SuppliedProjectionSectorFields.embeddingProjectionCommutatorStableIsTrue fields)
    (SuppliedProjectionSectorFields.samplingProjectionCommutatorStable fields)
    (SuppliedProjectionSectorFields.samplingProjectionCommutatorStableIsTrue fields)
    projectionCommutatorStabilityCriterionInhabited
    refl
    projectionCommutatorStabilityProvedHere
    refl
    projection-sector-criterion-inhabited

physicalSectorStabilityFrom :
  ImportedProjectionSectorSurface ->
  SuppliedProjectionSectorFields ->
  PhysicalSectorStability
physicalSectorStabilityFrom surface fields =
  mkPhysicalSectorStability
    (ImportedProjectionSectorSurface.sprint113PhysicalSectorAssembly surface)
    (SuppliedProjectionSectorFields.physicalSectorInvariant fields)
    (SuppliedProjectionSectorFields.physicalSectorInvariantIsTrue fields)
    projectionCommutatorStabilityCriterionInhabited
    refl
    physicalSectorStabilityCriterionInhabited
    refl
    physicalSectorStabilityProvedHere
    refl
    projection-sector-criterion-inhabited

vacuumSectorStabilityFrom :
  ImportedProjectionSectorSurface ->
  SuppliedProjectionSectorFields ->
  VacuumSectorStability
vacuumSectorStabilityFrom surface fields =
  mkVacuumSectorStability
    (ImportedProjectionSectorSurface.sprint113VacuumSectorAssembly surface)
    (SuppliedProjectionSectorFields.vacuumSectorInvariant fields)
    (SuppliedProjectionSectorFields.vacuumSectorInvariantIsTrue fields)
    projectionCommutatorStabilityCriterionInhabited
    refl
    vacuumSectorStabilityCriterionInhabited
    refl
    vacuumSectorStabilityProvedHere
    refl
    projection-sector-criterion-inhabited

leakageExclusionFrom :
  SuppliedProjectionSectorFields -> LeakageExclusion
leakageExclusionFrom fields =
  mkLeakageExclusion
    (SuppliedProjectionSectorFields.gaugeSectorLeakageExcluded fields)
    (SuppliedProjectionSectorFields.gaugeSectorLeakageExcludedIsTrue fields)
    (SuppliedProjectionSectorFields.vacuumSectorLeakageExcluded fields)
    (SuppliedProjectionSectorFields.vacuumSectorLeakageExcludedIsTrue fields)
    (SuppliedProjectionSectorFields.nonVacuumSectorLeakageExcluded fields)
    (SuppliedProjectionSectorFields.nonVacuumSectorLeakageExcludedIsTrue fields)
    leakageExclusionCriterionInhabited
    refl
    leakageExclusionTheoremProvedHere
    refl
    projection-sector-criterion-inhabited

quotientDescentFeedThroughFrom :
  ImportedProjectionSectorSurface ->
  SuppliedProjectionSectorFields ->
  QuotientDescentFeedThrough
quotientDescentFeedThroughFrom surface fields =
  mkQuotientDescentFeedThrough
    (ImportedProjectionSectorSurface.sprint114Receipt surface)
    (SuppliedProjectionSectorFields.quotientDescentAvailable fields)
    (SuppliedProjectionSectorFields.quotientDescentAvailableIsTrue fields)
    (SuppliedProjectionSectorFields.representativeIndependenceAvailable fields)
    (SuppliedProjectionSectorFields.representativeIndependenceAvailableIsTrue fields)
    (SuppliedProjectionSectorFields.sprint114FeedThroughCompatible fields)
    (SuppliedProjectionSectorFields.sprint114FeedThroughCompatibleIsTrue fields)
    quotientDescentFeedThroughCriterionInhabited
    refl
    quotientDescentTheoremProvedHere
    refl
    projection-sector-criterion-inhabited

sectorStabilityCriterionFrom :
  ImportedProjectionSectorSurface ->
  SuppliedProjectionSectorFields ->
  ProjectionSectorStabilityCriterion
sectorStabilityCriterionFrom surface fields =
  mkProjectionSectorStabilityCriterion
    (projectionCommutatorStabilityFrom surface fields)
    (physicalSectorStabilityFrom surface fields)
    (vacuumSectorStabilityFrom surface fields)
    (leakageExclusionFrom fields)
    (quotientDescentFeedThroughFrom surface fields)
    criterionStatementText
    conditionalSectorStabilityCriterionInhabited
    refl
    sectorStabilityTheoremProvedHere
    refl
    projection-sector-criterion-inhabited

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
    leakageExclusionTheoremProvedHere
    refl
    quotientDescentTheoremProvedHere
    refl
    sectorStabilityTheoremProvedHere
    refl
    inverseProjectionClosureTheoremProvedHere
    refl
    clayYangMillsPromoted
    refl
    fail-closed-nonpromotion

criterionReceiptFrom :
  ImportedProjectionSectorSurface ->
  SuppliedProjectionSectorFields ->
  YMSprint115ProjectionSectorStabilityCriterionReceipt
criterionReceiptFrom surface fields =
  mkYMSprint115ProjectionSectorStabilityCriterionReceipt
    sprintNumber
    modulePath
    surface
    fields
    (consumedSectorFieldsFrom fields)
    (sectorStabilityCriterionFrom surface fields)
    canonicalTheoremBoundary
    canonicalSectorStabilityLanes
    canonicalSectorStabilityFieldKinds
    (criterionStatementText
     ∷ projectionCommutatorStabilityText
     ∷ physicalSectorStabilityText
     ∷ vacuumSectorStabilityText
     ∷ leakageExclusionText
     ∷ quotientDescentFeedThroughText
     ∷ nonPromotionBoundaryText
     ∷ sprint114InverseProjectionClosureCriterionPath
     ∷ sprint113InverseProjectionResidualAssemblyPath
     ∷ [])
    projectionSectorStabilityCriterionRecorded
    conditionalSectorStabilityCriterionInhabited
    clayYangMillsPromoted
    refl

canonicalYMSprint115ProjectionSectorStabilityCriterionReceipt :
  YMSprint115ProjectionSectorStabilityCriterionReceipt
canonicalYMSprint115ProjectionSectorStabilityCriterionReceipt =
  criterionReceiptFrom
    canonicalImportedProjectionSectorSurface
    canonicalSuppliedProjectionSectorFields

canonicalReceipt :
  YMSprint115ProjectionSectorStabilityCriterionReceipt
canonicalReceipt =
  canonicalYMSprint115ProjectionSectorStabilityCriterionReceipt

canonicalCriterionInhabitedIsTrue :
  criterionInhabited canonicalReceipt ≡ true
canonicalCriterionInhabitedIsTrue =
  refl

canonicalProjectionCommutatorCriterionInhabitedIsTrue :
  ProjectionCommutatorStability.criterionInhabited
    (ProjectionSectorStabilityCriterion.projectionCommutatorStability
      (projectionSectorStabilityCriterion canonicalReceipt)) ≡ true
canonicalProjectionCommutatorCriterionInhabitedIsTrue =
  refl

canonicalPhysicalSectorCriterionInhabitedIsTrue :
  PhysicalSectorStability.criterionInhabited
    (ProjectionSectorStabilityCriterion.physicalSectorStability
      (projectionSectorStabilityCriterion canonicalReceipt)) ≡ true
canonicalPhysicalSectorCriterionInhabitedIsTrue =
  refl

canonicalVacuumSectorCriterionInhabitedIsTrue :
  VacuumSectorStability.criterionInhabited
    (ProjectionSectorStabilityCriterion.vacuumSectorStability
      (projectionSectorStabilityCriterion canonicalReceipt)) ≡ true
canonicalVacuumSectorCriterionInhabitedIsTrue =
  refl

canonicalLeakageExclusionCriterionInhabitedIsTrue :
  LeakageExclusion.criterionInhabited
    (ProjectionSectorStabilityCriterion.leakageExclusion
      (projectionSectorStabilityCriterion canonicalReceipt)) ≡ true
canonicalLeakageExclusionCriterionInhabitedIsTrue =
  refl

canonicalQuotientDescentFeedThroughCriterionInhabitedIsTrue :
  QuotientDescentFeedThrough.criterionInhabited
    (ProjectionSectorStabilityCriterion.quotientDescentFeedThrough
      (projectionSectorStabilityCriterion canonicalReceipt)) ≡ true
canonicalQuotientDescentFeedThroughCriterionInhabitedIsTrue =
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

canonicalLeakageExclusionTheoremProvedHereIsFalse :
  TheoremBoundary.leakageExclusionTheoremProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalLeakageExclusionTheoremProvedHereIsFalse =
  refl

canonicalQuotientDescentTheoremProvedHereIsFalse :
  TheoremBoundary.quotientDescentTheoremProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalQuotientDescentTheoremProvedHereIsFalse =
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

canonicalClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalClayYangMillsPromotedIsFalse =
  refl
