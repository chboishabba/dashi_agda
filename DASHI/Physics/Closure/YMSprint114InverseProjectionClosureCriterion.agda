module DASHI.Physics.Closure.YMSprint114InverseProjectionClosureCriterion where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint113InverseProjectionResidualAssembly
  as Residual113

------------------------------------------------------------------------
-- Sprint114 inverse projection closure criterion.
--
-- This module turns the Sprint113 residual assembly into a conditional
-- closure criterion.  It consumes supplied flags for left and right residual
-- vanishing, projection commutator stability, physical/vacuum sector
-- stability, quotient/norm-window availability, and common-carrier feed
-- admissibility.  It records the resulting criterion as inhabited when those
-- flags are supplied together.  It proves no analytic residual theorem, no
-- sector theorem, no common-carrier construction theorem, and no Clay
-- Yang-Mills promotion.

sprintNumber : Nat
sprintNumber = 114

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint114InverseProjectionClosureCriterion.agda"

sprint113InverseProjectionResidualAssemblyPath : String
sprint113InverseProjectionResidualAssemblyPath =
  "DASHI/Physics/Closure/YMSprint113InverseProjectionResidualAssembly.agda"

sprint114QuadratureResidualClosureCriterionPath : String
sprint114QuadratureResidualClosureCriterionPath =
  "DASHI/Physics/Closure/YMSprint114QuadratureResidualClosureCriterion.agda"

sprint114QuadratureResidualClosureCriterionImported : Bool
sprint114QuadratureResidualClosureCriterionImported = false

inverseProjectionClosureCriterionRecorded : Bool
inverseProjectionClosureCriterionRecorded = true

residualVanishingAssumptionsConsumed : Bool
residualVanishingAssumptionsConsumed = true

projectionCommutatorStabilityConsumed : Bool
projectionCommutatorStabilityConsumed = true

physicalSectorStabilityConsumed : Bool
physicalSectorStabilityConsumed = true

vacuumSectorStabilityConsumed : Bool
vacuumSectorStabilityConsumed = true

normWindowFlagsConsumedHere : Bool
normWindowFlagsConsumedHere = true

commonCarrierFeedThroughCriterionInhabited : Bool
commonCarrierFeedThroughCriterionInhabited = true

leftInverseResidualVanishesProvedHere : Bool
leftInverseResidualVanishesProvedHere = false

rightInverseResidualVanishesProvedHere : Bool
rightInverseResidualVanishesProvedHere = false

projectionCommutatorStabilityProvedHere : Bool
projectionCommutatorStabilityProvedHere = false

physicalSectorStabilityProvedHere : Bool
physicalSectorStabilityProvedHere = false

vacuumSectorStabilityProvedHere : Bool
vacuumSectorStabilityProvedHere = false

normWindowClosedHere : Bool
normWindowClosedHere = false

commonCarrierConstructionClosedHere : Bool
commonCarrierConstructionClosedHere = false

inverseProjectionClosureTheoremProvedHere : Bool
inverseProjectionClosureTheoremProvedHere = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

criterionStatementText : String
criterionStatementText =
  "Sprint114 inverse projection closure criterion: if the left residual E_a P_a -> Id_H_phys and the right residual P_a E_a -> Id_a,phys vanish on the same admissible a-window, projection commutators are stable, physical and vacuum sectors are stable, quotient descent is compatible, and the norm-window flags are supplied, then the Sprint113 assembled evidence is accepted as a common-carrier feed-through criterion."

leftResidualConsumptionText : String
leftResidualConsumptionText =
  "Left inverse consumption: use the supplied vanishing flag for ||E_a(P_a v) - v||_H_phys on the continuum physical comparison sector; this module records consumption only."

rightResidualConsumptionText : String
rightResidualConsumptionText =
  "Right inverse consumption: use the supplied vanishing flag for ||P_a(E_a u) - u||_a,quot on finite physical gauge-quotient vectors; this module records consumption only."

projectionCommutatorConsumptionText : String
projectionCommutatorConsumptionText =
  "Projection commutator consumption: use supplied stability for Pi_phys E_a versus E_a Pi_a,phys and Pi_a,phys P_a versus P_a Pi_phys under the same quotient convention."

sectorStabilityConsumptionText : String
sectorStabilityConsumptionText =
  "Sector stability consumption: use supplied physical-sector and vacuum-sector stability to exclude leakage between gauge, vacuum, and non-vacuum sectors during E_a/P_a feed-through."

normWindowConsumptionText : String
normWindowConsumptionText =
  "Norm-window consumption: use supplied upper/lower norm-window flags, quotient descent, and representative independence for the common finite/continuum carrier convention."

commonCarrierFeedThroughText : String
commonCarrierFeedThroughText =
  "Common-carrier feed-through: the inhabited criterion packages the supplied residual, projection, sector, quotient, and norm flags into one record consumable by later common-carrier closure modules."

nonPromotionBoundaryText : String
nonPromotionBoundaryText =
  "Sprint114 records a conditional closure criterion only.  It imports Sprint113 residual assembly, references the absent Sprint114 quadrature sibling by path text, proves no analytic theorem, and keeps clayYangMillsPromoted=false."

data CriterionLane : Set where
  sprint113-residual-input-lane :
    CriterionLane
  left-inverse-vanishing-lane :
    CriterionLane
  right-inverse-vanishing-lane :
    CriterionLane
  projection-commutator-stability-lane :
    CriterionLane
  physical-sector-stability-lane :
    CriterionLane
  vacuum-sector-stability-lane :
    CriterionLane
  norm-window-lane :
    CriterionLane
  common-carrier-feed-through-lane :
    CriterionLane
  theorem-boundary-lane :
    CriterionLane

data CriterionStatus : Set where
  imported-sprint113-assembly :
    CriterionStatus
  sibling-path-referenced :
    CriterionStatus
  supplied-assumption-consumed :
    CriterionStatus
  closure-criterion-inhabited :
    CriterionStatus
  theorem-not-proved-here :
    CriterionStatus
  fail-closed-nonpromotion :
    CriterionStatus

data SuppliedFlagKind : Set where
  left-residual-vanishes-flag :
    SuppliedFlagKind
  right-residual-vanishes-flag :
    SuppliedFlagKind
  projection-commutator-stable-flag :
    SuppliedFlagKind
  physical-sector-stable-flag :
    SuppliedFlagKind
  vacuum-sector-stable-flag :
    SuppliedFlagKind
  quotient-descent-stable-flag :
    SuppliedFlagKind
  norm-window-upper-flag :
    SuppliedFlagKind
  norm-window-lower-flag :
    SuppliedFlagKind
  common-carrier-admissible-flag :
    SuppliedFlagKind

canonicalCriterionLanes : List CriterionLane
canonicalCriterionLanes =
  sprint113-residual-input-lane
  ∷ left-inverse-vanishing-lane
  ∷ right-inverse-vanishing-lane
  ∷ projection-commutator-stability-lane
  ∷ physical-sector-stability-lane
  ∷ vacuum-sector-stability-lane
  ∷ norm-window-lane
  ∷ common-carrier-feed-through-lane
  ∷ theorem-boundary-lane
  ∷ []

canonicalSuppliedFlagKinds : List SuppliedFlagKind
canonicalSuppliedFlagKinds =
  left-residual-vanishes-flag
  ∷ right-residual-vanishes-flag
  ∷ projection-commutator-stable-flag
  ∷ physical-sector-stable-flag
  ∷ vacuum-sector-stable-flag
  ∷ quotient-descent-stable-flag
  ∷ norm-window-upper-flag
  ∷ norm-window-lower-flag
  ∷ common-carrier-admissible-flag
  ∷ []

record Sprint113Input : Setω where
  constructor mkSprint113Input
  field
    residualAssemblyReceipt :
      Residual113.YMSprint113InverseProjectionResidualAssemblyReceipt
    residualAssemblyPath :
      String
    quadratureClosureCriterionPath :
      String
    quadratureClosureCriterionImported :
      Bool
    residualAssemblyRecorded :
      Bool
    leftResidualAssembly :
      Residual113.ResidualAssembly
    rightResidualAssembly :
      Residual113.ResidualAssembly
    projectionStabilityAssembly :
      Residual113.ProjectionStabilityAssembly
    physicalSectorStabilityAssembly :
      Residual113.SectorStabilityAssembly
    vacuumSectorStabilityAssembly :
      Residual113.SectorStabilityAssembly
    commonCarrierFeedThroughAssembly :
      Residual113.CommonCarrierFeedThrough
    sprint113ClayPromoted :
      Bool
    sprint113ClayPromotedIsFalse :
      sprint113ClayPromoted ≡ false
    status :
      CriterionStatus

record SuppliedClosureFlags : Set where
  constructor mkSuppliedClosureFlags
  field
    leftResidualVanishes :
      Bool
    rightResidualVanishes :
      Bool
    projectionCommutatorsStable :
      Bool
    physicalSectorStable :
      Bool
    vacuumSectorStable :
      Bool
    quotientDescentStable :
      Bool
    normWindowUpperBoundAvailable :
      Bool
    normWindowLowerBoundAvailable :
      Bool
    commonCarrierAdmissible :
      Bool
    leftResidualVanishesIsTrue :
      leftResidualVanishes ≡ true
    rightResidualVanishesIsTrue :
      rightResidualVanishes ≡ true
    projectionCommutatorsStableIsTrue :
      projectionCommutatorsStable ≡ true
    physicalSectorStableIsTrue :
      physicalSectorStable ≡ true
    vacuumSectorStableIsTrue :
      vacuumSectorStable ≡ true
    quotientDescentStableIsTrue :
      quotientDescentStable ≡ true
    normWindowUpperBoundAvailableIsTrue :
      normWindowUpperBoundAvailable ≡ true
    normWindowLowerBoundAvailableIsTrue :
      normWindowLowerBoundAvailable ≡ true
    commonCarrierAdmissibleIsTrue :
      commonCarrierAdmissible ≡ true

record ConsumedFlag : Set where
  constructor mkConsumedFlag
  field
    kind :
      SuppliedFlagKind
    lane :
      CriterionLane
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
      CriterionStatus

record ResidualClosureCriterion : Set where
  constructor mkResidualClosureCriterion
  field
    leftResidualAssembly :
      Residual113.ResidualAssembly
    rightResidualAssembly :
      Residual113.ResidualAssembly
    leftResidualVanishes :
      Bool
    leftResidualVanishesIsTrue :
      leftResidualVanishes ≡ true
    rightResidualVanishes :
      Bool
    rightResidualVanishesIsTrue :
      rightResidualVanishes ≡ true
    residualVanishingConsumed :
      Bool
    residualVanishingConsumedIsTrue :
      residualVanishingConsumed ≡ true
    theoremProvedHere :
      Bool
    theoremProvedHereIsFalse :
      theoremProvedHere ≡ false
    status :
      CriterionStatus

record ProjectionSectorClosureCriterion : Set where
  constructor mkProjectionSectorClosureCriterion
  field
    projectionAssembly :
      Residual113.ProjectionStabilityAssembly
    physicalSectorAssembly :
      Residual113.SectorStabilityAssembly
    vacuumSectorAssembly :
      Residual113.SectorStabilityAssembly
    projectionCommutatorsStable :
      Bool
    projectionCommutatorsStableIsTrue :
      projectionCommutatorsStable ≡ true
    physicalSectorStable :
      Bool
    physicalSectorStableIsTrue :
      physicalSectorStable ≡ true
    vacuumSectorStable :
      Bool
    vacuumSectorStableIsTrue :
      vacuumSectorStable ≡ true
    quotientDescentStable :
      Bool
    quotientDescentStableIsTrue :
      quotientDescentStable ≡ true
    theoremProvedHere :
      Bool
    theoremProvedHereIsFalse :
      theoremProvedHere ≡ false
    status :
      CriterionStatus

record NormWindowClosureCriterion : Set where
  constructor mkNormWindowClosureCriterion
  field
    normWindowUpperBoundAvailable :
      Bool
    normWindowUpperBoundAvailableIsTrue :
      normWindowUpperBoundAvailable ≡ true
    normWindowLowerBoundAvailable :
      Bool
    normWindowLowerBoundAvailableIsTrue :
      normWindowLowerBoundAvailable ≡ true
    normWindowFlagsConsumed :
      Bool
    normWindowFlagsConsumedIsTrue :
      normWindowFlagsConsumed ≡ true
    theoremProvedHere :
      Bool
    theoremProvedHereIsFalse :
      theoremProvedHere ≡ false
    status :
      CriterionStatus

record CommonCarrierFeedThroughCriterion : Setω where
  constructor mkCommonCarrierFeedThroughCriterion
  field
    sprint113FeedThrough :
      Residual113.CommonCarrierFeedThrough
    residualCriterion :
      ResidualClosureCriterion
    projectionSectorCriterion :
      ProjectionSectorClosureCriterion
    normWindowCriterion :
      NormWindowClosureCriterion
    commonCarrierAdmissible :
      Bool
    commonCarrierAdmissibleIsTrue :
      commonCarrierAdmissible ≡ true
    criterionInhabited :
      Bool
    criterionInhabitedIsTrue :
      criterionInhabited ≡ true
    commonCarrierClosedHere :
      Bool
    commonCarrierClosedHereIsFalse :
      commonCarrierClosedHere ≡ false
    status :
      CriterionStatus

record TheoremBoundary : Set where
  constructor mkTheoremBoundary
  field
    boundaryStatement :
      String
    leftInverseResidualVanishesProvedHereFlag :
      Bool
    leftInverseResidualVanishesProvedHereIsFalse :
      leftInverseResidualVanishesProvedHereFlag ≡ false
    rightInverseResidualVanishesProvedHereFlag :
      Bool
    rightInverseResidualVanishesProvedHereIsFalse :
      rightInverseResidualVanishesProvedHereFlag ≡ false
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
    normWindowClosedHereFlag :
      Bool
    normWindowClosedHereIsFalse :
      normWindowClosedHereFlag ≡ false
    commonCarrierConstructionClosedHereFlag :
      Bool
    commonCarrierConstructionClosedHereIsFalse :
      commonCarrierConstructionClosedHereFlag ≡ false
    inverseProjectionClosureTheoremProvedHereFlag :
      Bool
    inverseProjectionClosureTheoremProvedHereIsFalse :
      inverseProjectionClosureTheoremProvedHereFlag ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    status :
      CriterionStatus

record YMSprint114InverseProjectionClosureCriterionReceipt : Setω where
  constructor mkYMSprint114InverseProjectionClosureCriterionReceipt
  field
    sprint :
      Nat
    evidencePath :
      String
    sprint113Input :
      Sprint113Input
    suppliedFlags :
      SuppliedClosureFlags
    consumedFlags :
      List ConsumedFlag
    residualCriterion :
      ResidualClosureCriterion
    projectionSectorCriterion :
      ProjectionSectorClosureCriterion
    normWindowCriterion :
      NormWindowClosureCriterion
    commonCarrierFeedThroughCriterion :
      CommonCarrierFeedThroughCriterion
    theoremBoundary :
      TheoremBoundary
    lanes :
      List CriterionLane
    suppliedFlagKinds :
      List SuppliedFlagKind
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

open YMSprint114InverseProjectionClosureCriterionReceipt public

canonicalSprint113Input : Sprint113Input
canonicalSprint113Input =
  mkSprint113Input
    Residual113.canonicalReceipt
    sprint113InverseProjectionResidualAssemblyPath
    sprint114QuadratureResidualClosureCriterionPath
    sprint114QuadratureResidualClosureCriterionImported
    Residual113.inverseProjectionResidualAssemblyRecorded
    Residual113.canonicalLeftInverseResidual
    Residual113.canonicalRightInverseResidual
    Residual113.canonicalProjectionStability
    Residual113.canonicalPhysicalSectorStability
    Residual113.canonicalVacuumSectorStability
    Residual113.canonicalCommonCarrierFeed
    (Residual113.clayYangMillsPromotedHere Residual113.canonicalReceipt)
    Residual113.canonicalClayYangMillsPromotedIsFalse
    imported-sprint113-assembly

canonicalSuppliedClosureFlags : SuppliedClosureFlags
canonicalSuppliedClosureFlags =
  mkSuppliedClosureFlags
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

consumedFlagsFrom :
  SuppliedClosureFlags -> List ConsumedFlag
consumedFlagsFrom flags =
  mkConsumedFlag
    left-residual-vanishes-flag
    left-inverse-vanishing-lane
    leftResidualConsumptionText
    (SuppliedClosureFlags.leftResidualVanishes flags)
    (SuppliedClosureFlags.leftResidualVanishesIsTrue flags)
    residualVanishingAssumptionsConsumed
    refl
    supplied-assumption-consumed
  ∷ mkConsumedFlag
    right-residual-vanishes-flag
    right-inverse-vanishing-lane
    rightResidualConsumptionText
    (SuppliedClosureFlags.rightResidualVanishes flags)
    (SuppliedClosureFlags.rightResidualVanishesIsTrue flags)
    residualVanishingAssumptionsConsumed
    refl
    supplied-assumption-consumed
  ∷ mkConsumedFlag
    projection-commutator-stable-flag
    projection-commutator-stability-lane
    projectionCommutatorConsumptionText
    (SuppliedClosureFlags.projectionCommutatorsStable flags)
    (SuppliedClosureFlags.projectionCommutatorsStableIsTrue flags)
    projectionCommutatorStabilityConsumed
    refl
    supplied-assumption-consumed
  ∷ mkConsumedFlag
    physical-sector-stable-flag
    physical-sector-stability-lane
    sectorStabilityConsumptionText
    (SuppliedClosureFlags.physicalSectorStable flags)
    (SuppliedClosureFlags.physicalSectorStableIsTrue flags)
    physicalSectorStabilityConsumed
    refl
    supplied-assumption-consumed
  ∷ mkConsumedFlag
    vacuum-sector-stable-flag
    vacuum-sector-stability-lane
    sectorStabilityConsumptionText
    (SuppliedClosureFlags.vacuumSectorStable flags)
    (SuppliedClosureFlags.vacuumSectorStableIsTrue flags)
    vacuumSectorStabilityConsumed
    refl
    supplied-assumption-consumed
  ∷ mkConsumedFlag
    quotient-descent-stable-flag
    norm-window-lane
    normWindowConsumptionText
    (SuppliedClosureFlags.quotientDescentStable flags)
    (SuppliedClosureFlags.quotientDescentStableIsTrue flags)
    normWindowFlagsConsumedHere
    refl
    supplied-assumption-consumed
  ∷ mkConsumedFlag
    norm-window-upper-flag
    norm-window-lane
    normWindowConsumptionText
    (SuppliedClosureFlags.normWindowUpperBoundAvailable flags)
    (SuppliedClosureFlags.normWindowUpperBoundAvailableIsTrue flags)
    normWindowFlagsConsumedHere
    refl
    supplied-assumption-consumed
  ∷ mkConsumedFlag
    norm-window-lower-flag
    norm-window-lane
    normWindowConsumptionText
    (SuppliedClosureFlags.normWindowLowerBoundAvailable flags)
    (SuppliedClosureFlags.normWindowLowerBoundAvailableIsTrue flags)
    normWindowFlagsConsumedHere
    refl
    supplied-assumption-consumed
  ∷ mkConsumedFlag
    common-carrier-admissible-flag
    common-carrier-feed-through-lane
    commonCarrierFeedThroughText
    (SuppliedClosureFlags.commonCarrierAdmissible flags)
    (SuppliedClosureFlags.commonCarrierAdmissibleIsTrue flags)
    commonCarrierFeedThroughCriterionInhabited
    refl
    closure-criterion-inhabited
  ∷ []

residualCriterionFrom :
  Sprint113Input ->
  SuppliedClosureFlags ->
  ResidualClosureCriterion
residualCriterionFrom input flags =
  mkResidualClosureCriterion
    (Sprint113Input.leftResidualAssembly input)
    (Sprint113Input.rightResidualAssembly input)
    (SuppliedClosureFlags.leftResidualVanishes flags)
    (SuppliedClosureFlags.leftResidualVanishesIsTrue flags)
    (SuppliedClosureFlags.rightResidualVanishes flags)
    (SuppliedClosureFlags.rightResidualVanishesIsTrue flags)
    residualVanishingAssumptionsConsumed
    refl
    inverseProjectionClosureTheoremProvedHere
    refl
    closure-criterion-inhabited

projectionSectorCriterionFrom :
  Sprint113Input ->
  SuppliedClosureFlags ->
  ProjectionSectorClosureCriterion
projectionSectorCriterionFrom input flags =
  mkProjectionSectorClosureCriterion
    (Sprint113Input.projectionStabilityAssembly input)
    (Sprint113Input.physicalSectorStabilityAssembly input)
    (Sprint113Input.vacuumSectorStabilityAssembly input)
    (SuppliedClosureFlags.projectionCommutatorsStable flags)
    (SuppliedClosureFlags.projectionCommutatorsStableIsTrue flags)
    (SuppliedClosureFlags.physicalSectorStable flags)
    (SuppliedClosureFlags.physicalSectorStableIsTrue flags)
    (SuppliedClosureFlags.vacuumSectorStable flags)
    (SuppliedClosureFlags.vacuumSectorStableIsTrue flags)
    (SuppliedClosureFlags.quotientDescentStable flags)
    (SuppliedClosureFlags.quotientDescentStableIsTrue flags)
    projectionCommutatorStabilityProvedHere
    refl
    closure-criterion-inhabited

normWindowCriterionFrom :
  SuppliedClosureFlags ->
  NormWindowClosureCriterion
normWindowCriterionFrom flags =
  mkNormWindowClosureCriterion
    (SuppliedClosureFlags.normWindowUpperBoundAvailable flags)
    (SuppliedClosureFlags.normWindowUpperBoundAvailableIsTrue flags)
    (SuppliedClosureFlags.normWindowLowerBoundAvailable flags)
    (SuppliedClosureFlags.normWindowLowerBoundAvailableIsTrue flags)
    normWindowFlagsConsumedHere
    refl
    normWindowClosedHere
    refl
    closure-criterion-inhabited

commonCarrierFeedThroughCriterionFrom :
  Sprint113Input ->
  SuppliedClosureFlags ->
  CommonCarrierFeedThroughCriterion
commonCarrierFeedThroughCriterionFrom input flags =
  mkCommonCarrierFeedThroughCriterion
    (Sprint113Input.commonCarrierFeedThroughAssembly input)
    (residualCriterionFrom input flags)
    (projectionSectorCriterionFrom input flags)
    (normWindowCriterionFrom flags)
    (SuppliedClosureFlags.commonCarrierAdmissible flags)
    (SuppliedClosureFlags.commonCarrierAdmissibleIsTrue flags)
    commonCarrierFeedThroughCriterionInhabited
    refl
    commonCarrierConstructionClosedHere
    refl
    closure-criterion-inhabited

canonicalTheoremBoundary : TheoremBoundary
canonicalTheoremBoundary =
  mkTheoremBoundary
    nonPromotionBoundaryText
    leftInverseResidualVanishesProvedHere
    refl
    rightInverseResidualVanishesProvedHere
    refl
    projectionCommutatorStabilityProvedHere
    refl
    physicalSectorStabilityProvedHere
    refl
    vacuumSectorStabilityProvedHere
    refl
    normWindowClosedHere
    refl
    commonCarrierConstructionClosedHere
    refl
    inverseProjectionClosureTheoremProvedHere
    refl
    clayYangMillsPromoted
    refl
    fail-closed-nonpromotion

criterionReceiptFrom :
  Sprint113Input ->
  SuppliedClosureFlags ->
  YMSprint114InverseProjectionClosureCriterionReceipt
criterionReceiptFrom input flags =
  mkYMSprint114InverseProjectionClosureCriterionReceipt
    sprintNumber
    modulePath
    input
    flags
    (consumedFlagsFrom flags)
    (residualCriterionFrom input flags)
    (projectionSectorCriterionFrom input flags)
    (normWindowCriterionFrom flags)
    (commonCarrierFeedThroughCriterionFrom input flags)
    canonicalTheoremBoundary
    canonicalCriterionLanes
    canonicalSuppliedFlagKinds
    (criterionStatementText
     ∷ leftResidualConsumptionText
     ∷ rightResidualConsumptionText
     ∷ projectionCommutatorConsumptionText
     ∷ sectorStabilityConsumptionText
     ∷ normWindowConsumptionText
     ∷ commonCarrierFeedThroughText
     ∷ nonPromotionBoundaryText
     ∷ sprint113InverseProjectionResidualAssemblyPath
     ∷ sprint114QuadratureResidualClosureCriterionPath
     ∷ [])
    inverseProjectionClosureCriterionRecorded
    commonCarrierFeedThroughCriterionInhabited
    clayYangMillsPromoted
    refl

canonicalYMSprint114InverseProjectionClosureCriterionReceipt :
  YMSprint114InverseProjectionClosureCriterionReceipt
canonicalYMSprint114InverseProjectionClosureCriterionReceipt =
  criterionReceiptFrom
    canonicalSprint113Input
    canonicalSuppliedClosureFlags

canonicalReceipt :
  YMSprint114InverseProjectionClosureCriterionReceipt
canonicalReceipt =
  canonicalYMSprint114InverseProjectionClosureCriterionReceipt

canonicalCriterionInhabitedIsTrue :
  criterionInhabited canonicalReceipt ≡ true
canonicalCriterionInhabitedIsTrue =
  refl

canonicalCommonCarrierFeedThroughCriterionInhabitedIsTrue :
  CommonCarrierFeedThroughCriterion.criterionInhabited
    (commonCarrierFeedThroughCriterion canonicalReceipt) ≡ true
canonicalCommonCarrierFeedThroughCriterionInhabitedIsTrue =
  refl

canonicalLeftResidualVanishesSuppliedIsTrue :
  ResidualClosureCriterion.leftResidualVanishes
    (residualCriterion canonicalReceipt) ≡ true
canonicalLeftResidualVanishesSuppliedIsTrue =
  refl

canonicalRightResidualVanishesSuppliedIsTrue :
  ResidualClosureCriterion.rightResidualVanishes
    (residualCriterion canonicalReceipt) ≡ true
canonicalRightResidualVanishesSuppliedIsTrue =
  refl

canonicalProjectionCommutatorStabilitySuppliedIsTrue :
  ProjectionSectorClosureCriterion.projectionCommutatorsStable
    (projectionSectorCriterion canonicalReceipt) ≡ true
canonicalProjectionCommutatorStabilitySuppliedIsTrue =
  refl

canonicalPhysicalSectorStabilitySuppliedIsTrue :
  ProjectionSectorClosureCriterion.physicalSectorStable
    (projectionSectorCriterion canonicalReceipt) ≡ true
canonicalPhysicalSectorStabilitySuppliedIsTrue =
  refl

canonicalVacuumSectorStabilitySuppliedIsTrue :
  ProjectionSectorClosureCriterion.vacuumSectorStable
    (projectionSectorCriterion canonicalReceipt) ≡ true
canonicalVacuumSectorStabilitySuppliedIsTrue =
  refl

canonicalNormWindowUpperBoundSuppliedIsTrue :
  NormWindowClosureCriterion.normWindowUpperBoundAvailable
    (normWindowCriterion canonicalReceipt) ≡ true
canonicalNormWindowUpperBoundSuppliedIsTrue =
  refl

canonicalNormWindowLowerBoundSuppliedIsTrue :
  NormWindowClosureCriterion.normWindowLowerBoundAvailable
    (normWindowCriterion canonicalReceipt) ≡ true
canonicalNormWindowLowerBoundSuppliedIsTrue =
  refl

canonicalInverseProjectionClosureTheoremProvedHereIsFalse :
  TheoremBoundary.inverseProjectionClosureTheoremProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalInverseProjectionClosureTheoremProvedHereIsFalse =
  refl

canonicalCommonCarrierConstructionClosedHereIsFalse :
  TheoremBoundary.commonCarrierConstructionClosedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalCommonCarrierConstructionClosedHereIsFalse =
  refl

canonicalClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalClayYangMillsPromotedIsFalse =
  refl
