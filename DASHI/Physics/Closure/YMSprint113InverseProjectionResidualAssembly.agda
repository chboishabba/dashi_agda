module DASHI.Physics.Closure.YMSprint113InverseProjectionResidualAssembly where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint112AdjointnessApproxInverseReduction
  as Adj112
import DASHI.Physics.Closure.YMSprint112QuotientIndependenceDiagramLedger
  as Quot112
import DASHI.Physics.Closure.YMSprint112UniformNormBoundReduction
  as Norm112
import DASHI.Physics.Closure.YMSprint111EmbeddingProjectionAdjointnessLedger
  as Adj111
import DASHI.Physics.Closure.YMSprint111CommonCarrierConstructionAssembly
  as Carrier111

------------------------------------------------------------------------
-- Sprint113 inverse/projection residual assembly.
--
-- This module assembles the Sprint112 residual reductions into one
-- fail-closed carrier-facing receipt.  It records left and right inverse
-- residuals, projection stability, vacuum/physical sector stability,
-- feed-through conditions for the Sprint111 common-carrier construction, and
-- exact blockers.  It proves no residual vanishing theorem, no projection
-- stability theorem, no common-carrier construction theorem, and no Clay
-- Yang-Mills promotion.

sprintNumber : Nat
sprintNumber = 113

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint113InverseProjectionResidualAssembly.agda"

inverseProjectionResidualAssemblyRecorded : Bool
inverseProjectionResidualAssemblyRecorded = true

leftInverseResidualAssemblyRecorded : Bool
leftInverseResidualAssemblyRecorded = true

rightInverseResidualAssemblyRecorded : Bool
rightInverseResidualAssemblyRecorded = true

projectionStabilityAssemblyRecorded : Bool
projectionStabilityAssemblyRecorded = true

physicalSectorStabilityAssemblyRecorded : Bool
physicalSectorStabilityAssemblyRecorded = true

vacuumSectorStabilityAssemblyRecorded : Bool
vacuumSectorStabilityAssemblyRecorded = true

commonCarrierFeedThroughRecorded : Bool
commonCarrierFeedThroughRecorded = true

exactBlockerAssemblyRecorded : Bool
exactBlockerAssemblyRecorded = true

leftInverseResidualVanishesProvedHere : Bool
leftInverseResidualVanishesProvedHere = false

rightInverseResidualVanishesProvedHere : Bool
rightInverseResidualVanishesProvedHere = false

projectionStabilityProvedHere : Bool
projectionStabilityProvedHere = false

physicalSectorStabilityProvedHere : Bool
physicalSectorStabilityProvedHere = false

vacuumSectorStabilityProvedHere : Bool
vacuumSectorStabilityProvedHere = false

commonCarrierConstructionFedHere : Bool
commonCarrierConstructionFedHere = false

residualAssemblyTheoremProvedHere : Bool
residualAssemblyTheoremProvedHere = false

commonCarrierConstructionClosedHere : Bool
commonCarrierConstructionClosedHere = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

leftInverseAssemblyText : String
leftInverseAssemblyText =
  "Left inverse residual assembly: carry the Sprint112 continuum-side E_a o P_a residual into one named bound ||E_a(P_a v) - v||_H_phys <= eps_left(a,v) on the continuum physical finite-energy comparison sector."

rightInverseAssemblyText : String
rightInverseAssemblyText =
  "Right inverse residual assembly: carry the Sprint112 finite-side P_a o E_a residual into one named bound ||P_a(E_a u) - u||_a,quot <= eps_right(a,u) on finite physical gauge-quotient vectors."

projectionStabilityAssemblyText : String
projectionStabilityAssemblyText =
  "Projection stability assembly: combine the Sprint112 projection-commutator residuals for Pi_phys E_a versus E_a Pi_a,phys and Pi_a,phys P_a versus P_a Pi_phys under the same quotient and norm window."

physicalSectorStabilityText : String
physicalSectorStabilityText =
  "Physical sector stability: residual control is accepted only after representative independence, quotient descent, physical projection commutation, and leakage exclusion are all available for the same E_a/P_a convention."

vacuumSectorStabilityText : String
vacuumSectorStabilityText =
  "Vacuum/non-vacuum sector stability: the residual assembly must preserve the Sprint111 isolated vacuum projection and non-vacuum complement strongly enough to feed bottom-sector no-collapse without changing carrier labels."

commonCarrierFeedThroughText : String
commonCarrierFeedThroughText =
  "Common-carrier feed-through: when left/right inverse residuals vanish, projection stability is closed, quotient independence is proved, and the uniform norm window is proved, the Sprint111 common-carrier construction can consume the assembled evidence."

failClosedBoundaryText : String
failClosedBoundaryText =
  "Sprint113 records residual assembly only.  It does not prove residual vanishing, sector stability, quotient independence, uniform norm estimates, common-carrier construction, transfer lower bounds, continuum gap, or Clay Yang-Mills."

leftInverseBlockerText : String
leftInverseBlockerText =
  "Exact blocker: Sprint112 records the E_a o P_a continuum residual criterion but no proof that eps_left(a,v) vanishes on the admissible comparison domain."

rightInverseBlockerText : String
rightInverseBlockerText =
  "Exact blocker: Sprint112 records the P_a o E_a finite quotient residual criterion but no proof that eps_right(a,u) vanishes uniformly in the admissible a-window."

projectionStabilityBlockerText : String
projectionStabilityBlockerText =
  "Exact blocker: Sprint112 records physical-projection commutator residuals but no theorem making those residuals vanish or remain uniformly controlled through quotient descent."

sectorStabilityBlockerText : String
sectorStabilityBlockerText =
  "Exact blocker: Sprint111/112 record physical and vacuum-sector criteria, but no proof excludes leakage between gauge, vacuum, and non-vacuum sectors under E_a and P_a."

normWindowBlockerText : String
normWindowBlockerText =
  "Exact blocker: Sprint112 reduces the required uniform norm window to local Jacobian, partition, and quotient-norm estimates, but those analytic estimates remain unproved."

commonCarrierFeedBlockerText : String
commonCarrierFeedBlockerText =
  "Exact blocker: the Sprint111 common-carrier construction cannot be consumed until residual vanishing, quotient independence, projection stability, and uniform norm bounds are closed together."

nonPromotionBlockerText : String
nonPromotionBlockerText =
  "Exact blocker: Clay Yang-Mills promotion remains false because this Sprint113 module is an assembly receipt and proves no continuum mass-gap theorem."

data AssemblyLane : Set where
  left-inverse-residual-lane :
    AssemblyLane
  right-inverse-residual-lane :
    AssemblyLane
  projection-stability-lane :
    AssemblyLane
  physical-sector-stability-lane :
    AssemblyLane
  vacuum-sector-stability-lane :
    AssemblyLane
  common-carrier-feed-through-lane :
    AssemblyLane
  exact-blocker-lane :
    AssemblyLane
  theorem-boundary-lane :
    AssemblyLane

data AssemblyStatus : Set where
  imported-sprint112-adjointness :
    AssemblyStatus
  imported-sprint112-quotient :
    AssemblyStatus
  imported-sprint112-norm :
    AssemblyStatus
  imported-sprint111-adjointness :
    AssemblyStatus
  assembly-recorded :
    AssemblyStatus
  residual-vanishing-required :
    AssemblyStatus
  projection-stability-required :
    AssemblyStatus
  sector-stability-required :
    AssemblyStatus
  feed-through-blocked :
    AssemblyStatus
  exact-blocker-recorded :
    AssemblyStatus
  fail-closed-nonpromotion :
    AssemblyStatus

data ResidualOrientation : Set where
  continuum-left-orientation :
    ResidualOrientation
  finite-right-orientation :
    ResidualOrientation
  projection-commutator-orientation :
    ResidualOrientation
  sector-preservation-orientation :
    ResidualOrientation

data SectorKind : Set where
  physical-sector :
    SectorKind
  vacuum-sector :
    SectorKind
  non-vacuum-sector :
    SectorKind

data BlockerKind : Set where
  left-inverse-blocker :
    BlockerKind
  right-inverse-blocker :
    BlockerKind
  projection-stability-blocker :
    BlockerKind
  sector-stability-blocker :
    BlockerKind
  norm-window-blocker :
    BlockerKind
  common-carrier-feed-blocker :
    BlockerKind
  nonpromotion-blocker :
    BlockerKind

canonicalAssemblyLanes : List AssemblyLane
canonicalAssemblyLanes =
  left-inverse-residual-lane
  ∷ right-inverse-residual-lane
  ∷ projection-stability-lane
  ∷ physical-sector-stability-lane
  ∷ vacuum-sector-stability-lane
  ∷ common-carrier-feed-through-lane
  ∷ exact-blocker-lane
  ∷ theorem-boundary-lane
  ∷ []

record ImportedResidualInputs : Setω where
  constructor mkImportedResidualInputs
  field
    adjointnessReductionReceipt :
      Adj112.YMSprint112AdjointnessApproxInverseReductionReceipt
    quotientDiagramReceipt :
      Quot112.YMSprint112QuotientIndependenceDiagramLedgerReceipt
    normBoundReductionReceipt :
      Norm112.YMSprint112UniformNormBoundReductionReceipt
    sprint111AdjointnessReceipt :
      Adj111.YMSprint111EmbeddingProjectionAdjointnessReceipt
    sprint111CommonCarrierReceipt :
      Carrier111.AssemblyReceipt
    adjointnessReductionRecorded :
      Bool
    quotientDiagramRecorded :
      Bool
    normBoundReductionRecorded :
      Bool
    sprint111AdjointnessRecorded :
      Bool
    sprint111CommonCarrierRecorded :
      Bool
    importedLeftInverseClosed :
      Bool
    importedRightInverseClosed :
      Bool
    importedProjectionStabilityClosed :
      Bool
    importedQuotientIndependenceClosed :
      Bool
    importedNormEquivalenceClosed :
      Bool
    importedCommonCarrierClosed :
      Bool
    importedLeftInverseClosedIsFalse :
      importedLeftInverseClosed ≡ false
    importedRightInverseClosedIsFalse :
      importedRightInverseClosed ≡ false
    importedProjectionStabilityClosedIsFalse :
      importedProjectionStabilityClosed ≡ false
    importedQuotientIndependenceClosedIsFalse :
      importedQuotientIndependenceClosed ≡ false
    importedNormEquivalenceClosedIsFalse :
      importedNormEquivalenceClosed ≡ false
    importedCommonCarrierClosedIsFalse :
      importedCommonCarrierClosed ≡ false

record ResidualAssembly : Set where
  constructor mkResidualAssembly
  field
    lane :
      AssemblyLane
    orientation :
      ResidualOrientation
    statement :
      String
    sourceResidualStatement :
      String
    compositeSymbol :
      String
    identitySymbol :
      String
    normSymbol :
      String
    residualSymbol :
      String
    admissibleWindow :
      String
    sourceRecorded :
      Bool
    assembledHere :
      Bool
    vanishingProvedHere :
      Bool
    vanishingProvedHereIsFalse :
      vanishingProvedHere ≡ false
    status :
      AssemblyStatus

record ProjectionStabilityAssembly : Set where
  constructor mkProjectionStabilityAssembly
  field
    lane :
      AssemblyLane
    orientation :
      ResidualOrientation
    statement :
      String
    finiteProjectionSymbol :
      String
    continuumProjectionSymbol :
      String
    embeddingCommutatorResidual :
      String
    projectionCommutatorResidual :
      String
    quotientDiagramRecorded :
      Bool
    adjointnessResidualRecorded :
      Bool
    assembledHere :
      Bool
    stabilityProvedHere :
      Bool
    stabilityProvedHereIsFalse :
      stabilityProvedHere ≡ false
    status :
      AssemblyStatus

record SectorStabilityAssembly : Set where
  constructor mkSectorStabilityAssembly
  field
    lane :
      AssemblyLane
    sector :
      SectorKind
    statement :
      String
    projectionSymbol :
      String
    quotientIndependenceRequired :
      Bool
    projectionStabilityRequired :
      Bool
    residualVanishingRequired :
      Bool
    leakageExclusionRequired :
      Bool
    sprint111CriterionRecorded :
      Bool
    sprint112DiagramRecorded :
      Bool
    assembledHere :
      Bool
    stabilityProvedHere :
      Bool
    stabilityProvedHereIsFalse :
      stabilityProvedHere ≡ false
    status :
      AssemblyStatus

record CommonCarrierFeedThrough : Setω where
  constructor mkCommonCarrierFeedThrough
  field
    lane :
      AssemblyLane
    statement :
      String
    commonCarrierReceipt :
      Carrier111.AssemblyReceipt
    leftResidual :
      ResidualAssembly
    rightResidual :
      ResidualAssembly
    projectionStability :
      ProjectionStabilityAssembly
    physicalSectorStability :
      SectorStabilityAssembly
    vacuumSectorStability :
      SectorStabilityAssembly
    needsLeftResidualVanishing :
      Bool
    needsRightResidualVanishing :
      Bool
    needsProjectionStability :
      Bool
    needsQuotientIndependence :
      Bool
    needsUniformNormWindow :
      Bool
    feedThroughRecorded :
      Bool
    fedHere :
      Bool
    fedHereIsFalse :
      fedHere ≡ false
    status :
      AssemblyStatus

record BlockerReceipt : Set where
  constructor mkBlockerReceipt
  field
    blocker :
      BlockerKind
    lane :
      AssemblyLane
    statement :
      String
    blocksAssemblyClosure :
      Bool
    closedHere :
      Bool
    closedHereIsFalse :
      closedHere ≡ false
    status :
      AssemblyStatus

record ExactBlockerLedger : Set where
  constructor mkExactBlockerLedger
  field
    lane :
      AssemblyLane
    leftInverseBlocker :
      String
    rightInverseBlocker :
      String
    projectionStabilityBlocker :
      String
    sectorStabilityBlocker :
      String
    normWindowBlocker :
      String
    commonCarrierFeedBlocker :
      String
    nonPromotionBlocker :
      String
    blockerReceipts :
      List BlockerReceipt
    blockerTexts :
      List String
    allBlockersExact :
      Bool
    theoremStillOpen :
      Bool
    status :
      AssemblyStatus

record TheoremBoundary : Set where
  constructor mkTheoremBoundary
  field
    lane :
      AssemblyLane
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
    projectionStabilityProvedHereFlag :
      Bool
    projectionStabilityProvedHereIsFalse :
      projectionStabilityProvedHereFlag ≡ false
    physicalSectorStabilityProvedHereFlag :
      Bool
    physicalSectorStabilityProvedHereIsFalse :
      physicalSectorStabilityProvedHereFlag ≡ false
    vacuumSectorStabilityProvedHereFlag :
      Bool
    vacuumSectorStabilityProvedHereIsFalse :
      vacuumSectorStabilityProvedHereFlag ≡ false
    commonCarrierConstructionFedHereFlag :
      Bool
    commonCarrierConstructionFedHereIsFalse :
      commonCarrierConstructionFedHereFlag ≡ false
    residualAssemblyTheoremProvedHereFlag :
      Bool
    residualAssemblyTheoremProvedHereIsFalse :
      residualAssemblyTheoremProvedHereFlag ≡ false
    commonCarrierConstructionClosedHereFlag :
      Bool
    commonCarrierConstructionClosedHereIsFalse :
      commonCarrierConstructionClosedHereFlag ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    status :
      AssemblyStatus

record YMSprint113InverseProjectionResidualAssemblyReceipt : Setω where
  constructor mkYMSprint113InverseProjectionResidualAssemblyReceipt
  field
    sprint :
      Nat
    evidencePath :
      String
    importedInputs :
      ImportedResidualInputs
    leftInverseResidual :
      ResidualAssembly
    rightInverseResidual :
      ResidualAssembly
    projectionStability :
      ProjectionStabilityAssembly
    physicalSectorStability :
      SectorStabilityAssembly
    vacuumSectorStability :
      SectorStabilityAssembly
    commonCarrierFeedThrough :
      CommonCarrierFeedThrough
    exactBlockers :
      ExactBlockerLedger
    theoremBoundary :
      TheoremBoundary
    lanes :
      List AssemblyLane
    evidenceLedger :
      List String
    receiptRecorded :
      Bool
    assemblyRecordedHere :
      Bool
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false

open YMSprint113InverseProjectionResidualAssemblyReceipt public

canonicalImportedResidualInputs : ImportedResidualInputs
canonicalImportedResidualInputs =
  mkImportedResidualInputs
    Adj112.canonicalReceipt
    Quot112.canonicalReceipt
    Norm112.canonicalReceipt
    Adj111.canonicalReceipt
    Carrier111.canonicalAssemblyReceipt
    Adj112.adjointnessReductionRecorded
    Quot112.quotientDiagramLedgerRecorded
    Norm112.uniformNormBoundReductionRecorded
    Adj111.embeddingProjectionAdjointnessLedgerRecorded
    Carrier111.sprint111AssemblyRecorded
    Adj112.leftInverseResidualVanishesProvedHere
    Adj112.rightInverseResidualVanishesProvedHere
    Adj112.projectionStabilityProvedHere
    Quot112.quotientIndependenceClosedHere
    Norm112.normEquivalenceTheoremProvedHere
    Carrier111.commonCarrierConstructionClosedHere
    refl
    refl
    refl
    refl
    refl
    refl

canonicalLeftInverseResidualAssembly : ResidualAssembly
canonicalLeftInverseResidualAssembly =
  mkResidualAssembly
    left-inverse-residual-lane
    continuum-left-orientation
    leftInverseAssemblyText
    Adj112.leftInverseResidualText
    "E_a o P_a"
    "Id_H_phys"
    "||-||_H_phys"
    "eps_left(a,v)"
    "0 < a <= a0"
    Adj112.leftInverseResidualCriterionRecorded
    leftInverseResidualAssemblyRecorded
    leftInverseResidualVanishesProvedHere
    refl
    residual-vanishing-required

canonicalRightInverseResidualAssembly : ResidualAssembly
canonicalRightInverseResidualAssembly =
  mkResidualAssembly
    right-inverse-residual-lane
    finite-right-orientation
    rightInverseAssemblyText
    Adj112.rightInverseResidualText
    "P_a o E_a"
    "Id_a,phys"
    "||-||_a,quot"
    "eps_right(a,u)"
    "0 < a <= a0"
    Adj112.rightInverseResidualCriterionRecorded
    rightInverseResidualAssemblyRecorded
    rightInverseResidualVanishesProvedHere
    refl
    residual-vanishing-required

canonicalProjectionStabilityAssembly : ProjectionStabilityAssembly
canonicalProjectionStabilityAssembly =
  mkProjectionStabilityAssembly
    projection-stability-lane
    projection-commutator-orientation
    projectionStabilityAssemblyText
    "Pi_a,phys"
    "Pi_phys"
    "||Pi_phys E_a u - E_a Pi_a,phys u||_H_phys"
    "||Pi_a,phys P_a v - P_a Pi_phys v||_a,quot"
    Quot112.physicalProjectionCommutationDiagramRecorded
    Adj112.projectionStabilityResidualCriterionRecorded
    projectionStabilityAssemblyRecorded
    projectionStabilityProvedHere
    refl
    projection-stability-required

canonicalPhysicalSectorStabilityAssembly : SectorStabilityAssembly
canonicalPhysicalSectorStabilityAssembly =
  mkSectorStabilityAssembly
    physical-sector-stability-lane
    physical-sector
    physicalSectorStabilityText
    "Pi_phys and Pi_a,phys"
    true
    true
    true
    true
    Adj111.projectionStabilityCriterionRecorded
    Quot112.physicalProjectionCommutationDiagramRecorded
    physicalSectorStabilityAssemblyRecorded
    physicalSectorStabilityProvedHere
    refl
    sector-stability-required

canonicalVacuumSectorStabilityAssembly : SectorStabilityAssembly
canonicalVacuumSectorStabilityAssembly =
  mkSectorStabilityAssembly
    vacuum-sector-stability-lane
    vacuum-sector
    vacuumSectorStabilityText
    "Pi_vac,a and Pi_0"
    true
    true
    true
    true
    Adj111.vacuumProjectionStabilityCriterionRecorded
    Quot112.leakageControlCriterionRecorded
    vacuumSectorStabilityAssemblyRecorded
    vacuumSectorStabilityProvedHere
    refl
    sector-stability-required

canonicalCommonCarrierFeedThrough : CommonCarrierFeedThrough
canonicalCommonCarrierFeedThrough =
  mkCommonCarrierFeedThrough
    common-carrier-feed-through-lane
    commonCarrierFeedThroughText
    Carrier111.canonicalAssemblyReceipt
    canonicalLeftInverseResidualAssembly
    canonicalRightInverseResidualAssembly
    canonicalProjectionStabilityAssembly
    canonicalPhysicalSectorStabilityAssembly
    canonicalVacuumSectorStabilityAssembly
    true
    true
    true
    true
    true
    commonCarrierFeedThroughRecorded
    commonCarrierConstructionFedHere
    refl
    feed-through-blocked

canonicalBlockerReceipts : List BlockerReceipt
canonicalBlockerReceipts =
  mkBlockerReceipt
    left-inverse-blocker
    left-inverse-residual-lane
    leftInverseBlockerText
    true
    leftInverseResidualVanishesProvedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerReceipt
    right-inverse-blocker
    right-inverse-residual-lane
    rightInverseBlockerText
    true
    rightInverseResidualVanishesProvedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerReceipt
    projection-stability-blocker
    projection-stability-lane
    projectionStabilityBlockerText
    true
    projectionStabilityProvedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerReceipt
    sector-stability-blocker
    physical-sector-stability-lane
    sectorStabilityBlockerText
    true
    physicalSectorStabilityProvedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerReceipt
    norm-window-blocker
    common-carrier-feed-through-lane
    normWindowBlockerText
    true
    Norm112.normEquivalenceTheoremProvedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerReceipt
    common-carrier-feed-blocker
    common-carrier-feed-through-lane
    commonCarrierFeedBlockerText
    true
    commonCarrierConstructionFedHere
    refl
    feed-through-blocked
  ∷ mkBlockerReceipt
    nonpromotion-blocker
    theorem-boundary-lane
    nonPromotionBlockerText
    true
    clayYangMillsPromoted
    refl
    fail-closed-nonpromotion
  ∷ []

canonicalExactBlockerLedger : ExactBlockerLedger
canonicalExactBlockerLedger =
  mkExactBlockerLedger
    exact-blocker-lane
    leftInverseBlockerText
    rightInverseBlockerText
    projectionStabilityBlockerText
    sectorStabilityBlockerText
    normWindowBlockerText
    commonCarrierFeedBlockerText
    nonPromotionBlockerText
    canonicalBlockerReceipts
    (leftInverseBlockerText
     ∷ rightInverseBlockerText
     ∷ projectionStabilityBlockerText
     ∷ sectorStabilityBlockerText
     ∷ normWindowBlockerText
     ∷ commonCarrierFeedBlockerText
     ∷ nonPromotionBlockerText
     ∷ [])
    true
    true
    exact-blocker-recorded

canonicalTheoremBoundary : TheoremBoundary
canonicalTheoremBoundary =
  mkTheoremBoundary
    theorem-boundary-lane
    failClosedBoundaryText
    leftInverseResidualVanishesProvedHere
    refl
    rightInverseResidualVanishesProvedHere
    refl
    projectionStabilityProvedHere
    refl
    physicalSectorStabilityProvedHere
    refl
    vacuumSectorStabilityProvedHere
    refl
    commonCarrierConstructionFedHere
    refl
    residualAssemblyTheoremProvedHere
    refl
    commonCarrierConstructionClosedHere
    refl
    clayYangMillsPromoted
    refl
    fail-closed-nonpromotion

canonicalYMSprint113InverseProjectionResidualAssemblyReceipt :
  YMSprint113InverseProjectionResidualAssemblyReceipt
canonicalYMSprint113InverseProjectionResidualAssemblyReceipt =
  mkYMSprint113InverseProjectionResidualAssemblyReceipt
    sprintNumber
    modulePath
    canonicalImportedResidualInputs
    canonicalLeftInverseResidualAssembly
    canonicalRightInverseResidualAssembly
    canonicalProjectionStabilityAssembly
    canonicalPhysicalSectorStabilityAssembly
    canonicalVacuumSectorStabilityAssembly
    canonicalCommonCarrierFeedThrough
    canonicalExactBlockerLedger
    canonicalTheoremBoundary
    canonicalAssemblyLanes
    (leftInverseAssemblyText
     ∷ rightInverseAssemblyText
     ∷ projectionStabilityAssemblyText
     ∷ physicalSectorStabilityText
     ∷ vacuumSectorStabilityText
     ∷ commonCarrierFeedThroughText
     ∷ failClosedBoundaryText
     ∷ leftInverseBlockerText
     ∷ rightInverseBlockerText
     ∷ projectionStabilityBlockerText
     ∷ sectorStabilityBlockerText
     ∷ normWindowBlockerText
     ∷ commonCarrierFeedBlockerText
     ∷ nonPromotionBlockerText
     ∷ [])
    inverseProjectionResidualAssemblyRecorded
    inverseProjectionResidualAssemblyRecorded
    clayYangMillsPromoted
    refl

canonicalReceipt :
  YMSprint113InverseProjectionResidualAssemblyReceipt
canonicalReceipt =
  canonicalYMSprint113InverseProjectionResidualAssemblyReceipt

canonicalLeftInverseResidualVanishesProvedHereIsFalse :
  TheoremBoundary.leftInverseResidualVanishesProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalLeftInverseResidualVanishesProvedHereIsFalse =
  refl

canonicalRightInverseResidualVanishesProvedHereIsFalse :
  TheoremBoundary.rightInverseResidualVanishesProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalRightInverseResidualVanishesProvedHereIsFalse =
  refl

canonicalProjectionStabilityProvedHereIsFalse :
  TheoremBoundary.projectionStabilityProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalProjectionStabilityProvedHereIsFalse =
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

canonicalCommonCarrierConstructionFedHereIsFalse :
  TheoremBoundary.commonCarrierConstructionFedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalCommonCarrierConstructionFedHereIsFalse =
  refl

canonicalResidualAssemblyTheoremProvedHereIsFalse :
  TheoremBoundary.residualAssemblyTheoremProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalResidualAssemblyTheoremProvedHereIsFalse =
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

canonicalLeftInverseResidual :
  ResidualAssembly
canonicalLeftInverseResidual =
  leftInverseResidual canonicalReceipt

canonicalRightInverseResidual :
  ResidualAssembly
canonicalRightInverseResidual =
  rightInverseResidual canonicalReceipt

canonicalProjectionStability :
  ProjectionStabilityAssembly
canonicalProjectionStability =
  projectionStability canonicalReceipt

canonicalPhysicalSectorStability :
  SectorStabilityAssembly
canonicalPhysicalSectorStability =
  physicalSectorStability canonicalReceipt

canonicalVacuumSectorStability :
  SectorStabilityAssembly
canonicalVacuumSectorStability =
  vacuumSectorStability canonicalReceipt

canonicalCommonCarrierFeed :
  CommonCarrierFeedThrough
canonicalCommonCarrierFeed =
  commonCarrierFeedThrough canonicalReceipt

canonicalBlockers :
  ExactBlockerLedger
canonicalBlockers =
  exactBlockers canonicalReceipt
