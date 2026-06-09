module DASHI.Physics.Closure.YMSprint115CommonCarrierFeedThroughCriterion where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint110WeakCompactnessEnergyCore
  as Weak110
import DASHI.Physics.Closure.YMSprint110ClosedFormLowerSemicontinuityCriterion
  as Closed110
import DASHI.Physics.Closure.YMSprint110RecoveryCoreDensityEnergyLimsup
  as Recovery110
import DASHI.Physics.Closure.YMSprint111CommonCarrierConstructionAssembly
  as Carrier111
import DASHI.Physics.Closure.YMSprint112UniformNormBoundReduction
  as Uniform112
import DASHI.Physics.Closure.YMSprint114CommonCarrierEstimateClosureAssembly
  as Estimate114

------------------------------------------------------------------------
-- Sprint115 common-carrier feed-through criterion.
--
-- Sprint114 assembled the common-carrier estimate closure boundary.  This
-- module advances that boundary into an explicit feed-through criterion for
-- Sprint110 weak compactness, closed-form lower semicontinuity, and recovery
-- limsup.  It records the norm, residual, and sector inputs that must be
-- closed before the Sprint111 common-carrier construction or the transfer
-- lower-bound theorem can be reopened.
--
-- This receipt is fail-closed.  It does not import concurrent Sprint115
-- sibling modules; those are named only by source-path strings.  It proves no
-- external common-carrier construction theorem, no transfer lower-bound
-- theorem, no continuum mass-gap theorem, and no Clay Yang-Mills promotion.

sprintNumber : Nat
sprintNumber = 115

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint115CommonCarrierFeedThroughCriterion.agda"

sprint114EstimateClosureSourcePath : String
sprint114EstimateClosureSourcePath =
  "DASHI/Physics/Closure/YMSprint114CommonCarrierEstimateClosureAssembly.agda"

sprint110WeakCompactnessSourcePath : String
sprint110WeakCompactnessSourcePath =
  "DASHI/Physics/Closure/YMSprint110WeakCompactnessEnergyCore.agda"

sprint110ClosedFormSourcePath : String
sprint110ClosedFormSourcePath =
  "DASHI/Physics/Closure/YMSprint110ClosedFormLowerSemicontinuityCriterion.agda"

sprint110RecoverySourcePath : String
sprint110RecoverySourcePath =
  "DASHI/Physics/Closure/YMSprint110RecoveryCoreDensityEnergyLimsup.agda"

sprint111CommonCarrierSourcePath : String
sprint111CommonCarrierSourcePath =
  "DASHI/Physics/Closure/YMSprint111CommonCarrierConstructionAssembly.agda"

sprint112UniformNormSourcePath : String
sprint112UniformNormSourcePath =
  "DASHI/Physics/Closure/YMSprint112UniformNormBoundReduction.agda"

sprint115WeakFeedSiblingPath : String
sprint115WeakFeedSiblingPath =
  "DASHI/Physics/Closure/YMSprint115WeakCompactnessFeedThrough.agda"

sprint115RecoveryFeedSiblingPath : String
sprint115RecoveryFeedSiblingPath =
  "DASHI/Physics/Closure/YMSprint115RecoveryLimsupFeedThrough.agda"

sprint115ClosedFormFeedSiblingPath : String
sprint115ClosedFormFeedSiblingPath =
  "DASHI/Physics/Closure/YMSprint115ClosedFormLSCFeedThrough.agda"

sprint115TransferClosureSiblingPath : String
sprint115TransferClosureSiblingPath =
  "DASHI/Physics/Closure/YMSprint115CommonCarrierTransferLowerBoundClosure.agda"

feedThroughCriterionRecorded : Bool
feedThroughCriterionRecorded = true

weakCompactnessFeedThroughRecorded : Bool
weakCompactnessFeedThroughRecorded = true

recoveryLimsupFeedThroughRecorded : Bool
recoveryLimsupFeedThroughRecorded = true

closedFormLowerSemicontinuityFeedThroughRecorded : Bool
closedFormLowerSemicontinuityFeedThroughRecorded = true

normResidualSectorInputsRecorded : Bool
normResidualSectorInputsRecorded = true

failClosedCommonCarrierTransferRouteRecorded : Bool
failClosedCommonCarrierTransferRouteRecorded = true

weakCompactnessFedHere : Bool
weakCompactnessFedHere = false

recoveryLimsupFedHere : Bool
recoveryLimsupFedHere = false

closedFormLowerSemicontinuityFedHere : Bool
closedFormLowerSemicontinuityFedHere = false

normCriterionClosedHere : Bool
normCriterionClosedHere = false

residualCriterionClosedHere : Bool
residualCriterionClosedHere = false

sectorCriterionClosedHere : Bool
sectorCriterionClosedHere = false

commonCarrierConstructionClosedExternallyHere : Bool
commonCarrierConstructionClosedExternallyHere = false

commonCarrierFeedThroughClosedHere : Bool
commonCarrierFeedThroughClosedHere = false

commonCarrierTransferLowerBoundReadyHere : Bool
commonCarrierTransferLowerBoundReadyHere = false

transferLowerBoundTheoremProvedHere : Bool
transferLowerBoundTheoremProvedHere = false

continuumMassGapProvedHere : Bool
continuumMassGapProvedHere = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

importedSprint114EstimateReceiptRecorded : Bool
importedSprint114EstimateReceiptRecorded =
  Estimate114.assemblyRecorded

importedSprint114CommonCarrierEstimateClosed : Bool
importedSprint114CommonCarrierEstimateClosed =
  Estimate114.commonCarrierEstimateClosureClosedHere

importedSprint114WeakCompactnessFed : Bool
importedSprint114WeakCompactnessFed =
  Estimate114.weakCompactnessFedHere

importedSprint114RecoveryLimsupFed : Bool
importedSprint114RecoveryLimsupFed =
  Estimate114.recoveryLimsupFedHere

importedSprint114TransferLowerBoundTransferred : Bool
importedSprint114TransferLowerBoundTransferred =
  Estimate114.transferLowerBoundTransferredHere

importedSprint110WeakCoreRecorded : Bool
importedSprint110WeakCoreRecorded =
  Weak110.weakCompactnessEnergyCoreRecorded

importedSprint110WeakExtractionClosed : Bool
importedSprint110WeakExtractionClosed =
  Weak110.weakSubsequenceExtractionProvedHere

importedSprint110ClosedFormCriterionRecorded : Bool
importedSprint110ClosedFormCriterionRecorded =
  Closed110.criterionReceiptRecorded

importedSprint110ClosedFormCriterionClosed : Bool
importedSprint110ClosedFormCriterionClosed =
  Closed110.closedFormCriterionClosedHere

importedSprint110RecoveryCoreRecorded : Bool
importedSprint110RecoveryCoreRecorded =
  Recovery110.receiptRecorded

importedSprint110RecoveryLimsupClosed : Bool
importedSprint110RecoveryLimsupClosed =
  Recovery110.energyLimsupCriterionProvedHere

importedSprint111AssemblyRecorded : Bool
importedSprint111AssemblyRecorded =
  Carrier111.sprint111AssemblyRecorded

importedSprint111CommonCarrierClosed : Bool
importedSprint111CommonCarrierClosed =
  Carrier111.commonCarrierConstructionClosedHere

importedSprint111TransferLowerBoundProved : Bool
importedSprint111TransferLowerBoundProved =
  Carrier111.transferLowerBoundTheoremProvedHere

importedSprint112ReductionRecorded : Bool
importedSprint112ReductionRecorded =
  Uniform112.uniformNormBoundReductionRecorded

importedSprint112NormEquivalenceClosed : Bool
importedSprint112NormEquivalenceClosed =
  Uniform112.normEquivalenceTheoremProvedHere

importedSprint112WeakCompactnessFed : Bool
importedSprint112WeakCompactnessFed =
  Uniform112.weakCompactnessFedHere

weakCompactnessFeedThroughText : String
weakCompactnessFeedThroughText =
  "Weak compactness feed-through criterion: the Sprint114 common carrier may feed Sprint110 weak compactness only after the same H_phys carrier, finite transfer-form sequence, cutoff window, uniform norm comparison, energy bound, and tightness controls are fixed without relabelling sectors."

recoveryLimsupFeedThroughText : String
recoveryLimsupFeedThroughText =
  "Recovery limsup feed-through criterion: the Sprint114 carrier may feed Sprint110 recovery only after the dense finite physical core, interpolation map I_a, sampling map S_a, renormalized finite form q_a, continuum form q, and strong norm recovery convention are all the same as the estimate closure convention."

closedFormLowerSemicontinuityFeedThroughText : String
closedFormLowerSemicontinuityFeedThroughText =
  "Closed-form lower semicontinuity feed-through criterion: weak bounded-energy finite-transfer sequences must compare in one closed semibounded continuum form domain D(q), preserve the physical gauge sector, and satisfy the liminf inequality on the identified common carrier."

normResidualSectorInputsText : String
normResidualSectorInputsText =
  "Norm/residual/sector criterion inputs: feed-through requires Sprint112 upper/lower norm bounds, Sprint114 quadrature residual closure, Sprint114 inverse/projection residual closure, gauge quotient representative independence, physical projection compatibility, and vacuum/non-vacuum sector stability."

failClosedCommonCarrierTransferRouteText : String
failClosedCommonCarrierTransferRouteText =
  "Fail-closed route: common-carrier/transfer lower-bound closure can be reopened only after weak compactness feed-through, closed-form lower semicontinuity feed-through, recovery limsup feed-through, norm closure, residual closure, sector closure, and external common-carrier construction are all proved."

nonPromotionBoundaryText : String
nonPromotionBoundaryText =
  "Sprint115 records feed-through criteria only; common-carrier construction, transfer lower-bound transport, continuum mass gap, and Clay Yang-Mills promotion remain false."

weakCompactnessBlockerText : String
weakCompactnessBlockerText =
  "Blocker A: no proof in this module feeds the Sprint114 common carrier through Sprint110 weak subsequence extraction, bounded-energy tightness, and Mosco liminf consumption."

recoveryLimsupBlockerText : String
recoveryLimsupBlockerText =
  "Blocker B: no proof in this module feeds the Sprint114 common carrier through Sprint110 dense-core recovery, strong norm convergence, and energy limsup."

closedFormBlockerText : String
closedFormBlockerText =
  "Blocker C: no proof in this module feeds the Sprint114 common carrier through Sprint110 closed-form lower semicontinuity, closedness, semiboundedness, gauge-sector preservation, and liminf inequality."

normInputBlockerText : String
normInputBlockerText =
  "Blocker D: Sprint112 norm equivalence and Sprint114 uniform norm constants remain recorded requirements, not proved feed-through inputs."

residualInputBlockerText : String
residualInputBlockerText =
  "Blocker E: Sprint114 quadrature and inverse/projection residual closures remain open, so feed-through cannot treat E_a/P_a as closed comparison maps."

sectorInputBlockerText : String
sectorInputBlockerText =
  "Blocker F: gauge quotient independence, physical projection compatibility, and bottom/vacuum sector stability are recorded but not proved as one sector criterion."

commonCarrierConstructionBlockerText : String
commonCarrierConstructionBlockerText =
  "Blocker G: the external common-carrier construction flag stays false; this module does not replace the Sprint111 construction theorem."

transferLowerBoundBlockerText : String
transferLowerBoundBlockerText =
  "Blocker H: transfer lower-bound closure stays false until the feed-through criteria and external common-carrier construction are all discharged."

clayPromotionBlockerText : String
clayPromotionBlockerText =
  "Blocker I: Clay Yang-Mills promotion stays false because neither transfer lower-bound closure nor continuum mass-gap closure is proved here."

data FeedThroughLane : Set where
  sprint114-estimate-input-lane :
    FeedThroughLane
  sprint110-weak-input-lane :
    FeedThroughLane
  sprint110-closed-form-input-lane :
    FeedThroughLane
  sprint110-recovery-input-lane :
    FeedThroughLane
  sprint111-common-carrier-input-lane :
    FeedThroughLane
  sprint112-norm-input-lane :
    FeedThroughLane
  weak-compactness-feed-through-lane :
    FeedThroughLane
  closed-form-lsc-feed-through-lane :
    FeedThroughLane
  recovery-limsup-feed-through-lane :
    FeedThroughLane
  norm-residual-sector-input-lane :
    FeedThroughLane
  common-carrier-transfer-route-lane :
    FeedThroughLane
  blocker-lane :
    FeedThroughLane
  receipt-lane :
    FeedThroughLane

data FeedThroughStatus : Set where
  imported-stable-input :
    FeedThroughStatus
  source-path-recorded :
    FeedThroughStatus
  criterion-recorded :
    FeedThroughStatus
  norm-input-required :
    FeedThroughStatus
  residual-input-required :
    FeedThroughStatus
  sector-input-required :
    FeedThroughStatus
  feed-through-required :
    FeedThroughStatus
  external-theorem-open :
    FeedThroughStatus
  fail-closed-route-recorded :
    FeedThroughStatus
  exact-blocker-recorded :
    FeedThroughStatus
  fail-closed-nonpromotion :
    FeedThroughStatus

data BlockerKind : Set where
  weak-compactness-feed-blocker :
    BlockerKind
  closed-form-lsc-feed-blocker :
    BlockerKind
  recovery-limsup-feed-blocker :
    BlockerKind
  norm-input-blocker :
    BlockerKind
  residual-input-blocker :
    BlockerKind
  sector-input-blocker :
    BlockerKind
  common-carrier-construction-blocker :
    BlockerKind
  transfer-lower-bound-blocker :
    BlockerKind
  clay-promotion-blocker :
    BlockerKind

canonicalFeedThroughLanes : List FeedThroughLane
canonicalFeedThroughLanes =
  sprint114-estimate-input-lane
  ∷ sprint110-weak-input-lane
  ∷ sprint110-closed-form-input-lane
  ∷ sprint110-recovery-input-lane
  ∷ sprint111-common-carrier-input-lane
  ∷ sprint112-norm-input-lane
  ∷ weak-compactness-feed-through-lane
  ∷ closed-form-lsc-feed-through-lane
  ∷ recovery-limsup-feed-through-lane
  ∷ norm-residual-sector-input-lane
  ∷ common-carrier-transfer-route-lane
  ∷ blocker-lane
  ∷ receipt-lane
  ∷ []

record StableFeedInputs : Setω where
  constructor mkStableFeedInputs
  field
    sprint114EstimateReceipt :
      Estimate114.YMSprint114CommonCarrierEstimateClosureAssemblyReceipt
    sprint110WeakReceipt :
      Weak110.YMSprint110WeakCompactnessEnergyCoreReceipt
    sprint110ClosedFormReceipt :
      Closed110.YMSprint110ClosedFormLowerSemicontinuityCriterionReceipt
    sprint110RecoveryReceipt :
      Recovery110.YMSprint110RecoveryCoreDensityEnergyLimsupReceipt
    sprint111CommonCarrierReceipt :
      Carrier111.AssemblyReceipt
    sprint112UniformNormReceipt :
      Uniform112.YMSprint112UniformNormBoundReductionReceipt
    sprint114Path :
      String
    sprint110WeakPath :
      String
    sprint110ClosedFormPath :
      String
    sprint110RecoveryPath :
      String
    sprint111Path :
      String
    sprint112Path :
      String
    sprint114EstimateRecorded :
      Bool
    sprint110WeakRecorded :
      Bool
    sprint110ClosedFormRecorded :
      Bool
    sprint110RecoveryRecorded :
      Bool
    sprint111AssemblyRecorded :
      Bool
    sprint112ReductionRecorded :
      Bool
    sprint114EstimateClosed :
      Bool
    sprint110WeakExtractionClosed :
      Bool
    sprint110ClosedFormClosed :
      Bool
    sprint110RecoveryLimsupClosed :
      Bool
    sprint111CommonCarrierClosed :
      Bool
    sprint111TransferLowerBoundProved :
      Bool
    sprint112NormEquivalenceClosed :
      Bool
    sprint112WeakCompactnessFed :
      Bool
    sprint114EstimateClosedIsFalse :
      sprint114EstimateClosed ≡ false
    sprint110WeakExtractionClosedIsFalse :
      sprint110WeakExtractionClosed ≡ false
    sprint110ClosedFormClosedIsFalse :
      sprint110ClosedFormClosed ≡ false
    sprint110RecoveryLimsupClosedIsFalse :
      sprint110RecoveryLimsupClosed ≡ false
    sprint111CommonCarrierClosedIsFalse :
      sprint111CommonCarrierClosed ≡ false
    sprint111TransferLowerBoundProvedIsFalse :
      sprint111TransferLowerBoundProved ≡ false
    sprint112NormEquivalenceClosedIsFalse :
      sprint112NormEquivalenceClosed ≡ false
    sprint112WeakCompactnessFedIsFalse :
      sprint112WeakCompactnessFed ≡ false

record Sprint115SiblingPathLedger : Set where
  constructor mkSprint115SiblingPathLedger
  field
    weakFeedThroughSibling :
      String
    recoveryFeedThroughSibling :
      String
    closedFormFeedThroughSibling :
      String
    transferClosureSibling :
      String
    usesTextPathsOnly :
      Bool
    avoidsConcurrentSprint115Imports :
      Bool
    status :
      FeedThroughStatus

record WeakCompactnessFeedThrough : Setω where
  constructor mkWeakCompactnessFeedThrough
  field
    lane :
      FeedThroughLane
    statement :
      String
    weakReceipt :
      Weak110.YMSprint110WeakCompactnessEnergyCoreReceipt
    estimateReceipt :
      Estimate114.YMSprint114CommonCarrierEstimateClosureAssemblyReceipt
    sameHilbertCarrierRequired :
      Bool
    sameCutoffWindowRequired :
      Bool
    uniformNormComparisonRequired :
      Bool
    boundedEnergySequenceRequired :
      Bool
    tightnessControlsRequired :
      Bool
    gaugeSectorPreservationRequired :
      Bool
    recordedHere :
      Bool
    fedHere :
      Bool
    fedHereIsFalse :
      fedHere ≡ false
    status :
      FeedThroughStatus

record RecoveryLimsupFeedThrough : Setω where
  constructor mkRecoveryLimsupFeedThrough
  field
    lane :
      FeedThroughLane
    statement :
      String
    recoveryReceipt :
      Recovery110.YMSprint110RecoveryCoreDensityEnergyLimsupReceipt
    estimateReceipt :
      Estimate114.YMSprint114CommonCarrierEstimateClosureAssemblyReceipt
    denseFiniteCoreRequired :
      Bool
    interpolationMapRequired :
      Bool
    samplingMapRequired :
      Bool
    strongNormRecoveryRequired :
      Bool
    energyLimsupRequired :
      Bool
    renormalizedFormConventionRequired :
      Bool
    recordedHere :
      Bool
    fedHere :
      Bool
    fedHereIsFalse :
      fedHere ≡ false
    status :
      FeedThroughStatus

record ClosedFormLSCFeedThrough : Setω where
  constructor mkClosedFormLSCFeedThrough
  field
    lane :
      FeedThroughLane
    statement :
      String
    closedFormReceipt :
      Closed110.YMSprint110ClosedFormLowerSemicontinuityCriterionReceipt
    estimateReceipt :
      Estimate114.YMSprint114CommonCarrierEstimateClosureAssemblyReceipt
    formDomainIdentificationRequired :
      Bool
    closednessRequired :
      Bool
    semiboundednessRequired :
      Bool
    weakBoundedEnergySequenceRequired :
      Bool
    liminfInequalityRequired :
      Bool
    gaugeSectorPreservationRequired :
      Bool
    recordedHere :
      Bool
    fedHere :
      Bool
    fedHereIsFalse :
      fedHere ≡ false
    status :
      FeedThroughStatus

record NormResidualSectorCriterionInputs : Setω where
  constructor mkNormResidualSectorCriterionInputs
  field
    lane :
      FeedThroughLane
    statement :
      String
    uniformNormReceipt :
      Uniform112.YMSprint112UniformNormBoundReductionReceipt
    estimateReceipt :
      Estimate114.YMSprint114CommonCarrierEstimateClosureAssemblyReceipt
    upperNormBoundRequired :
      Bool
    lowerNormBoundRequired :
      Bool
    uniformNormConstantsRequired :
      Bool
    quadratureResidualClosureRequired :
      Bool
    inverseProjectionResidualClosureRequired :
      Bool
    gaugeQuotientRepresentativeIndependenceRequired :
      Bool
    physicalProjectionCompatibilityRequired :
      Bool
    vacuumNonVacuumSectorStabilityRequired :
      Bool
    normCriterionClosed :
      Bool
    residualCriterionClosed :
      Bool
    sectorCriterionClosed :
      Bool
    normCriterionClosedIsFalse :
      normCriterionClosed ≡ false
    residualCriterionClosedIsFalse :
      residualCriterionClosed ≡ false
    sectorCriterionClosedIsFalse :
      sectorCriterionClosed ≡ false
    status :
      FeedThroughStatus

record CommonCarrierTransferFailClosedRoute : Setω where
  constructor mkCommonCarrierTransferFailClosedRoute
  field
    lane :
      FeedThroughLane
    routeStatement :
      String
    carrierAssemblyReceipt :
      Carrier111.AssemblyReceipt
    estimateReceipt :
      Estimate114.YMSprint114CommonCarrierEstimateClosureAssemblyReceipt
    needsWeakCompactnessFeed :
      Bool
    needsClosedFormLSCFeed :
      Bool
    needsRecoveryLimsupFeed :
      Bool
    needsNormCriterionClosure :
      Bool
    needsResidualCriterionClosure :
      Bool
    needsSectorCriterionClosure :
      Bool
    needsExternalCommonCarrierConstruction :
      Bool
    routeRecorded :
      Bool
    externalCommonCarrierConstructionClosed :
      Bool
    commonCarrierFeedThroughClosed :
      Bool
    transferLowerBoundReady :
      Bool
    transferLowerBoundProved :
      Bool
    externalCommonCarrierConstructionClosedIsFalse :
      externalCommonCarrierConstructionClosed ≡ false
    commonCarrierFeedThroughClosedIsFalse :
      commonCarrierFeedThroughClosed ≡ false
    transferLowerBoundReadyIsFalse :
      transferLowerBoundReady ≡ false
    transferLowerBoundProvedIsFalse :
      transferLowerBoundProved ≡ false
    status :
      FeedThroughStatus

record BlockerReceipt : Set where
  constructor mkBlockerReceipt
  field
    blocker :
      BlockerKind
    lane :
      FeedThroughLane
    statement :
      String
    sourcePath :
      String
    blocksFeedThrough :
      Bool
    blocksCommonCarrierClosure :
      Bool
    blocksTransferLowerBound :
      Bool
    closedHere :
      Bool
    closedHereIsFalse :
      closedHere ≡ false
    status :
      FeedThroughStatus

record FeedThroughBlockerLedger : Set where
  constructor mkFeedThroughBlockerLedger
  field
    lane :
      FeedThroughLane
    blockerReceipts :
      List BlockerReceipt
    weakCompactnessBlocker :
      String
    closedFormBlocker :
      String
    recoveryLimsupBlocker :
      String
    normInputBlocker :
      String
    residualInputBlocker :
      String
    sectorInputBlocker :
      String
    commonCarrierConstructionBlocker :
      String
    transferLowerBoundBlocker :
      String
    clayPromotionBlocker :
      String
    allBlockersExact :
      Bool
    theoremStillOpen :
      Bool
    status :
      FeedThroughStatus

record TheoremBoundary : Set where
  constructor mkTheoremBoundary
  field
    boundaryStatement :
      String
    weakCompactnessFedHereFlag :
      Bool
    weakCompactnessFedHereIsFalse :
      weakCompactnessFedHereFlag ≡ false
    closedFormLowerSemicontinuityFedHereFlag :
      Bool
    closedFormLowerSemicontinuityFedHereIsFalse :
      closedFormLowerSemicontinuityFedHereFlag ≡ false
    recoveryLimsupFedHereFlag :
      Bool
    recoveryLimsupFedHereIsFalse :
      recoveryLimsupFedHereFlag ≡ false
    normCriterionClosedHereFlag :
      Bool
    normCriterionClosedHereIsFalse :
      normCriterionClosedHereFlag ≡ false
    residualCriterionClosedHereFlag :
      Bool
    residualCriterionClosedHereIsFalse :
      residualCriterionClosedHereFlag ≡ false
    sectorCriterionClosedHereFlag :
      Bool
    sectorCriterionClosedHereIsFalse :
      sectorCriterionClosedHereFlag ≡ false
    commonCarrierConstructionClosedExternallyHereFlag :
      Bool
    commonCarrierConstructionClosedExternallyHereIsFalse :
      commonCarrierConstructionClosedExternallyHereFlag ≡ false
    commonCarrierFeedThroughClosedHereFlag :
      Bool
    commonCarrierFeedThroughClosedHereIsFalse :
      commonCarrierFeedThroughClosedHereFlag ≡ false
    transferLowerBoundTheoremProvedHereFlag :
      Bool
    transferLowerBoundTheoremProvedHereIsFalse :
      transferLowerBoundTheoremProvedHereFlag ≡ false
    continuumMassGapProvedHereFlag :
      Bool
    continuumMassGapProvedHereIsFalse :
      continuumMassGapProvedHereFlag ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    status :
      FeedThroughStatus

record YMSprint115CommonCarrierFeedThroughCriterionReceipt : Setω where
  constructor mkYMSprint115CommonCarrierFeedThroughCriterionReceipt
  field
    sprint :
      Nat
    evidencePath :
      String
    stableInputs :
      StableFeedInputs
    sprint115SiblingPaths :
      Sprint115SiblingPathLedger
    weakCompactnessFeedThrough :
      WeakCompactnessFeedThrough
    closedFormLowerSemicontinuityFeedThrough :
      ClosedFormLSCFeedThrough
    recoveryLimsupFeedThrough :
      RecoveryLimsupFeedThrough
    normResidualSectorInputs :
      NormResidualSectorCriterionInputs
    transferRoute :
      CommonCarrierTransferFailClosedRoute
    blockers :
      FeedThroughBlockerLedger
    theoremBoundary :
      TheoremBoundary
    lanes :
      List FeedThroughLane
    evidenceLedger :
      List String
    receiptRecorded :
      Bool
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false

open YMSprint115CommonCarrierFeedThroughCriterionReceipt public

canonicalStableFeedInputs : StableFeedInputs
canonicalStableFeedInputs =
  mkStableFeedInputs
    Estimate114.canonicalReceipt
    Weak110.canonicalReceipt
    Closed110.canonicalReceipt
    Recovery110.canonicalReceipt
    Carrier111.canonicalAssemblyReceipt
    Uniform112.canonicalReceipt
    sprint114EstimateClosureSourcePath
    sprint110WeakCompactnessSourcePath
    sprint110ClosedFormSourcePath
    sprint110RecoverySourcePath
    sprint111CommonCarrierSourcePath
    sprint112UniformNormSourcePath
    importedSprint114EstimateReceiptRecorded
    importedSprint110WeakCoreRecorded
    importedSprint110ClosedFormCriterionRecorded
    importedSprint110RecoveryCoreRecorded
    importedSprint111AssemblyRecorded
    importedSprint112ReductionRecorded
    importedSprint114CommonCarrierEstimateClosed
    importedSprint110WeakExtractionClosed
    importedSprint110ClosedFormCriterionClosed
    importedSprint110RecoveryLimsupClosed
    importedSprint111CommonCarrierClosed
    importedSprint111TransferLowerBoundProved
    importedSprint112NormEquivalenceClosed
    importedSprint112WeakCompactnessFed
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalSprint115SiblingPathLedger : Sprint115SiblingPathLedger
canonicalSprint115SiblingPathLedger =
  mkSprint115SiblingPathLedger
    sprint115WeakFeedSiblingPath
    sprint115RecoveryFeedSiblingPath
    sprint115ClosedFormFeedSiblingPath
    sprint115TransferClosureSiblingPath
    true
    true
    source-path-recorded

canonicalWeakCompactnessFeedThrough :
  WeakCompactnessFeedThrough
canonicalWeakCompactnessFeedThrough =
  mkWeakCompactnessFeedThrough
    weak-compactness-feed-through-lane
    weakCompactnessFeedThroughText
    Weak110.canonicalReceipt
    Estimate114.canonicalReceipt
    true
    true
    true
    true
    true
    true
    weakCompactnessFeedThroughRecorded
    weakCompactnessFedHere
    refl
    feed-through-required

canonicalRecoveryLimsupFeedThrough :
  RecoveryLimsupFeedThrough
canonicalRecoveryLimsupFeedThrough =
  mkRecoveryLimsupFeedThrough
    recovery-limsup-feed-through-lane
    recoveryLimsupFeedThroughText
    Recovery110.canonicalReceipt
    Estimate114.canonicalReceipt
    true
    true
    true
    true
    true
    true
    recoveryLimsupFeedThroughRecorded
    recoveryLimsupFedHere
    refl
    feed-through-required

canonicalClosedFormLSCFeedThrough :
  ClosedFormLSCFeedThrough
canonicalClosedFormLSCFeedThrough =
  mkClosedFormLSCFeedThrough
    closed-form-lsc-feed-through-lane
    closedFormLowerSemicontinuityFeedThroughText
    Closed110.canonicalReceipt
    Estimate114.canonicalReceipt
    true
    true
    true
    true
    true
    true
    closedFormLowerSemicontinuityFeedThroughRecorded
    closedFormLowerSemicontinuityFedHere
    refl
    feed-through-required

canonicalNormResidualSectorCriterionInputs :
  NormResidualSectorCriterionInputs
canonicalNormResidualSectorCriterionInputs =
  mkNormResidualSectorCriterionInputs
    norm-residual-sector-input-lane
    normResidualSectorInputsText
    Uniform112.canonicalReceipt
    Estimate114.canonicalReceipt
    true
    true
    true
    true
    true
    true
    true
    true
    normCriterionClosedHere
    residualCriterionClosedHere
    sectorCriterionClosedHere
    refl
    refl
    refl
    criterion-recorded

canonicalCommonCarrierTransferFailClosedRoute :
  CommonCarrierTransferFailClosedRoute
canonicalCommonCarrierTransferFailClosedRoute =
  mkCommonCarrierTransferFailClosedRoute
    common-carrier-transfer-route-lane
    failClosedCommonCarrierTransferRouteText
    Carrier111.canonicalAssemblyReceipt
    Estimate114.canonicalReceipt
    true
    true
    true
    true
    true
    true
    true
    failClosedCommonCarrierTransferRouteRecorded
    commonCarrierConstructionClosedExternallyHere
    commonCarrierFeedThroughClosedHere
    commonCarrierTransferLowerBoundReadyHere
    transferLowerBoundTheoremProvedHere
    refl
    refl
    refl
    refl
    fail-closed-route-recorded

canonicalBlockerReceipts : List BlockerReceipt
canonicalBlockerReceipts =
  mkBlockerReceipt
    weak-compactness-feed-blocker
    weak-compactness-feed-through-lane
    weakCompactnessBlockerText
    sprint110WeakCompactnessSourcePath
    true
    true
    true
    weakCompactnessFedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerReceipt
    closed-form-lsc-feed-blocker
    closed-form-lsc-feed-through-lane
    closedFormBlockerText
    sprint110ClosedFormSourcePath
    true
    true
    true
    closedFormLowerSemicontinuityFedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerReceipt
    recovery-limsup-feed-blocker
    recovery-limsup-feed-through-lane
    recoveryLimsupBlockerText
    sprint110RecoverySourcePath
    true
    true
    true
    recoveryLimsupFedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerReceipt
    norm-input-blocker
    norm-residual-sector-input-lane
    normInputBlockerText
    sprint112UniformNormSourcePath
    true
    true
    true
    normCriterionClosedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerReceipt
    residual-input-blocker
    norm-residual-sector-input-lane
    residualInputBlockerText
    sprint114EstimateClosureSourcePath
    true
    true
    true
    residualCriterionClosedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerReceipt
    sector-input-blocker
    norm-residual-sector-input-lane
    sectorInputBlockerText
    sprint114EstimateClosureSourcePath
    true
    true
    true
    sectorCriterionClosedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerReceipt
    common-carrier-construction-blocker
    common-carrier-transfer-route-lane
    commonCarrierConstructionBlockerText
    sprint111CommonCarrierSourcePath
    true
    true
    true
    commonCarrierConstructionClosedExternallyHere
    refl
    external-theorem-open
  ∷ mkBlockerReceipt
    transfer-lower-bound-blocker
    common-carrier-transfer-route-lane
    transferLowerBoundBlockerText
    sprint111CommonCarrierSourcePath
    true
    true
    true
    transferLowerBoundTheoremProvedHere
    refl
    fail-closed-route-recorded
  ∷ mkBlockerReceipt
    clay-promotion-blocker
    receipt-lane
    clayPromotionBlockerText
    modulePath
    true
    true
    true
    clayYangMillsPromoted
    refl
    fail-closed-nonpromotion
  ∷ []

canonicalFeedThroughBlockerLedger : FeedThroughBlockerLedger
canonicalFeedThroughBlockerLedger =
  mkFeedThroughBlockerLedger
    blocker-lane
    canonicalBlockerReceipts
    weakCompactnessBlockerText
    closedFormBlockerText
    recoveryLimsupBlockerText
    normInputBlockerText
    residualInputBlockerText
    sectorInputBlockerText
    commonCarrierConstructionBlockerText
    transferLowerBoundBlockerText
    clayPromotionBlockerText
    true
    true
    exact-blocker-recorded

canonicalTheoremBoundary : TheoremBoundary
canonicalTheoremBoundary =
  mkTheoremBoundary
    nonPromotionBoundaryText
    weakCompactnessFedHere
    refl
    closedFormLowerSemicontinuityFedHere
    refl
    recoveryLimsupFedHere
    refl
    normCriterionClosedHere
    refl
    residualCriterionClosedHere
    refl
    sectorCriterionClosedHere
    refl
    commonCarrierConstructionClosedExternallyHere
    refl
    commonCarrierFeedThroughClosedHere
    refl
    transferLowerBoundTheoremProvedHere
    refl
    continuumMassGapProvedHere
    refl
    clayYangMillsPromoted
    refl
    fail-closed-nonpromotion

canonicalEvidenceLedger : List String
canonicalEvidenceLedger =
  weakCompactnessFeedThroughText
  ∷ closedFormLowerSemicontinuityFeedThroughText
  ∷ recoveryLimsupFeedThroughText
  ∷ normResidualSectorInputsText
  ∷ failClosedCommonCarrierTransferRouteText
  ∷ weakCompactnessBlockerText
  ∷ closedFormBlockerText
  ∷ recoveryLimsupBlockerText
  ∷ normInputBlockerText
  ∷ residualInputBlockerText
  ∷ sectorInputBlockerText
  ∷ commonCarrierConstructionBlockerText
  ∷ transferLowerBoundBlockerText
  ∷ clayPromotionBlockerText
  ∷ nonPromotionBoundaryText
  ∷ []

canonicalYMSprint115CommonCarrierFeedThroughCriterionReceipt :
  YMSprint115CommonCarrierFeedThroughCriterionReceipt
canonicalYMSprint115CommonCarrierFeedThroughCriterionReceipt =
  mkYMSprint115CommonCarrierFeedThroughCriterionReceipt
    sprintNumber
    modulePath
    canonicalStableFeedInputs
    canonicalSprint115SiblingPathLedger
    canonicalWeakCompactnessFeedThrough
    canonicalClosedFormLSCFeedThrough
    canonicalRecoveryLimsupFeedThrough
    canonicalNormResidualSectorCriterionInputs
    canonicalCommonCarrierTransferFailClosedRoute
    canonicalFeedThroughBlockerLedger
    canonicalTheoremBoundary
    canonicalFeedThroughLanes
    canonicalEvidenceLedger
    feedThroughCriterionRecorded
    clayYangMillsPromoted
    refl

canonicalReceipt :
  YMSprint115CommonCarrierFeedThroughCriterionReceipt
canonicalReceipt =
  canonicalYMSprint115CommonCarrierFeedThroughCriterionReceipt

canonicalWeakCompactnessFedHereIsFalse :
  TheoremBoundary.weakCompactnessFedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalWeakCompactnessFedHereIsFalse =
  refl

canonicalClosedFormLowerSemicontinuityFedHereIsFalse :
  TheoremBoundary.closedFormLowerSemicontinuityFedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalClosedFormLowerSemicontinuityFedHereIsFalse =
  refl

canonicalRecoveryLimsupFedHereIsFalse :
  TheoremBoundary.recoveryLimsupFedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalRecoveryLimsupFedHereIsFalse =
  refl

canonicalNormCriterionClosedHereIsFalse :
  TheoremBoundary.normCriterionClosedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalNormCriterionClosedHereIsFalse =
  refl

canonicalResidualCriterionClosedHereIsFalse :
  TheoremBoundary.residualCriterionClosedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalResidualCriterionClosedHereIsFalse =
  refl

canonicalSectorCriterionClosedHereIsFalse :
  TheoremBoundary.sectorCriterionClosedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalSectorCriterionClosedHereIsFalse =
  refl

canonicalExternalCommonCarrierConstructionClosedHereIsFalse :
  TheoremBoundary.commonCarrierConstructionClosedExternallyHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalExternalCommonCarrierConstructionClosedHereIsFalse =
  refl

canonicalCommonCarrierFeedThroughClosedHereIsFalse :
  TheoremBoundary.commonCarrierFeedThroughClosedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalCommonCarrierFeedThroughClosedHereIsFalse =
  refl

canonicalTransferLowerBoundTheoremProvedHereIsFalse :
  TheoremBoundary.transferLowerBoundTheoremProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalTransferLowerBoundTheoremProvedHereIsFalse =
  refl

canonicalContinuumMassGapProvedHereIsFalse :
  TheoremBoundary.continuumMassGapProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalContinuumMassGapProvedHereIsFalse =
  refl

canonicalClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalClayYangMillsPromotedIsFalse =
  refl

canonicalTransferRoute :
  CommonCarrierTransferFailClosedRoute
canonicalTransferRoute =
  transferRoute canonicalReceipt

canonicalNormResidualSectorInputs :
  NormResidualSectorCriterionInputs
canonicalNormResidualSectorInputs =
  normResidualSectorInputs canonicalReceipt

canonicalBlockers :
  FeedThroughBlockerLedger
canonicalBlockers =
  blockers canonicalReceipt

canonicalSiblingPaths :
  Sprint115SiblingPathLedger
canonicalSiblingPaths =
  sprint115SiblingPaths canonicalReceipt
