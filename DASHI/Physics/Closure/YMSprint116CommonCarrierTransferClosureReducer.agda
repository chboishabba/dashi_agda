module DASHI.Physics.Closure.YMSprint116CommonCarrierTransferClosureReducer where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint110CommonCarrierHilbertIdentification
  as Carrier110
import DASHI.Physics.Closure.YMSprint110WeakCompactnessEnergyCore
  as Weak110
import DASHI.Physics.Closure.YMSprint110ClosedFormLowerSemicontinuityCriterion
  as Closed110
import DASHI.Physics.Closure.YMSprint110RecoveryCoreDensityEnergyLimsup
  as Recovery110
import DASHI.Physics.Closure.YMSprint111CommonCarrierConstructionAssembly
  as Carrier111
import DASHI.Physics.Closure.YMSprint114CommonCarrierEstimateClosureAssembly
  as Estimate114
import DASHI.Physics.Closure.YMSprint115CommonCarrierFeedThroughCriterion
  as Feed115

------------------------------------------------------------------------
-- Sprint116 common-carrier transfer closure reducer.
--
-- This module consumes the Sprint115 common-carrier feed-through criterion
-- and stable Sprint110/Sprint111/Sprint114 receipts.  It records an inhabited
-- reducer from common-carrier construction supply, weak compactness,
-- closed-form lower semicontinuity, recovery limsup, and norm/residual/sector
-- dependencies into transfer lower-bound readiness.
--
-- The reducer is deliberately fail-closed.  It imports no Sprint116 sibling
-- modules, proves no transfer lower-bound theorem, proves no continuum mass
-- gap theorem, and keeps Clay Yang-Mills promotion false.

sprintNumber : Nat
sprintNumber = 116

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint116CommonCarrierTransferClosureReducer.agda"

sprint110CarrierModuleName : String
sprint110CarrierModuleName =
  "DASHI.Physics.Closure.YMSprint110CommonCarrierHilbertIdentification"

sprint110WeakModuleName : String
sprint110WeakModuleName =
  "DASHI.Physics.Closure.YMSprint110WeakCompactnessEnergyCore"

sprint110ClosedFormModuleName : String
sprint110ClosedFormModuleName =
  "DASHI.Physics.Closure.YMSprint110ClosedFormLowerSemicontinuityCriterion"

sprint110RecoveryModuleName : String
sprint110RecoveryModuleName =
  "DASHI.Physics.Closure.YMSprint110RecoveryCoreDensityEnergyLimsup"

sprint111CarrierModuleName : String
sprint111CarrierModuleName =
  "DASHI.Physics.Closure.YMSprint111CommonCarrierConstructionAssembly"

sprint114EstimateModuleName : String
sprint114EstimateModuleName =
  "DASHI.Physics.Closure.YMSprint114CommonCarrierEstimateClosureAssembly"

sprint115FeedThroughModuleName : String
sprint115FeedThroughModuleName =
  "DASHI.Physics.Closure.YMSprint115CommonCarrierFeedThroughCriterion"

sprint110CarrierSourcePath : String
sprint110CarrierSourcePath =
  "DASHI/Physics/Closure/YMSprint110CommonCarrierHilbertIdentification.agda"

sprint110WeakSourcePath : String
sprint110WeakSourcePath =
  Feed115.sprint110WeakCompactnessSourcePath

sprint110ClosedFormSourcePath : String
sprint110ClosedFormSourcePath =
  Feed115.sprint110ClosedFormSourcePath

sprint110RecoverySourcePath : String
sprint110RecoverySourcePath =
  Feed115.sprint110RecoverySourcePath

sprint111CarrierSourcePath : String
sprint111CarrierSourcePath =
  Feed115.sprint111CommonCarrierSourcePath

sprint112UniformNormSourcePath : String
sprint112UniformNormSourcePath =
  Feed115.sprint112UniformNormSourcePath

sprint114EstimateSourcePath : String
sprint114EstimateSourcePath =
  Feed115.sprint114EstimateClosureSourcePath

sprint115FeedThroughSourcePath : String
sprint115FeedThroughSourcePath =
  Feed115.modulePath

reducerRecorded : Bool
reducerRecorded = true

commonCarrierConstructionSupplyRecorded : Bool
commonCarrierConstructionSupplyRecorded = true

weakCompactnessFeedRecorded : Bool
weakCompactnessFeedRecorded = true

closedFormLSCFeedRecorded : Bool
closedFormLSCFeedRecorded = true

recoveryLimsupFeedRecorded : Bool
recoveryLimsupFeedRecorded = true

normResidualSectorDependencyRecorded : Bool
normResidualSectorDependencyRecorded = true

transferReadinessReducerRecorded : Bool
transferReadinessReducerRecorded = true

commonCarrierConstructionClosedExternallyHere : Bool
commonCarrierConstructionClosedExternallyHere = false

externalCommonCarrierClosedHere : Bool
externalCommonCarrierClosedHere = false

commonCarrierFeedThroughClosedHere : Bool
commonCarrierFeedThroughClosedHere = false

weakCompactnessFedHere : Bool
weakCompactnessFedHere = false

closedFormLowerSemicontinuityFedHere : Bool
closedFormLowerSemicontinuityFedHere = false

recoveryLimsupFedHere : Bool
recoveryLimsupFedHere = false

normCriterionClosedHere : Bool
normCriterionClosedHere = false

residualCriterionClosedHere : Bool
residualCriterionClosedHere = false

sectorCriterionClosedHere : Bool
sectorCriterionClosedHere = false

transferLowerBoundReadyHere : Bool
transferLowerBoundReadyHere = false

transferLowerBoundTheoremProvedHere : Bool
transferLowerBoundTheoremProvedHere = false

continuumMassGapProvedHere : Bool
continuumMassGapProvedHere = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

feed115CriterionImported : Bool
feed115CriterionImported =
  Feed115.feedThroughCriterionRecorded

feed115CommonCarrierConstructionClosedExternallyInput : Bool
feed115CommonCarrierConstructionClosedExternallyInput =
  Feed115.commonCarrierConstructionClosedExternallyHere

feed115CommonCarrierFeedThroughClosedInput : Bool
feed115CommonCarrierFeedThroughClosedInput =
  Feed115.commonCarrierFeedThroughClosedHere

feed115TransferReadyInput : Bool
feed115TransferReadyInput =
  Feed115.commonCarrierTransferLowerBoundReadyHere

carrier110Imported : Bool
carrier110Imported =
  Carrier110.commonCarrierReceiptRecorded

weak110Imported : Bool
weak110Imported =
  Weak110.weakCompactnessEnergyCoreRecorded

closed110Imported : Bool
closed110Imported =
  Closed110.criterionReceiptRecorded

recovery110Imported : Bool
recovery110Imported =
  Recovery110.receiptRecorded

carrier111Imported : Bool
carrier111Imported =
  Carrier111.sprint111AssemblyRecorded

estimate114Imported : Bool
estimate114Imported =
  Estimate114.assemblyRecorded

commonCarrierConstructionSupplyText : String
commonCarrierConstructionSupplyText =
  "Common-carrier construction supply closes externally only when Sprint111 construction, Sprint110 carrier identification, and Sprint114 estimate closure use one physical Hilbert carrier, one E_a/P_a convention, and one gauge quotient/sector split."

weakCompactnessFeedText : String
weakCompactnessFeedText =
  "Weak compactness feed requires the Sprint115 feed-through criterion plus Sprint110 weak subsequence extraction on the same bounded-energy finite transfer-form sequence and same common carrier."

closedFormLSCFeedText : String
closedFormLSCFeedText =
  "Closed-form LSC feed requires Sprint110 domain identification, closedness, semiboundedness, gauge-sector preservation, and liminf inequality on the Sprint115 common carrier."

recoveryLimsupFeedText : String
recoveryLimsupFeedText =
  "Recovery limsup feed requires Sprint110 dense finite physical core, interpolation/sampling maps, strong norm recovery, and energy limsup with the Sprint115 carrier and renormalized form convention."

normDependencyText : String
normDependencyText =
  "Norm dependency: Sprint112 uniform upper/lower norm bounds and Sprint114 uniform constant assembly must be available before transfer readiness can consume the common carrier."

residualDependencyText : String
residualDependencyText =
  "Residual dependency: Sprint114 quadrature residual and inverse/projection residual closure must vanish in the same E_a/P_a convention before transfer readiness can open."

sectorDependencyText : String
sectorDependencyText =
  "Sector dependency: gauge quotient representative independence, physical projection compatibility, and vacuum/non-vacuum sector stability must close before transfer readiness can open."

failClosedReducerText : String
failClosedReducerText =
  "Fail-closed reducer: transfer lower-bound readiness is false unless external common-carrier construction, common-carrier feed-through, weak compactness, closed-form LSC, recovery limsup, norm closure, residual closure, and sector closure are all supplied."

nonPromotionBoundaryText : String
nonPromotionBoundaryText =
  "Sprint116 reduces feed-through obligations to transfer lower-bound readiness only; transfer theorem, continuum mass gap, and Clay Yang-Mills promotion remain false."

data ReducerLane : Set where
  sprint115-feed-through-input-lane :
    ReducerLane
  common-carrier-construction-supply-lane :
    ReducerLane
  weak-compactness-feed-lane :
    ReducerLane
  closed-form-lsc-feed-lane :
    ReducerLane
  recovery-limsup-feed-lane :
    ReducerLane
  norm-dependency-lane :
    ReducerLane
  residual-dependency-lane :
    ReducerLane
  sector-dependency-lane :
    ReducerLane
  transfer-readiness-reducer-lane :
    ReducerLane
  theorem-boundary-lane :
    ReducerLane

data ReducerStatus : Set where
  imported-stable-input :
    ReducerStatus
  imported-sprint115-feed-through :
    ReducerStatus
  source-path-recorded :
    ReducerStatus
  supply-recorded :
    ReducerStatus
  feed-recorded :
    ReducerStatus
  dependency-recorded :
    ReducerStatus
  transfer-readiness-fail-closed :
    ReducerStatus
  theorem-open :
    ReducerStatus
  fail-closed-nonpromotion :
    ReducerStatus

canonicalReducerLanes : List ReducerLane
canonicalReducerLanes =
  sprint115-feed-through-input-lane
  ∷ common-carrier-construction-supply-lane
  ∷ weak-compactness-feed-lane
  ∷ closed-form-lsc-feed-lane
  ∷ recovery-limsup-feed-lane
  ∷ norm-dependency-lane
  ∷ residual-dependency-lane
  ∷ sector-dependency-lane
  ∷ transfer-readiness-reducer-lane
  ∷ theorem-boundary-lane
  ∷ []

record StableImportedReceipts : Setω where
  constructor mkStableImportedReceipts
  field
    carrier110Receipt :
      Carrier110.YMSprint110CommonCarrierHilbertIdentificationReceipt
    weak110Receipt :
      Weak110.YMSprint110WeakCompactnessEnergyCoreReceipt
    closed110Receipt :
      Closed110.YMSprint110ClosedFormLowerSemicontinuityCriterionReceipt
    recovery110Receipt :
      Recovery110.YMSprint110RecoveryCoreDensityEnergyLimsupReceipt
    carrier111Receipt :
      Carrier111.AssemblyReceipt
    estimate114Receipt :
      Estimate114.YMSprint114CommonCarrierEstimateClosureAssemblyReceipt
    feed115Receipt :
      Feed115.YMSprint115CommonCarrierFeedThroughCriterionReceipt
    stableReceiptsRecorded :
      Bool
    sprint115FeedThroughRecorded :
      Bool
    status :
      ReducerStatus

record DependencyByPathName : Set where
  constructor mkDependencyByPathName
  field
    lane :
      ReducerLane
    moduleName :
      String
    sourcePath :
      String
    statement :
      String
    recordedByPathName :
      Bool
    closedHere :
      Bool
    closedHereIsFalse :
      closedHere ≡ false
    status :
      ReducerStatus

record CommonCarrierConstructionSupply : Setω where
  constructor mkCommonCarrierConstructionSupply
  field
    lane :
      ReducerLane
    statement :
      String
    carrier110Receipt :
      Carrier110.YMSprint110CommonCarrierHilbertIdentificationReceipt
    carrier111Receipt :
      Carrier111.AssemblyReceipt
    estimate114Receipt :
      Estimate114.YMSprint114CommonCarrierEstimateClosureAssemblyReceipt
    feed115Route :
      Feed115.CommonCarrierTransferFailClosedRoute
    sprint110CarrierRecorded :
      Bool
    sprint111ConstructionCriterionRecorded :
      Bool
    sprint114EstimateClosureRecorded :
      Bool
    feed115RouteRecorded :
      Bool
    supplyRecorded :
      Bool
    commonCarrierConstructionClosedExternally :
      Bool
    externalCommonCarrierClosed :
      Bool
    commonCarrierConstructionClosedExternallyIsFalse :
      commonCarrierConstructionClosedExternally ≡ false
    externalCommonCarrierClosedIsFalse :
      externalCommonCarrierClosed ≡ false
    status :
      ReducerStatus

record WeakCompactnessFeed : Setω where
  constructor mkWeakCompactnessFeed
  field
    lane :
      ReducerLane
    statement :
      String
    weak110Receipt :
      Weak110.YMSprint110WeakCompactnessEnergyCoreReceipt
    feed115Weak :
      Feed115.WeakCompactnessFeedThrough
    sameCarrierRequired :
      Bool
    boundedEnergySequenceRequired :
      Bool
    tightnessRequired :
      Bool
    feedRecorded :
      Bool
    fedHere :
      Bool
    fedHereIsFalse :
      fedHere ≡ false
    status :
      ReducerStatus

record ClosedFormLSCFeed : Setω where
  constructor mkClosedFormLSCFeed
  field
    lane :
      ReducerLane
    statement :
      String
    closed110Receipt :
      Closed110.YMSprint110ClosedFormLowerSemicontinuityCriterionReceipt
    feed115Closed :
      Feed115.ClosedFormLSCFeedThrough
    domainIdentificationRequired :
      Bool
    closednessSemiboundednessRequired :
      Bool
    liminfInequalityRequired :
      Bool
    gaugeSectorPreservationRequired :
      Bool
    feedRecorded :
      Bool
    fedHere :
      Bool
    fedHereIsFalse :
      fedHere ≡ false
    status :
      ReducerStatus

record RecoveryLimsupFeed : Setω where
  constructor mkRecoveryLimsupFeed
  field
    lane :
      ReducerLane
    statement :
      String
    recovery110Receipt :
      Recovery110.YMSprint110RecoveryCoreDensityEnergyLimsupReceipt
    feed115Recovery :
      Feed115.RecoveryLimsupFeedThrough
    denseCoreRequired :
      Bool
    interpolationSamplingRequired :
      Bool
    strongNormRecoveryRequired :
      Bool
    energyLimsupRequired :
      Bool
    feedRecorded :
      Bool
    fedHere :
      Bool
    fedHereIsFalse :
      fedHere ≡ false
    status :
      ReducerStatus

record NormResidualSectorDependencies : Setω where
  constructor mkNormResidualSectorDependencies
  field
    feed115Inputs :
      Feed115.NormResidualSectorCriterionInputs
    normDependency :
      DependencyByPathName
    residualDependency :
      DependencyByPathName
    sectorDependency :
      DependencyByPathName
    dependenciesRecorded :
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
      ReducerStatus

record FailClosedTransferRouteReducer : Setω where
  constructor mkFailClosedTransferRouteReducer
  field
    lane :
      ReducerLane
    routeStatement :
      String
    feed115TransferRoute :
      Feed115.CommonCarrierTransferFailClosedRoute
    constructionSupply :
      CommonCarrierConstructionSupply
    weakFeed :
      WeakCompactnessFeed
    closedFormFeed :
      ClosedFormLSCFeed
    recoveryFeed :
      RecoveryLimsupFeed
    normResidualSectorDependencies :
      NormResidualSectorDependencies
    routeRecorded :
      Bool
    externalCommonCarrierClosed :
      Bool
    commonCarrierConstructionClosedExternally :
      Bool
    commonCarrierFeedThroughClosed :
      Bool
    weakCompactnessFed :
      Bool
    closedFormLowerSemicontinuityFed :
      Bool
    recoveryLimsupFed :
      Bool
    normCriterionClosed :
      Bool
    residualCriterionClosed :
      Bool
    sectorCriterionClosed :
      Bool
    transferLowerBoundReady :
      Bool
    transferLowerBoundTheoremProved :
      Bool
    externalCommonCarrierClosedIsFalse :
      externalCommonCarrierClosed ≡ false
    commonCarrierConstructionClosedExternallyIsFalse :
      commonCarrierConstructionClosedExternally ≡ false
    commonCarrierFeedThroughClosedIsFalse :
      commonCarrierFeedThroughClosed ≡ false
    transferLowerBoundReadyIsFalse :
      transferLowerBoundReady ≡ false
    transferLowerBoundTheoremProvedIsFalse :
      transferLowerBoundTheoremProved ≡ false
    status :
      ReducerStatus

record TheoremBoundary : Set where
  constructor mkTheoremBoundary
  field
    boundaryStatement :
      String
    transferLowerBoundReadyHereFlag :
      Bool
    transferLowerBoundReadyHereIsFalse :
      transferLowerBoundReadyHereFlag ≡ false
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
      ReducerStatus

record YMSprint116CommonCarrierTransferClosureReducerReceipt : Setω where
  constructor mkYMSprint116CommonCarrierTransferClosureReducerReceipt
  field
    sprint :
      Nat
    evidencePath :
      String
    importedReceipts :
      StableImportedReceipts
    constructionSupply :
      CommonCarrierConstructionSupply
    weakFeed :
      WeakCompactnessFeed
    closedFormFeed :
      ClosedFormLSCFeed
    recoveryFeed :
      RecoveryLimsupFeed
    normResidualSectorDependencies :
      NormResidualSectorDependencies
    transferRouteReducer :
      FailClosedTransferRouteReducer
    theoremBoundary :
      TheoremBoundary
    lanes :
      List ReducerLane
    evidenceLedger :
      List String
    receiptRecorded :
      Bool
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false

open YMSprint116CommonCarrierTransferClosureReducerReceipt public

canonicalImportedReceipts : StableImportedReceipts
canonicalImportedReceipts =
  mkStableImportedReceipts
    Carrier110.canonicalReceipt
    Weak110.canonicalReceipt
    Closed110.canonicalReceipt
    Recovery110.canonicalReceipt
    Carrier111.canonicalAssemblyReceipt
    Estimate114.canonicalReceipt
    Feed115.canonicalReceipt
    true
    feed115CriterionImported
    imported-stable-input

canonicalCommonCarrierConstructionSupply :
  CommonCarrierConstructionSupply
canonicalCommonCarrierConstructionSupply =
  mkCommonCarrierConstructionSupply
    common-carrier-construction-supply-lane
    commonCarrierConstructionSupplyText
    Carrier110.canonicalReceipt
    Carrier111.canonicalAssemblyReceipt
    Estimate114.canonicalReceipt
    Feed115.canonicalCommonCarrierTransferFailClosedRoute
    carrier110Imported
    Carrier111.constructionCriteriaRecorded
    estimate114Imported
    Feed115.failClosedCommonCarrierTransferRouteRecorded
    commonCarrierConstructionSupplyRecorded
    commonCarrierConstructionClosedExternallyHere
    externalCommonCarrierClosedHere
    refl
    refl
    supply-recorded

canonicalWeakCompactnessFeed : WeakCompactnessFeed
canonicalWeakCompactnessFeed =
  mkWeakCompactnessFeed
    weak-compactness-feed-lane
    weakCompactnessFeedText
    Weak110.canonicalReceipt
    Feed115.canonicalWeakCompactnessFeedThrough
    true
    true
    true
    weakCompactnessFeedRecorded
    weakCompactnessFedHere
    refl
    feed-recorded

canonicalClosedFormLSCFeed : ClosedFormLSCFeed
canonicalClosedFormLSCFeed =
  mkClosedFormLSCFeed
    closed-form-lsc-feed-lane
    closedFormLSCFeedText
    Closed110.canonicalReceipt
    Feed115.canonicalClosedFormLSCFeedThrough
    true
    true
    true
    true
    closedFormLSCFeedRecorded
    closedFormLowerSemicontinuityFedHere
    refl
    feed-recorded

canonicalRecoveryLimsupFeed : RecoveryLimsupFeed
canonicalRecoveryLimsupFeed =
  mkRecoveryLimsupFeed
    recovery-limsup-feed-lane
    recoveryLimsupFeedText
    Recovery110.canonicalReceipt
    Feed115.canonicalRecoveryLimsupFeedThrough
    true
    true
    true
    true
    recoveryLimsupFeedRecorded
    recoveryLimsupFedHere
    refl
    feed-recorded

canonicalNormDependency : DependencyByPathName
canonicalNormDependency =
  mkDependencyByPathName
    norm-dependency-lane
    "DASHI.Physics.Closure.YMSprint112UniformNormBoundReduction"
    sprint112UniformNormSourcePath
    normDependencyText
    true
    normCriterionClosedHere
    refl
    dependency-recorded

canonicalResidualDependency : DependencyByPathName
canonicalResidualDependency =
  mkDependencyByPathName
    residual-dependency-lane
    sprint114EstimateModuleName
    sprint114EstimateSourcePath
    residualDependencyText
    true
    residualCriterionClosedHere
    refl
    dependency-recorded

canonicalSectorDependency : DependencyByPathName
canonicalSectorDependency =
  mkDependencyByPathName
    sector-dependency-lane
    sprint111CarrierModuleName
    sprint111CarrierSourcePath
    sectorDependencyText
    true
    sectorCriterionClosedHere
    refl
    dependency-recorded

canonicalNormResidualSectorDependencies :
  NormResidualSectorDependencies
canonicalNormResidualSectorDependencies =
  mkNormResidualSectorDependencies
    Feed115.canonicalNormResidualSectorCriterionInputs
    canonicalNormDependency
    canonicalResidualDependency
    canonicalSectorDependency
    normResidualSectorDependencyRecorded
    normCriterionClosedHere
    residualCriterionClosedHere
    sectorCriterionClosedHere
    refl
    refl
    refl
    dependency-recorded

canonicalFailClosedTransferRouteReducer :
  FailClosedTransferRouteReducer
canonicalFailClosedTransferRouteReducer =
  mkFailClosedTransferRouteReducer
    transfer-readiness-reducer-lane
    failClosedReducerText
    Feed115.canonicalCommonCarrierTransferFailClosedRoute
    canonicalCommonCarrierConstructionSupply
    canonicalWeakCompactnessFeed
    canonicalClosedFormLSCFeed
    canonicalRecoveryLimsupFeed
    canonicalNormResidualSectorDependencies
    transferReadinessReducerRecorded
    externalCommonCarrierClosedHere
    commonCarrierConstructionClosedExternallyHere
    commonCarrierFeedThroughClosedHere
    weakCompactnessFedHere
    closedFormLowerSemicontinuityFedHere
    recoveryLimsupFedHere
    normCriterionClosedHere
    residualCriterionClosedHere
    sectorCriterionClosedHere
    transferLowerBoundReadyHere
    transferLowerBoundTheoremProvedHere
    refl
    refl
    refl
    refl
    refl
    transfer-readiness-fail-closed

canonicalTheoremBoundary : TheoremBoundary
canonicalTheoremBoundary =
  mkTheoremBoundary
    nonPromotionBoundaryText
    transferLowerBoundReadyHere
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
  modulePath
  ∷ sprint115FeedThroughSourcePath
  ∷ sprint110CarrierSourcePath
  ∷ sprint110WeakSourcePath
  ∷ sprint110ClosedFormSourcePath
  ∷ sprint110RecoverySourcePath
  ∷ sprint111CarrierSourcePath
  ∷ sprint114EstimateSourcePath
  ∷ sprint112UniformNormSourcePath
  ∷ commonCarrierConstructionSupplyText
  ∷ weakCompactnessFeedText
  ∷ closedFormLSCFeedText
  ∷ recoveryLimsupFeedText
  ∷ normDependencyText
  ∷ residualDependencyText
  ∷ sectorDependencyText
  ∷ failClosedReducerText
  ∷ nonPromotionBoundaryText
  ∷ []

canonicalYMSprint116CommonCarrierTransferClosureReducerReceipt :
  YMSprint116CommonCarrierTransferClosureReducerReceipt
canonicalYMSprint116CommonCarrierTransferClosureReducerReceipt =
  mkYMSprint116CommonCarrierTransferClosureReducerReceipt
    sprintNumber
    modulePath
    canonicalImportedReceipts
    canonicalCommonCarrierConstructionSupply
    canonicalWeakCompactnessFeed
    canonicalClosedFormLSCFeed
    canonicalRecoveryLimsupFeed
    canonicalNormResidualSectorDependencies
    canonicalFailClosedTransferRouteReducer
    canonicalTheoremBoundary
    canonicalReducerLanes
    canonicalEvidenceLedger
    reducerRecorded
    clayYangMillsPromoted
    refl

canonicalReceipt :
  YMSprint116CommonCarrierTransferClosureReducerReceipt
canonicalReceipt =
  canonicalYMSprint116CommonCarrierTransferClosureReducerReceipt

canonicalReceiptExternalCommonCarrierClosedHereIsFalse :
  externalCommonCarrierClosedHere ≡ false
canonicalReceiptExternalCommonCarrierClosedHereIsFalse =
  refl

canonicalReceiptCommonCarrierConstructionClosedExternallyHereIsFalse :
  commonCarrierConstructionClosedExternallyHere ≡ false
canonicalReceiptCommonCarrierConstructionClosedExternallyHereIsFalse =
  refl

canonicalReceiptCommonCarrierFeedThroughClosedHereIsFalse :
  commonCarrierFeedThroughClosedHere ≡ false
canonicalReceiptCommonCarrierFeedThroughClosedHereIsFalse =
  refl

canonicalReceiptTransferLowerBoundReadyHereIsFalse :
  transferLowerBoundReadyHere ≡ false
canonicalReceiptTransferLowerBoundReadyHereIsFalse =
  refl

canonicalReceiptTransferLowerBoundTheoremProvedHereIsFalse :
  transferLowerBoundTheoremProvedHere ≡ false
canonicalReceiptTransferLowerBoundTheoremProvedHereIsFalse =
  refl

canonicalReceiptClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalReceiptClayYangMillsPromotedIsFalse =
  refl

canonicalReducerConsumesSprint115FalseFlags :
  feed115CommonCarrierConstructionClosedExternallyInput ≡ false
canonicalReducerConsumesSprint115FalseFlags =
  refl

canonicalReducerKeepsSprint115FeedThroughClosedFalse :
  feed115CommonCarrierFeedThroughClosedInput ≡ false
canonicalReducerKeepsSprint115FeedThroughClosedFalse =
  refl

canonicalReducerKeepsSprint115TransferReadyFalse :
  feed115TransferReadyInput ≡ false
canonicalReducerKeepsSprint115TransferReadyFalse =
  refl
