module DASHI.Physics.Closure.YMSprint116ResidualConvergenceClosureReducer where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint113QuadratureResidualEstimate
  as Estimate113
import DASHI.Physics.Closure.YMSprint113InverseProjectionResidualAssembly
  as Inverse113
import DASHI.Physics.Closure.YMSprint114QuadratureResidualClosureCriterion
  as Quadrature114
import DASHI.Physics.Closure.YMSprint114InverseProjectionClosureCriterion
  as Inverse114
import DASHI.Physics.Closure.YMSprint115VanishingRateLedger
  as Ledger115
import DASHI.Physics.Closure.YMSprint115ApproximateInverseResidualCriterion
  as Approx115

------------------------------------------------------------------------
-- Sprint116 residual convergence closure reducer.
--
-- This module is deliberately conditional.  It records the supplied feeds
-- that would close the Sprint115 residual flags, and it keeps the canonical
-- Sprint115 analytic flags fail-closed when those feeds are not available as
-- DASHI-native convergence theorems.

sprintNumber : Nat
sprintNumber = 116

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint116ResidualConvergenceClosureReducer.agda"

residualConvergenceClosureReducerRecorded : Bool
residualConvergenceClosureReducerRecorded = true

conditionalReducerInhabited : Bool
conditionalReducerInhabited = true

blockedSprint115FlagsRecorded : Bool
blockedSprint115FlagsRecorded = true

externalLeftResidualVanishingClosedHere : Bool
externalLeftResidualVanishingClosedHere =
  Approx115.externalLeftResidualVanishingClosedHere

externalRightResidualVanishingClosedHere : Bool
externalRightResidualVanishingClosedHere =
  Approx115.externalRightResidualVanishingClosedHere

externalAdjointnessResidualClosedHere : Bool
externalAdjointnessResidualClosedHere =
  Approx115.externalAdjointnessResidualClosedHere

externalQuadratureResidualClosedHere : Bool
externalQuadratureResidualClosedHere =
  Approx115.externalQuadratureResidualClosedHere

renormalizedInnerProductConvergenceProvedHere : Bool
renormalizedInnerProductConvergenceProvedHere =
  Ledger115.renormalizedInnerProductConvergenceProvedHere

vanishingRateLedgerTheoremProvedHere : Bool
vanishingRateLedgerTheoremProvedHere =
  Ledger115.vanishingRateLedgerTheoremProvedHere

adjointnessResidualClosureTheoremProvedHere : Bool
adjointnessResidualClosureTheoremProvedHere =
  Ledger115.adjointnessResidualClosureTheoremProvedHere

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

leftResidualFeedText : String
leftResidualFeedText =
  "Sprint116 feed: a supplied theorem that the left E_a P_a residual vanishes on the Sprint115 admissible continuum physical comparison window."

rightResidualFeedText : String
rightResidualFeedText =
  "Sprint116 feed: a supplied theorem that the right P_a E_a residual vanishes on the Sprint115 admissible finite physical quotient window."

renormalizedInnerProductFeedText : String
renormalizedInnerProductFeedText =
  "Sprint116 feed: a supplied theorem closing the Sprint113/Sprint115 renormalized inner-product residual under the common Z(a), g(a), cell-volume, and quotient-normalization convention."

componentConvergenceFeedsText : String
componentConvergenceFeedsText =
  "Component feeds: supplied cell quadrature, smoothing approximation, holonomy sampling, and renormalized inner-product convergence on the same a-window and exponent ledger."

reducerText : String
reducerText =
  "Reducer: supplied component convergence and left/right residual feeds inhabit the Sprint115 conditional records; absent those external analytic supplies, the canonical Sprint115 false flags remain explicitly blocked."

blockedFlagsText : String
blockedFlagsText =
  "Blocked status: Sprint116 records the exact Sprint115 false flags and the missing analytic evidence instead of promoting them to true."

data ReducerLane : Set where
  sprint113-quadrature-lane :
    ReducerLane
  sprint113-inverse-lane :
    ReducerLane
  sprint114-quadrature-lane :
    ReducerLane
  sprint114-inverse-lane :
    ReducerLane
  sprint115-ledger-lane :
    ReducerLane
  sprint115-approximate-inverse-lane :
    ReducerLane
  component-convergence-feed-lane :
    ReducerLane
  renormalized-inner-product-feed-lane :
    ReducerLane
  left-residual-feed-lane :
    ReducerLane
  right-residual-feed-lane :
    ReducerLane
  residual-convergence-theorem-package-lane :
    ReducerLane
  reducer-lane :
    ReducerLane
  blocked-flag-lane :
    ReducerLane

data ReducerStatus : Set where
  imported-sprint113-quadrature :
    ReducerStatus
  imported-sprint113-inverse :
    ReducerStatus
  imported-sprint114-quadrature :
    ReducerStatus
  imported-sprint114-inverse :
    ReducerStatus
  imported-sprint115-ledger :
    ReducerStatus
  imported-sprint115-approximate-inverse :
    ReducerStatus
  supplied-component-convergence :
    ReducerStatus
  supplied-renormalized-inner-product :
    ReducerStatus
  supplied-left-residual :
    ReducerStatus
  supplied-right-residual :
    ReducerStatus
  conditional-reducer-closed :
    ReducerStatus
  external-analytic-evidence-missing :
    ReducerStatus
  fail-closed-nonpromotion :
    ReducerStatus

data ResidualFlag : Set where
  left-residual-flag :
    ResidualFlag
  right-residual-flag :
    ResidualFlag
  adjointness-residual-flag :
    ResidualFlag
  quadrature-residual-flag :
    ResidualFlag
  renormalized-inner-product-flag :
    ResidualFlag
  vanishing-rate-ledger-flag :
    ResidualFlag
  adjointness-residual-closure-flag :
    ResidualFlag

data Supplied : Bool -> Set where
  supplied :
    Supplied true

record ImportedResidualClosureSurface : Setω where
  constructor mkImportedResidualClosureSurface
  field
    sprint113QuadratureReceipt :
      Estimate113.YMSprint113QuadratureResidualEstimateReceipt
    sprint113InverseReceipt :
      Inverse113.YMSprint113InverseProjectionResidualAssemblyReceipt
    sprint114QuadratureReceipt :
      Quadrature114.YMSprint114QuadratureResidualClosureCriterionReceipt
    sprint114InverseReceipt :
      Inverse114.YMSprint114InverseProjectionClosureCriterionReceipt
    sprint115LedgerReceipt :
      Ledger115.YMSprint115VanishingRateLedgerReceipt
    sprint115ApproximateInverseReceipt :
      Approx115.YMSprint115ApproximateInverseResidualCriterionReceipt
    sprint113QuadratureRecorded :
      Bool
    sprint113InverseRecorded :
      Bool
    sprint114QuadratureRecorded :
      Bool
    sprint114InverseRecorded :
      Bool
    sprint115LedgerRecorded :
      Bool
    sprint115ApproximateInverseRecorded :
      Bool
    status :
      ReducerStatus

record ComponentConvergenceFeeds : Set where
  constructor mkComponentConvergenceFeeds
  field
    lane :
      ReducerLane
    statement :
      String
    ledgerPackage :
      Ledger115.VanishingRateSupplyPackage
    cellQuadratureFeedSupplied :
      Bool
    cellQuadratureFeedSuppliedEvidence :
      Supplied cellQuadratureFeedSupplied
    smoothingApproximationFeedSupplied :
      Bool
    smoothingApproximationFeedSuppliedEvidence :
      Supplied smoothingApproximationFeedSupplied
    holonomySamplingFeedSupplied :
      Bool
    holonomySamplingFeedSuppliedEvidence :
      Supplied holonomySamplingFeedSupplied
    renormalizedInnerProductFeedSupplied :
      Bool
    renormalizedInnerProductFeedSuppliedEvidence :
      Supplied renormalizedInnerProductFeedSupplied
    commonWindowLedgerSupplied :
      Bool
    commonWindowLedgerSuppliedEvidence :
      Supplied commonWindowLedgerSupplied
    status :
      ReducerStatus

record RenormalizedInnerProductFeed : Setω where
  constructor mkRenormalizedInnerProductFeed
  field
    lane :
      ReducerLane
    statement :
      String
    sprint113Receipt :
      Estimate113.YMSprint113QuadratureResidualEstimateReceipt
    sprint115Supply :
      Ledger115.ComponentRateSupply
    suppliedHere :
      Bool
    suppliedHereEvidence :
      Supplied suppliedHere
    sprint115TheoremFlag :
      Bool
    sprint115TheoremFlagIsFalse :
      sprint115TheoremFlag ≡ false
    status :
      ReducerStatus

record ResidualConvergenceFeed : Setω where
  constructor mkResidualConvergenceFeed
  field
    lane :
      ReducerLane
    flag :
      ResidualFlag
    statement :
      String
    sprint115ResidualSupply :
      Approx115.ResidualVanishingSupply
    suppliedHere :
      Bool
    suppliedHereEvidence :
      Supplied suppliedHere
    sprint115ExternalFlag :
      Bool
    sprint115ExternalFlagIsFalse :
      sprint115ExternalFlag ≡ false
    status :
      ReducerStatus

record ResidualConvergenceTheoremPackage : Setω where
  constructor mkResidualConvergenceTheoremPackage
  field
    lane :
      ReducerLane
    statement :
      String
    componentFeeds :
      ComponentConvergenceFeeds
    renormalizedInnerProductFeed :
      RenormalizedInnerProductFeed
    leftResidualFeed :
      ResidualConvergenceFeed
    rightResidualFeed :
      ResidualConvergenceFeed
    adjointnessFeed :
      Approx115.AdjointnessResidualFeed
    ledgerClosure :
      Ledger115.CombinedResidualClosure
    approximateInverseCriterion :
      Approx115.ApproximateInverseResidualCriterion
    allFeedsSupplied :
      Bool
    allFeedsSuppliedEvidence :
      Supplied allFeedsSupplied
    status :
      ReducerStatus

record BlockedSprint115Flag : Set where
  constructor mkBlockedSprint115Flag
  field
    lane :
      ReducerLane
    flag :
      ResidualFlag
    statement :
      String
    flagValue :
      Bool
    flagValueIsFalse :
      flagValue ≡ false
    missingEvidence :
      String
    status :
      ReducerStatus

record ResidualConvergenceClosureReducer : Setω where
  constructor mkResidualConvergenceClosureReducer
  field
    lane :
      ReducerLane
    statement :
      String
    importedSurface :
      ImportedResidualClosureSurface
    theoremPackage :
      ResidualConvergenceTheoremPackage
    reducesLedgerResidual :
      Bool
    reducesLedgerResidualEvidence :
      Supplied reducesLedgerResidual
    reducesLeftResidual :
      Bool
    reducesLeftResidualEvidence :
      Supplied reducesLeftResidual
    reducesRightResidual :
      Bool
    reducesRightResidualEvidence :
      Supplied reducesRightResidual
    reducesAdjointnessResidual :
      Bool
    reducesAdjointnessResidualEvidence :
      Supplied reducesAdjointnessResidual
    reducesQuadratureResidual :
      Bool
    reducesQuadratureResidualEvidence :
      Supplied reducesQuadratureResidual
    reducerInhabited :
      Bool
    reducerInhabitedEvidence :
      reducerInhabited ≡ true
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    status :
      ReducerStatus

record YMSprint116ResidualConvergenceClosureReducerReceipt : Setω where
  constructor mkYMSprint116ResidualConvergenceClosureReducerReceipt
  field
    sprint :
      Nat
    evidencePath :
      String
    importedSurface :
      ImportedResidualClosureSurface
    theoremPackage :
      ResidualConvergenceTheoremPackage
    reducer :
      ResidualConvergenceClosureReducer
    blockedFlags :
      List BlockedSprint115Flag
    lanes :
      List ReducerLane
    evidenceLedger :
      List String
    reducerRecorded :
      Bool
    reducerInhabitedHere :
      Bool
    blockedFlagsRecordedHere :
      Bool
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false

open ImportedResidualClosureSurface public
open ComponentConvergenceFeeds public
open RenormalizedInnerProductFeed public
open ResidualConvergenceFeed public
open ResidualConvergenceTheoremPackage public
open BlockedSprint115Flag public
open ResidualConvergenceClosureReducer public
open YMSprint116ResidualConvergenceClosureReducerReceipt public

canonicalImportedResidualClosureSurface :
  ImportedResidualClosureSurface
canonicalImportedResidualClosureSurface =
  mkImportedResidualClosureSurface
    Estimate113.canonicalReceipt
    Inverse113.canonicalReceipt
    Quadrature114.canonicalReceipt
    Inverse114.canonicalReceipt
    Ledger115.canonicalReceipt
    Approx115.canonicalReceipt
    Estimate113.quadratureResidualEstimateRecorded
    Inverse113.inverseProjectionResidualAssemblyRecorded
    Quadrature114.quadratureResidualClosureCriterionRecorded
    Inverse114.inverseProjectionClosureCriterionRecorded
    Ledger115.vanishingRateLedgerRecorded
    Approx115.approximateInverseResidualCriterionRecorded
    imported-sprint115-approximate-inverse

canonicalComponentConvergenceFeeds :
  ComponentConvergenceFeeds
canonicalComponentConvergenceFeeds =
  mkComponentConvergenceFeeds
    component-convergence-feed-lane
    componentConvergenceFeedsText
    Ledger115.suppliedVanishingRatePackage
    true
    supplied
    true
    supplied
    true
    supplied
    true
    supplied
    true
    supplied
    supplied-component-convergence

canonicalRenormalizedInnerProductFeed :
  RenormalizedInnerProductFeed
canonicalRenormalizedInnerProductFeed =
  mkRenormalizedInnerProductFeed
    renormalized-inner-product-feed-lane
    renormalizedInnerProductFeedText
    Estimate113.canonicalReceipt
    Ledger115.suppliedRenormalizedInnerProductRate
    true
    supplied
    renormalizedInnerProductConvergenceProvedHere
    refl
    supplied-renormalized-inner-product

canonicalLeftResidualFeed :
  ResidualConvergenceFeed
canonicalLeftResidualFeed =
  mkResidualConvergenceFeed
    left-residual-feed-lane
    left-residual-flag
    leftResidualFeedText
    Approx115.canonicalLeftResidualVanishingSupply
    true
    supplied
    externalLeftResidualVanishingClosedHere
    refl
    supplied-left-residual

canonicalRightResidualFeed :
  ResidualConvergenceFeed
canonicalRightResidualFeed =
  mkResidualConvergenceFeed
    right-residual-feed-lane
    right-residual-flag
    rightResidualFeedText
    Approx115.canonicalRightResidualVanishingSupply
    true
    supplied
    externalRightResidualVanishingClosedHere
    refl
    supplied-right-residual

canonicalResidualConvergenceTheoremPackage :
  ResidualConvergenceTheoremPackage
canonicalResidualConvergenceTheoremPackage =
  mkResidualConvergenceTheoremPackage
    residual-convergence-theorem-package-lane
    reducerText
    canonicalComponentConvergenceFeeds
    canonicalRenormalizedInnerProductFeed
    canonicalLeftResidualFeed
    canonicalRightResidualFeed
    Approx115.canonicalAdjointnessResidualFeed
    Ledger115.suppliedCombinedResidualClosure
    Approx115.canonicalApproximateInverseResidualCriterion
    true
    supplied
    conditional-reducer-closed

buildResidualConvergenceClosureReducer :
  ImportedResidualClosureSurface ->
  ResidualConvergenceTheoremPackage ->
  ResidualConvergenceClosureReducer
buildResidualConvergenceClosureReducer imported package =
  mkResidualConvergenceClosureReducer
    reducer-lane
    reducerText
    imported
    package
    (ResidualConvergenceTheoremPackage.allFeedsSupplied package)
    (ResidualConvergenceTheoremPackage.allFeedsSuppliedEvidence package)
    (ResidualConvergenceFeed.suppliedHere
      (ResidualConvergenceTheoremPackage.leftResidualFeed package))
    (ResidualConvergenceFeed.suppliedHereEvidence
      (ResidualConvergenceTheoremPackage.leftResidualFeed package))
    (ResidualConvergenceFeed.suppliedHere
      (ResidualConvergenceTheoremPackage.rightResidualFeed package))
    (ResidualConvergenceFeed.suppliedHereEvidence
      (ResidualConvergenceTheoremPackage.rightResidualFeed package))
    true
    supplied
    true
    supplied
    conditionalReducerInhabited
    refl
    clayYangMillsPromoted
    refl
    conditional-reducer-closed

canonicalResidualConvergenceClosureReducer :
  ResidualConvergenceClosureReducer
canonicalResidualConvergenceClosureReducer =
  buildResidualConvergenceClosureReducer
    canonicalImportedResidualClosureSurface
    canonicalResidualConvergenceTheoremPackage

blockedLeftResidualFlag : BlockedSprint115Flag
blockedLeftResidualFlag =
  mkBlockedSprint115Flag
    blocked-flag-lane
    left-residual-flag
    blockedFlagsText
    externalLeftResidualVanishingClosedHere
    refl
    "missing DASHI-native proof of left approximate-inverse residual convergence"
    external-analytic-evidence-missing

blockedRightResidualFlag : BlockedSprint115Flag
blockedRightResidualFlag =
  mkBlockedSprint115Flag
    blocked-flag-lane
    right-residual-flag
    blockedFlagsText
    externalRightResidualVanishingClosedHere
    refl
    "missing DASHI-native proof of right approximate-inverse residual convergence"
    external-analytic-evidence-missing

blockedAdjointnessResidualFlag : BlockedSprint115Flag
blockedAdjointnessResidualFlag =
  mkBlockedSprint115Flag
    blocked-flag-lane
    adjointness-residual-flag
    blockedFlagsText
    externalAdjointnessResidualClosedHere
    refl
    "missing DASHI-native proof that supplied Sprint113 component convergence closes the adjointness residual"
    external-analytic-evidence-missing

blockedQuadratureResidualFlag : BlockedSprint115Flag
blockedQuadratureResidualFlag =
  mkBlockedSprint115Flag
    blocked-flag-lane
    quadrature-residual-flag
    blockedFlagsText
    externalQuadratureResidualClosedHere
    refl
    "missing DASHI-native proof of external quadrature residual closure"
    external-analytic-evidence-missing

blockedRenormalizedInnerProductFlag : BlockedSprint115Flag
blockedRenormalizedInnerProductFlag =
  mkBlockedSprint115Flag
    blocked-flag-lane
    renormalized-inner-product-flag
    blockedFlagsText
    renormalizedInnerProductConvergenceProvedHere
    refl
    "missing DASHI-native renormalized inner-product convergence theorem"
    external-analytic-evidence-missing

blockedVanishingRateLedgerFlag : BlockedSprint115Flag
blockedVanishingRateLedgerFlag =
  mkBlockedSprint115Flag
    blocked-flag-lane
    vanishing-rate-ledger-flag
    blockedFlagsText
    vanishingRateLedgerTheoremProvedHere
    refl
    "missing DASHI-native theorem that the supplied common rate ledger follows from analytic estimates"
    external-analytic-evidence-missing

blockedAdjointnessResidualClosureFlag : BlockedSprint115Flag
blockedAdjointnessResidualClosureFlag =
  mkBlockedSprint115Flag
    blocked-flag-lane
    adjointness-residual-closure-flag
    blockedFlagsText
    adjointnessResidualClosureTheoremProvedHere
    refl
    "missing DASHI-native theorem promoting the conditional adjointness residual closure to an unconditional closure theorem"
    external-analytic-evidence-missing

canonicalBlockedFlags : List BlockedSprint115Flag
canonicalBlockedFlags =
  blockedLeftResidualFlag
  ∷ blockedRightResidualFlag
  ∷ blockedAdjointnessResidualFlag
  ∷ blockedQuadratureResidualFlag
  ∷ blockedRenormalizedInnerProductFlag
  ∷ blockedVanishingRateLedgerFlag
  ∷ blockedAdjointnessResidualClosureFlag
  ∷ []

canonicalReducerLanes : List ReducerLane
canonicalReducerLanes =
  sprint113-quadrature-lane
  ∷ sprint113-inverse-lane
  ∷ sprint114-quadrature-lane
  ∷ sprint114-inverse-lane
  ∷ sprint115-ledger-lane
  ∷ sprint115-approximate-inverse-lane
  ∷ component-convergence-feed-lane
  ∷ renormalized-inner-product-feed-lane
  ∷ left-residual-feed-lane
  ∷ right-residual-feed-lane
  ∷ residual-convergence-theorem-package-lane
  ∷ reducer-lane
  ∷ blocked-flag-lane
  ∷ []

canonicalYMSprint116ResidualConvergenceClosureReducerReceipt :
  YMSprint116ResidualConvergenceClosureReducerReceipt
canonicalYMSprint116ResidualConvergenceClosureReducerReceipt =
  mkYMSprint116ResidualConvergenceClosureReducerReceipt
    sprintNumber
    modulePath
    canonicalImportedResidualClosureSurface
    canonicalResidualConvergenceTheoremPackage
    canonicalResidualConvergenceClosureReducer
    canonicalBlockedFlags
    canonicalReducerLanes
    (leftResidualFeedText
     ∷ rightResidualFeedText
     ∷ renormalizedInnerProductFeedText
     ∷ componentConvergenceFeedsText
     ∷ reducerText
     ∷ blockedFlagsText
     ∷ [])
    residualConvergenceClosureReducerRecorded
    conditionalReducerInhabited
    blockedSprint115FlagsRecorded
    clayYangMillsPromoted
    refl

canonicalReceipt :
  YMSprint116ResidualConvergenceClosureReducerReceipt
canonicalReceipt =
  canonicalYMSprint116ResidualConvergenceClosureReducerReceipt

canonicalReducerInhabitedIsTrue :
  reducerInhabitedHere canonicalReceipt ≡ true
canonicalReducerInhabitedIsTrue =
  refl

canonicalAllFeedsSuppliedIsTrue :
  ResidualConvergenceTheoremPackage.allFeedsSupplied
    (theoremPackage canonicalReceipt) ≡ true
canonicalAllFeedsSuppliedIsTrue =
  refl

canonicalReducesLeftResidualIsTrue :
  reducesLeftResidual (reducer canonicalReceipt) ≡ true
canonicalReducesLeftResidualIsTrue =
  refl

canonicalReducesRightResidualIsTrue :
  reducesRightResidual (reducer canonicalReceipt) ≡ true
canonicalReducesRightResidualIsTrue =
  refl

canonicalReducesAdjointnessResidualIsTrue :
  reducesAdjointnessResidual (reducer canonicalReceipt) ≡ true
canonicalReducesAdjointnessResidualIsTrue =
  refl

canonicalReducesQuadratureResidualIsTrue :
  reducesQuadratureResidual (reducer canonicalReceipt) ≡ true
canonicalReducesQuadratureResidualIsTrue =
  refl

canonicalExternalLeftResidualVanishingClosedHereIsFalse :
  externalLeftResidualVanishingClosedHere ≡ false
canonicalExternalLeftResidualVanishingClosedHereIsFalse =
  refl

canonicalExternalRightResidualVanishingClosedHereIsFalse :
  externalRightResidualVanishingClosedHere ≡ false
canonicalExternalRightResidualVanishingClosedHereIsFalse =
  refl

canonicalExternalAdjointnessResidualClosedHereIsFalse :
  externalAdjointnessResidualClosedHere ≡ false
canonicalExternalAdjointnessResidualClosedHereIsFalse =
  refl

canonicalExternalQuadratureResidualClosedHereIsFalse :
  externalQuadratureResidualClosedHere ≡ false
canonicalExternalQuadratureResidualClosedHereIsFalse =
  refl

canonicalRenormalizedInnerProductConvergenceProvedHereIsFalse :
  renormalizedInnerProductConvergenceProvedHere ≡ false
canonicalRenormalizedInnerProductConvergenceProvedHereIsFalse =
  refl

canonicalVanishingRateLedgerTheoremProvedHereIsFalse :
  vanishingRateLedgerTheoremProvedHere ≡ false
canonicalVanishingRateLedgerTheoremProvedHereIsFalse =
  refl

canonicalAdjointnessResidualClosureTheoremProvedHereIsFalse :
  adjointnessResidualClosureTheoremProvedHere ≡ false
canonicalAdjointnessResidualClosureTheoremProvedHereIsFalse =
  refl

canonicalClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalClayYangMillsPromotedIsFalse =
  refl
