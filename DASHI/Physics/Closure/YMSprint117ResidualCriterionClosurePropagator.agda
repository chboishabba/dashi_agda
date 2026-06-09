module DASHI.Physics.Closure.YMSprint117ResidualCriterionClosurePropagator where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint115CommonCarrierFeedThroughCriterion
  as Feed115
import DASHI.Physics.Closure.YMSprint116ApproximateInverseClosureReducer
  as Approx116
import DASHI.Physics.Closure.YMSprint116ResidualConvergenceClosureReducer
  as Residual116

------------------------------------------------------------------------
-- Sprint117 residual criterion closure propagator.
--
-- This module is a propagation receipt.  It consumes the Sprint116 residual
-- convergence reducer and the Sprint116 approximate-inverse reducer, then
-- ties their supplied residual facts to the Sprint115 common-carrier
-- feed-through residual criterion surface.  The local feed flag is allowed to
-- be true because it records the propagation package itself.  It does not
-- promote any external analytic theorem.

sprintNumber : Nat
sprintNumber = 117

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint117ResidualCriterionClosurePropagator.agda"

sprint116ResidualConvergenceClosureReducerPath : String
sprint116ResidualConvergenceClosureReducerPath =
  "DASHI/Physics/Closure/YMSprint116ResidualConvergenceClosureReducer.agda"

sprint116ApproximateInverseClosureReducerPath : String
sprint116ApproximateInverseClosureReducerPath =
  "DASHI/Physics/Closure/YMSprint116ApproximateInverseClosureReducer.agda"

sprint115CommonCarrierFeedThroughCriterionPath : String
sprint115CommonCarrierFeedThroughCriterionPath =
  "DASHI/Physics/Closure/YMSprint115CommonCarrierFeedThroughCriterion.agda"

residualCriterionClosurePropagatorRecorded : Bool
residualCriterionClosurePropagatorRecorded = true

residualCriterionFeedClosedHere : Bool
residualCriterionFeedClosedHere = true

externalLeftResidualVanishingClosedHere : Bool
externalLeftResidualVanishingClosedHere = false

externalRightResidualVanishingClosedHere : Bool
externalRightResidualVanishingClosedHere = false

externalAdjointnessResidualClosedHere : Bool
externalAdjointnessResidualClosedHere = false

externalQuadratureResidualClosedHere : Bool
externalQuadratureResidualClosedHere = false

renormalizedInnerProductConvergenceProvedHere : Bool
renormalizedInnerProductConvergenceProvedHere = false

vanishingRateLedgerTheoremProvedHere : Bool
vanishingRateLedgerTheoremProvedHere = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

sourceLedgerText : String
sourceLedgerText =
  "Sprint117 sources: canonical Sprint116 residual convergence reducer, canonical Sprint116 approximate-inverse closure reducer, and canonical Sprint115 common-carrier feed-through criterion."

residualReducerFeedText : String
residualReducerFeedText =
  "Residual reducer feed: Sprint116 records left, right, adjointness, quadrature, and renormalized inner-product residual feeds as supplied propagation facts while its external theorem flags remain false."

approximateInverseReducerFeedText : String
approximateInverseReducerFeedText =
  "Approximate-inverse reducer feed: Sprint116 records residual criterion inputs from the Sprint115 approximate-inverse receipt, the Sprint115 vanishing-rate ledger, and the Sprint115 common-carrier feed-through criterion while residualCriterionClosedHere remains false."

commonCarrierFeedText : String
commonCarrierFeedText =
  "Common-carrier feed surface: Sprint115 records norm, residual, and sector criteria as required inputs; the residual criterion is still false as an external theorem."

propagationStatementText : String
propagationStatementText =
  "Sprint117 propagation: supplied residual reducer facts and supplied approximate-inverse reducer facts are packaged into an explicit residual criterion feed record; the local feed flag is true only for this propagation receipt."

theoremBoundaryText : String
theoremBoundaryText =
  "Theorem boundary: Sprint117 does not close left residual vanishing, right residual vanishing, adjointness residual, quadrature residual, renormalized inner-product convergence, vanishing-rate ledger theorem, transfer lower bound, continuum mass gap, or Clay Yang-Mills promotion."

finalReceiptText : String
finalReceiptText =
  "Final receipt: residualCriterionFeedClosedHere=true as a feed/progagation record; all requested external theorem and promotion flags remain false."

data PropagatorLane : Set where
  sprint116-residual-reducer-source-lane :
    PropagatorLane
  sprint116-approximate-inverse-reducer-source-lane :
    PropagatorLane
  sprint115-common-carrier-feed-source-lane :
    PropagatorLane
  residual-reducer-facts-lane :
    PropagatorLane
  approximate-inverse-reducer-facts-lane :
    PropagatorLane
  common-carrier-residual-boundary-lane :
    PropagatorLane
  residual-criterion-feed-propagation-lane :
    PropagatorLane
  theorem-boundary-lane :
    PropagatorLane
  final-receipt-lane :
    PropagatorLane

data PropagatorStatus : Set where
  imported-stable-source :
    PropagatorStatus
  source-path-recorded :
    PropagatorStatus
  reducer-feed-recorded :
    PropagatorStatus
  approximate-inverse-feed-recorded :
    PropagatorStatus
  common-carrier-boundary-recorded :
    PropagatorStatus
  propagation-feed-closed :
    PropagatorStatus
  external-theorem-left-open :
    PropagatorStatus
  fail-closed-nonpromotion :
    PropagatorStatus
  receipt-finalized :
    PropagatorStatus

data BoundaryFlag : Set where
  residual-criterion-feed-flag :
    BoundaryFlag
  external-left-residual-flag :
    BoundaryFlag
  external-right-residual-flag :
    BoundaryFlag
  external-adjointness-residual-flag :
    BoundaryFlag
  external-quadrature-residual-flag :
    BoundaryFlag
  renormalized-inner-product-flag :
    BoundaryFlag
  vanishing-rate-ledger-flag :
    BoundaryFlag
  clay-yang-mills-promotion-flag :
    BoundaryFlag

canonicalPropagatorLanes : List PropagatorLane
canonicalPropagatorLanes =
  sprint116-residual-reducer-source-lane
  ∷ sprint116-approximate-inverse-reducer-source-lane
  ∷ sprint115-common-carrier-feed-source-lane
  ∷ residual-reducer-facts-lane
  ∷ approximate-inverse-reducer-facts-lane
  ∷ common-carrier-residual-boundary-lane
  ∷ residual-criterion-feed-propagation-lane
  ∷ theorem-boundary-lane
  ∷ final-receipt-lane
  ∷ []

record Sprint117SourcePaths : Set where
  constructor mkSprint117SourcePaths
  field
    lane :
      PropagatorLane
    residualReducerPath :
      String
    approximateInverseReducerPath :
      String
    commonCarrierFeedPath :
      String
    currentModulePath :
      String
    sourceLedger :
      String
    residualReducerImported :
      Bool
    residualReducerImportedIsTrue :
      residualReducerImported ≡ true
    approximateInverseReducerImported :
      Bool
    approximateInverseReducerImportedIsTrue :
      approximateInverseReducerImported ≡ true
    commonCarrierFeedImported :
      Bool
    commonCarrierFeedImportedIsTrue :
      commonCarrierFeedImported ≡ true
    status :
      PropagatorStatus

record ResidualReducerFacts : Setω where
  constructor mkResidualReducerFacts
  field
    lane :
      PropagatorLane
    statement :
      String
    residualReducerReceipt :
      Residual116.YMSprint116ResidualConvergenceClosureReducerReceipt
    theoremPackage :
      Residual116.ResidualConvergenceTheoremPackage
    reducer :
      Residual116.ResidualConvergenceClosureReducer
    blockedFlags :
      List Residual116.BlockedSprint115Flag
    allFeedsSupplied :
      Bool
    allFeedsSuppliedIsTrue :
      allFeedsSupplied ≡ true
    reducesLeftResidual :
      Bool
    reducesLeftResidualIsTrue :
      reducesLeftResidual ≡ true
    reducesRightResidual :
      Bool
    reducesRightResidualIsTrue :
      reducesRightResidual ≡ true
    reducesAdjointnessResidual :
      Bool
    reducesAdjointnessResidualIsTrue :
      reducesAdjointnessResidual ≡ true
    reducesQuadratureResidual :
      Bool
    reducesQuadratureResidualIsTrue :
      reducesQuadratureResidual ≡ true
    importedExternalLeftFlag :
      Bool
    importedExternalLeftFlagIsFalse :
      importedExternalLeftFlag ≡ false
    importedExternalRightFlag :
      Bool
    importedExternalRightFlagIsFalse :
      importedExternalRightFlag ≡ false
    importedExternalAdjointnessFlag :
      Bool
    importedExternalAdjointnessFlagIsFalse :
      importedExternalAdjointnessFlag ≡ false
    importedExternalQuadratureFlag :
      Bool
    importedExternalQuadratureFlagIsFalse :
      importedExternalQuadratureFlag ≡ false
    importedRenormalizedInnerProductFlag :
      Bool
    importedRenormalizedInnerProductFlagIsFalse :
      importedRenormalizedInnerProductFlag ≡ false
    importedVanishingRateLedgerFlag :
      Bool
    importedVanishingRateLedgerFlagIsFalse :
      importedVanishingRateLedgerFlag ≡ false
    importedClayYangMillsFlag :
      Bool
    importedClayYangMillsFlagIsFalse :
      importedClayYangMillsFlag ≡ false
    status :
      PropagatorStatus

record ApproximateInverseReducerFacts : Setω where
  constructor mkApproximateInverseReducerFacts
  field
    lane :
      PropagatorLane
    statement :
      String
    approximateInverseReducerReceipt :
      Approx116.YMSprint116ApproximateInverseClosureReducerReceipt
    approximateInverseInputs :
      Approx116.ApproximateInverseClosureInputs
    residualCriterionInputs :
      Approx116.ResidualCriterionClosureInputs
    failClosedReduction :
      Approx116.FailClosedReduction
    theoremBoundary :
      Approx116.TheoremBoundary
    approximateInverseInputsInhabited :
      Bool
    approximateInverseInputsInhabitedIsTrue :
      approximateInverseInputsInhabited ≡ true
    residualCriterionInputsInhabited :
      Bool
    residualCriterionInputsInhabitedIsTrue :
      residualCriterionInputsInhabited ≡ true
    residualCriterionClosedFlag :
      Bool
    residualCriterionClosedFlagIsFalse :
      residualCriterionClosedFlag ≡ false
    approximateInverseExternalFlag :
      Bool
    approximateInverseExternalFlagIsFalse :
      approximateInverseExternalFlag ≡ false
    approximateInverseClayFlag :
      Bool
    approximateInverseClayFlagIsFalse :
      approximateInverseClayFlag ≡ false
    status :
      PropagatorStatus

record CommonCarrierResidualBoundary : Setω where
  constructor mkCommonCarrierResidualBoundary
  field
    lane :
      PropagatorLane
    statement :
      String
    commonCarrierFeedReceipt :
      Feed115.YMSprint115CommonCarrierFeedThroughCriterionReceipt
    normResidualSectorInputs :
      Feed115.NormResidualSectorCriterionInputs
    theoremBoundary :
      Feed115.TheoremBoundary
    normCriterionClosed :
      Bool
    normCriterionClosedIsFalse :
      normCriterionClosed ≡ false
    residualCriterionClosed :
      Bool
    residualCriterionClosedIsFalse :
      residualCriterionClosed ≡ false
    sectorCriterionClosed :
      Bool
    sectorCriterionClosedIsFalse :
      sectorCriterionClosed ≡ false
    commonCarrierFeedThroughClosed :
      Bool
    commonCarrierFeedThroughClosedIsFalse :
      commonCarrierFeedThroughClosed ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    status :
      PropagatorStatus

record ResidualCriterionFeedPropagation : Setω where
  constructor mkResidualCriterionFeedPropagation
  field
    lane :
      PropagatorLane
    statement :
      String
    residualFacts :
      ResidualReducerFacts
    approximateInverseFacts :
      ApproximateInverseReducerFacts
    commonCarrierBoundary :
      CommonCarrierResidualBoundary
    feedFlag :
      Bool
    feedFlagIsTrue :
      feedFlag ≡ true
    residualReducerFeedsConsumed :
      Bool
    residualReducerFeedsConsumedIsTrue :
      residualReducerFeedsConsumed ≡ true
    approximateInverseReducerInputsConsumed :
      Bool
    approximateInverseReducerInputsConsumedIsTrue :
      approximateInverseReducerInputsConsumed ≡ true
    commonCarrierBoundaryConsumed :
      Bool
    commonCarrierBoundaryConsumedIsTrue :
      commonCarrierBoundaryConsumed ≡ true
    externalTheoremClosureClaimed :
      Bool
    externalTheoremClosureClaimedIsFalse :
      externalTheoremClosureClaimed ≡ false
    clayPromotionClaimed :
      Bool
    clayPromotionClaimedIsFalse :
      clayPromotionClaimed ≡ false
    status :
      PropagatorStatus

record FlagBoundaryReceipt : Set where
  constructor mkFlagBoundaryReceipt
  field
    lane :
      PropagatorLane
    flag :
      BoundaryFlag
    statement :
      String
    flagValue :
      Bool
    flagValueIsFalse :
      flagValue ≡ false
    evidenceSource :
      String
    status :
      PropagatorStatus

record TheoremBoundary : Set where
  constructor mkTheoremBoundary
  field
    lane :
      PropagatorLane
    statement :
      String
    boundaryFlags :
      List FlagBoundaryReceipt
    externalLeftResidualVanishingClosedHereFlag :
      Bool
    externalLeftResidualVanishingClosedHereIsFalse :
      externalLeftResidualVanishingClosedHereFlag ≡ false
    externalRightResidualVanishingClosedHereFlag :
      Bool
    externalRightResidualVanishingClosedHereIsFalse :
      externalRightResidualVanishingClosedHereFlag ≡ false
    externalAdjointnessResidualClosedHereFlag :
      Bool
    externalAdjointnessResidualClosedHereIsFalse :
      externalAdjointnessResidualClosedHereFlag ≡ false
    externalQuadratureResidualClosedHereFlag :
      Bool
    externalQuadratureResidualClosedHereIsFalse :
      externalQuadratureResidualClosedHereFlag ≡ false
    renormalizedInnerProductConvergenceProvedHereFlag :
      Bool
    renormalizedInnerProductConvergenceProvedHereIsFalse :
      renormalizedInnerProductConvergenceProvedHereFlag ≡ false
    vanishingRateLedgerTheoremProvedHereFlag :
      Bool
    vanishingRateLedgerTheoremProvedHereIsFalse :
      vanishingRateLedgerTheoremProvedHereFlag ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    status :
      PropagatorStatus

record FinalReceipt : Setω where
  constructor mkFinalReceipt
  field
    lane :
      PropagatorLane
    statement :
      String
    propagation :
      ResidualCriterionFeedPropagation
    theoremBoundary :
      TheoremBoundary
    receiptRecorded :
      Bool
    receiptRecordedIsTrue :
      receiptRecorded ≡ true
    feedClosedHere :
      Bool
    feedClosedHereIsTrue :
      feedClosedHere ≡ true
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    status :
      PropagatorStatus

record YMSprint117ResidualCriterionClosurePropagatorReceipt : Setω where
  constructor mkYMSprint117ResidualCriterionClosurePropagatorReceipt
  field
    sprint :
      Nat
    evidencePath :
      String
    sourcePaths :
      Sprint117SourcePaths
    residualReducerFacts :
      ResidualReducerFacts
    approximateInverseReducerFacts :
      ApproximateInverseReducerFacts
    commonCarrierResidualBoundary :
      CommonCarrierResidualBoundary
    propagation :
      ResidualCriterionFeedPropagation
    theoremBoundary :
      TheoremBoundary
    finalReceipt :
      FinalReceipt
    lanes :
      List PropagatorLane
    evidenceLedger :
      List String
    receiptRecorded :
      Bool
    residualCriterionFeedClosedHereFlag :
      Bool
    residualCriterionFeedClosedHereIsTrue :
      residualCriterionFeedClosedHereFlag ≡ true
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false

open Sprint117SourcePaths public
open ResidualReducerFacts public
open ApproximateInverseReducerFacts public
open CommonCarrierResidualBoundary public
open ResidualCriterionFeedPropagation public
open FlagBoundaryReceipt public
open TheoremBoundary public
open FinalReceipt public
open YMSprint117ResidualCriterionClosurePropagatorReceipt public

canonicalSourcePaths : Sprint117SourcePaths
canonicalSourcePaths =
  mkSprint117SourcePaths
    sprint116-residual-reducer-source-lane
    sprint116ResidualConvergenceClosureReducerPath
    sprint116ApproximateInverseClosureReducerPath
    sprint115CommonCarrierFeedThroughCriterionPath
    modulePath
    sourceLedgerText
    true
    refl
    true
    refl
    true
    refl
    source-path-recorded

canonicalResidualReducerFacts : ResidualReducerFacts
canonicalResidualReducerFacts =
  mkResidualReducerFacts
    residual-reducer-facts-lane
    residualReducerFeedText
    Residual116.canonicalReceipt
    (Residual116.theoremPackage Residual116.canonicalReceipt)
    (Residual116.reducer Residual116.canonicalReceipt)
    (Residual116.blockedFlags Residual116.canonicalReceipt)
    (Residual116.ResidualConvergenceTheoremPackage.allFeedsSupplied
      (Residual116.theoremPackage Residual116.canonicalReceipt))
    refl
    (Residual116.reducesLeftResidual
      (Residual116.reducer Residual116.canonicalReceipt))
    refl
    (Residual116.reducesRightResidual
      (Residual116.reducer Residual116.canonicalReceipt))
    refl
    (Residual116.reducesAdjointnessResidual
      (Residual116.reducer Residual116.canonicalReceipt))
    refl
    (Residual116.reducesQuadratureResidual
      (Residual116.reducer Residual116.canonicalReceipt))
    refl
    Residual116.externalLeftResidualVanishingClosedHere
    refl
    Residual116.externalRightResidualVanishingClosedHere
    refl
    Residual116.externalAdjointnessResidualClosedHere
    refl
    Residual116.externalQuadratureResidualClosedHere
    refl
    Residual116.renormalizedInnerProductConvergenceProvedHere
    refl
    Residual116.vanishingRateLedgerTheoremProvedHere
    refl
    Residual116.clayYangMillsPromoted
    refl
    reducer-feed-recorded

canonicalApproximateInverseReducerFacts : ApproximateInverseReducerFacts
canonicalApproximateInverseReducerFacts =
  mkApproximateInverseReducerFacts
    approximate-inverse-reducer-facts-lane
    approximateInverseReducerFeedText
    Approx116.canonicalReceipt
    (Approx116.approximateInverseInputs Approx116.canonicalReceipt)
    (Approx116.residualCriterionInputs Approx116.canonicalReceipt)
    (Approx116.failClosedReduction Approx116.canonicalReceipt)
    (Approx116.theoremBoundary Approx116.canonicalReceipt)
    Approx116.approximateInverseClosureInputsInhabited
    refl
    Approx116.residualCriterionClosureInputsInhabited
    refl
    (Approx116.TheoremBoundary.residualCriterionClosedHereFlag
      (Approx116.theoremBoundary Approx116.canonicalReceipt))
    refl
    (Approx116.TheoremBoundary.externalApproximateInverseClosedHereFlag
      (Approx116.theoremBoundary Approx116.canonicalReceipt))
    refl
    (Approx116.clayYangMillsPromotedHere Approx116.canonicalReceipt)
    refl
    approximate-inverse-feed-recorded

canonicalCommonCarrierResidualBoundary : CommonCarrierResidualBoundary
canonicalCommonCarrierResidualBoundary =
  mkCommonCarrierResidualBoundary
    common-carrier-residual-boundary-lane
    commonCarrierFeedText
    Feed115.canonicalReceipt
    (Feed115.normResidualSectorInputs Feed115.canonicalReceipt)
    (Feed115.theoremBoundary Feed115.canonicalReceipt)
    (Feed115.NormResidualSectorCriterionInputs.normCriterionClosed
      (Feed115.normResidualSectorInputs Feed115.canonicalReceipt))
    (Feed115.NormResidualSectorCriterionInputs.normCriterionClosedIsFalse
      (Feed115.normResidualSectorInputs Feed115.canonicalReceipt))
    (Feed115.NormResidualSectorCriterionInputs.residualCriterionClosed
      (Feed115.normResidualSectorInputs Feed115.canonicalReceipt))
    (Feed115.NormResidualSectorCriterionInputs.residualCriterionClosedIsFalse
      (Feed115.normResidualSectorInputs Feed115.canonicalReceipt))
    (Feed115.NormResidualSectorCriterionInputs.sectorCriterionClosed
      (Feed115.normResidualSectorInputs Feed115.canonicalReceipt))
    (Feed115.NormResidualSectorCriterionInputs.sectorCriterionClosedIsFalse
      (Feed115.normResidualSectorInputs Feed115.canonicalReceipt))
    (Feed115.TheoremBoundary.commonCarrierFeedThroughClosedHereFlag
      (Feed115.theoremBoundary Feed115.canonicalReceipt))
    (Feed115.TheoremBoundary.commonCarrierFeedThroughClosedHereIsFalse
      (Feed115.theoremBoundary Feed115.canonicalReceipt))
    (Feed115.clayYangMillsPromotedHere Feed115.canonicalReceipt)
    refl
    common-carrier-boundary-recorded

canonicalResidualCriterionFeedPropagation :
  ResidualCriterionFeedPropagation
canonicalResidualCriterionFeedPropagation =
  mkResidualCriterionFeedPropagation
    residual-criterion-feed-propagation-lane
    propagationStatementText
    canonicalResidualReducerFacts
    canonicalApproximateInverseReducerFacts
    canonicalCommonCarrierResidualBoundary
    residualCriterionFeedClosedHere
    refl
    (ResidualReducerFacts.allFeedsSupplied canonicalResidualReducerFacts)
    (ResidualReducerFacts.allFeedsSuppliedIsTrue canonicalResidualReducerFacts)
    (ApproximateInverseReducerFacts.residualCriterionInputsInhabited
      canonicalApproximateInverseReducerFacts)
    (ApproximateInverseReducerFacts.residualCriterionInputsInhabitedIsTrue
      canonicalApproximateInverseReducerFacts)
    true
    refl
    false
    refl
    clayYangMillsPromoted
    refl
    propagation-feed-closed

canonicalBoundaryFlags : List FlagBoundaryReceipt
canonicalBoundaryFlags =
  mkFlagBoundaryReceipt
    theorem-boundary-lane
    external-left-residual-flag
    theoremBoundaryText
    externalLeftResidualVanishingClosedHere
    refl
    sprint116ResidualConvergenceClosureReducerPath
    external-theorem-left-open
  ∷ mkFlagBoundaryReceipt
    theorem-boundary-lane
    external-right-residual-flag
    theoremBoundaryText
    externalRightResidualVanishingClosedHere
    refl
    sprint116ResidualConvergenceClosureReducerPath
    external-theorem-left-open
  ∷ mkFlagBoundaryReceipt
    theorem-boundary-lane
    external-adjointness-residual-flag
    theoremBoundaryText
    externalAdjointnessResidualClosedHere
    refl
    sprint116ResidualConvergenceClosureReducerPath
    external-theorem-left-open
  ∷ mkFlagBoundaryReceipt
    theorem-boundary-lane
    external-quadrature-residual-flag
    theoremBoundaryText
    externalQuadratureResidualClosedHere
    refl
    sprint116ResidualConvergenceClosureReducerPath
    external-theorem-left-open
  ∷ mkFlagBoundaryReceipt
    theorem-boundary-lane
    renormalized-inner-product-flag
    theoremBoundaryText
    renormalizedInnerProductConvergenceProvedHere
    refl
    sprint116ResidualConvergenceClosureReducerPath
    external-theorem-left-open
  ∷ mkFlagBoundaryReceipt
    theorem-boundary-lane
    vanishing-rate-ledger-flag
    theoremBoundaryText
    vanishingRateLedgerTheoremProvedHere
    refl
    sprint116ResidualConvergenceClosureReducerPath
    external-theorem-left-open
  ∷ mkFlagBoundaryReceipt
    theorem-boundary-lane
    clay-yang-mills-promotion-flag
    theoremBoundaryText
    clayYangMillsPromoted
    refl
    modulePath
    fail-closed-nonpromotion
  ∷ []

canonicalTheoremBoundary : TheoremBoundary
canonicalTheoremBoundary =
  mkTheoremBoundary
    theorem-boundary-lane
    theoremBoundaryText
    canonicalBoundaryFlags
    externalLeftResidualVanishingClosedHere
    refl
    externalRightResidualVanishingClosedHere
    refl
    externalAdjointnessResidualClosedHere
    refl
    externalQuadratureResidualClosedHere
    refl
    renormalizedInnerProductConvergenceProvedHere
    refl
    vanishingRateLedgerTheoremProvedHere
    refl
    clayYangMillsPromoted
    refl
    fail-closed-nonpromotion

canonicalFinalReceipt : FinalReceipt
canonicalFinalReceipt =
  mkFinalReceipt
    final-receipt-lane
    finalReceiptText
    canonicalResidualCriterionFeedPropagation
    canonicalTheoremBoundary
    residualCriterionClosurePropagatorRecorded
    refl
    residualCriterionFeedClosedHere
    refl
    clayYangMillsPromoted
    refl
    receipt-finalized

canonicalEvidenceLedger : List String
canonicalEvidenceLedger =
  sourceLedgerText
  ∷ residualReducerFeedText
  ∷ approximateInverseReducerFeedText
  ∷ commonCarrierFeedText
  ∷ propagationStatementText
  ∷ theoremBoundaryText
  ∷ finalReceiptText
  ∷ sprint116ResidualConvergenceClosureReducerPath
  ∷ sprint116ApproximateInverseClosureReducerPath
  ∷ sprint115CommonCarrierFeedThroughCriterionPath
  ∷ modulePath
  ∷ []

canonicalYMSprint117ResidualCriterionClosurePropagatorReceipt :
  YMSprint117ResidualCriterionClosurePropagatorReceipt
canonicalYMSprint117ResidualCriterionClosurePropagatorReceipt =
  mkYMSprint117ResidualCriterionClosurePropagatorReceipt
    sprintNumber
    modulePath
    canonicalSourcePaths
    canonicalResidualReducerFacts
    canonicalApproximateInverseReducerFacts
    canonicalCommonCarrierResidualBoundary
    canonicalResidualCriterionFeedPropagation
    canonicalTheoremBoundary
    canonicalFinalReceipt
    canonicalPropagatorLanes
    canonicalEvidenceLedger
    residualCriterionClosurePropagatorRecorded
    residualCriterionFeedClosedHere
    refl
    clayYangMillsPromoted
    refl

canonicalReceipt :
  YMSprint117ResidualCriterionClosurePropagatorReceipt
canonicalReceipt =
  canonicalYMSprint117ResidualCriterionClosurePropagatorReceipt

canonicalResidualCriterionFeedClosedHereIsTrue :
  residualCriterionFeedClosedHereFlag canonicalReceipt ≡ true
canonicalResidualCriterionFeedClosedHereIsTrue =
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

canonicalClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalClayYangMillsPromotedIsFalse =
  refl

canonicalFinalReceiptFeedClosedHereIsTrue :
  FinalReceipt.feedClosedHere canonicalFinalReceipt ≡ true
canonicalFinalReceiptFeedClosedHereIsTrue =
  refl

canonicalTheoremBoundaryKeepsClayFalse :
  TheoremBoundary.clayYangMillsPromotedHere canonicalTheoremBoundary ≡ false
canonicalTheoremBoundaryKeepsClayFalse =
  refl
