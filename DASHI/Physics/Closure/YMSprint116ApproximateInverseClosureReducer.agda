module DASHI.Physics.Closure.YMSprint116ApproximateInverseClosureReducer where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint114CommonCarrierEstimateClosureAssembly
  as Carrier114
import DASHI.Physics.Closure.YMSprint115ApproximateInverseResidualCriterion
  as Approx115
import DASHI.Physics.Closure.YMSprint115CommonCarrierFeedThroughCriterion
  as Feed115
import DASHI.Physics.Closure.YMSprint115VanishingRateLedger
  as Ledger115

------------------------------------------------------------------------
-- Sprint116 approximate-inverse closure reducer.
--
-- This module reduces the Sprint115 approximate-inverse residual criterion,
-- common-carrier feed-through criterion, vanishing-rate ledger, and stable
-- Sprint114 common-carrier estimate assembly into one explicit fail-closed
-- receipt.  It materially records the compatibility needed to retire false
-- flag noise around approximate inverse, common carrier, residual criterion,
-- and common-carrier estimate theorem surfaces without promoting any external
-- analytic theorem.

sprintNumber : Nat
sprintNumber = 116

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint116ApproximateInverseClosureReducer.agda"

sprint115ApproximateInverseResidualCriterionPath : String
sprint115ApproximateInverseResidualCriterionPath =
  "DASHI/Physics/Closure/YMSprint115ApproximateInverseResidualCriterion.agda"

sprint115CommonCarrierFeedThroughCriterionPath : String
sprint115CommonCarrierFeedThroughCriterionPath =
  "DASHI/Physics/Closure/YMSprint115CommonCarrierFeedThroughCriterion.agda"

sprint115VanishingRateLedgerPath : String
sprint115VanishingRateLedgerPath =
  "DASHI/Physics/Closure/YMSprint115VanishingRateLedger.agda"

sprint114CommonCarrierEstimateClosureAssemblyPath : String
sprint114CommonCarrierEstimateClosureAssemblyPath =
  "DASHI/Physics/Closure/YMSprint114CommonCarrierEstimateClosureAssembly.agda"

approximateInverseClosureReducerRecorded : Bool
approximateInverseClosureReducerRecorded = true

approximateInverseClosureInputsInhabited : Bool
approximateInverseClosureInputsInhabited = true

residualCriterionClosureInputsInhabited : Bool
residualCriterionClosureInputsInhabited = true

commonCarrierEstimateCompatibilityInhabited : Bool
commonCarrierEstimateCompatibilityInhabited = true

failClosedReducerFromSuppliedFeedsRecorded : Bool
failClosedReducerFromSuppliedFeedsRecorded = true

externalApproximateInverseClosedHere : Bool
externalApproximateInverseClosedHere = false

externalCommonCarrierClosedHere : Bool
externalCommonCarrierClosedHere = false

residualCriterionClosedHere : Bool
residualCriterionClosedHere = false

commonCarrierEstimateClosureTheoremProvedHere : Bool
commonCarrierEstimateClosureTheoremProvedHere = false

transferLowerBoundTheoremProvedHere : Bool
transferLowerBoundTheoremProvedHere = false

continuumMassGapProvedHere : Bool
continuumMassGapProvedHere = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

reducerStatementText : String
reducerStatementText =
  "Sprint116 reducer: supplied Sprint115 approximate-inverse, vanishing-rate, and common-carrier feed-through receipts are collected against the stable Sprint114 common-carrier estimate assembly; the reducer records compatibility and keeps all external analytic closure flags false."

approximateInverseInputsText : String
approximateInverseInputsText =
  "Approximate-inverse closure inputs: Sprint115 left and right residual supplies, adjointness residual feed, explicit approximate-inverse supply, and quadrature separation are present as supplied evidence, not as a new analytic closure theorem."

residualCriterionInputsText : String
residualCriterionInputsText =
  "Residual criterion closure inputs: Sprint115 vanishing-rate supplied-field implication and Sprint115 common-carrier residual criterion boundary are both consumed; residualCriterionClosedHere remains false until an external residual theorem is proved."

commonCarrierCompatibilityText : String
commonCarrierCompatibilityText =
  "Common-carrier estimate compatibility: the Sprint115 feed-through route, Sprint115 ledger boundary, and stable Sprint114 estimate assembly agree that common-carrier estimate closure is still blocked and cannot be promoted here."

failClosedReducerText : String
failClosedReducerText =
  "Fail-closed reducer: supplied feeds may inhabit the closure input records, but approximate inverse closure, common-carrier closure, residual criterion closure, common-carrier estimate theorem closure, transfer lower-bound theorem, continuum mass gap, and Clay Yang-Mills promotion remain false."

data ReducerLane : Set where
  sprint115-approximate-inverse-feed-lane :
    ReducerLane
  sprint115-common-carrier-feed-lane :
    ReducerLane
  sprint115-vanishing-rate-ledger-lane :
    ReducerLane
  sprint114-common-carrier-estimate-lane :
    ReducerLane
  approximate-inverse-closure-input-lane :
    ReducerLane
  residual-criterion-closure-input-lane :
    ReducerLane
  common-carrier-estimate-compatibility-lane :
    ReducerLane
  fail-closed-reducer-lane :
    ReducerLane
  theorem-boundary-lane :
    ReducerLane

data ReducerStatus : Set where
  imported-supplied-feed :
    ReducerStatus
  closure-input-inhabited :
    ReducerStatus
  residual-input-inhabited :
    ReducerStatus
  common-carrier-compatibility-recorded :
    ReducerStatus
  fail-closed-reduction-recorded :
    ReducerStatus
  external-analytic-theorem-blocked :
    ReducerStatus
  fail-closed-nonpromotion :
    ReducerStatus

canonicalReducerLanes : List ReducerLane
canonicalReducerLanes =
  sprint115-approximate-inverse-feed-lane
  ∷ sprint115-common-carrier-feed-lane
  ∷ sprint115-vanishing-rate-ledger-lane
  ∷ sprint114-common-carrier-estimate-lane
  ∷ approximate-inverse-closure-input-lane
  ∷ residual-criterion-closure-input-lane
  ∷ common-carrier-estimate-compatibility-lane
  ∷ fail-closed-reducer-lane
  ∷ theorem-boundary-lane
  ∷ []

record SuppliedSprintFeeds : Setω where
  constructor mkSuppliedSprintFeeds
  field
    approximateInverseReceipt :
      Approx115.YMSprint115ApproximateInverseResidualCriterionReceipt
    commonCarrierFeedThroughReceipt :
      Feed115.YMSprint115CommonCarrierFeedThroughCriterionReceipt
    vanishingRateLedgerReceipt :
      Ledger115.YMSprint115VanishingRateLedgerReceipt
    stableCommonCarrierEstimateReceipt :
      Carrier114.YMSprint114CommonCarrierEstimateClosureAssemblyReceipt
    approximateInversePath :
      String
    commonCarrierFeedThroughPath :
      String
    vanishingRateLedgerPath :
      String
    stableCommonCarrierEstimatePath :
      String
    approximateInverseFeedSupplied :
      Bool
    approximateInverseFeedSuppliedIsTrue :
      approximateInverseFeedSupplied ≡ true
    commonCarrierFeedSupplied :
      Bool
    commonCarrierFeedSuppliedIsTrue :
      commonCarrierFeedSupplied ≡ true
    vanishingRateLedgerSupplied :
      Bool
    vanishingRateLedgerSuppliedIsTrue :
      vanishingRateLedgerSupplied ≡ true
    stableCommonCarrierEstimateSupplied :
      Bool
    stableCommonCarrierEstimateSuppliedIsTrue :
      stableCommonCarrierEstimateSupplied ≡ true
    status :
      ReducerStatus

record ApproximateInverseClosureInputs : Setω where
  constructor mkApproximateInverseClosureInputs
  field
    lane :
      ReducerLane
    statement :
      String
    approximateInverseReceipt :
      Approx115.YMSprint115ApproximateInverseResidualCriterionReceipt
    leftResidualSupply :
      Approx115.ResidualVanishingSupply
    rightResidualSupply :
      Approx115.ResidualVanishingSupply
    adjointnessFeed :
      Approx115.AdjointnessResidualFeed
    approximateInverseSupply :
      Approx115.ApproximateInverseSupply
    quadratureSeparation :
      Approx115.QuadratureResidualSeparation
    criterionInhabited :
      Bool
    criterionInhabitedIsTrue :
      criterionInhabited ≡ true
    leftSupplyPresent :
      Bool
    leftSupplyPresentIsTrue :
      leftSupplyPresent ≡ true
    rightSupplyPresent :
      Bool
    rightSupplyPresentIsTrue :
      rightSupplyPresent ≡ true
    externalApproximateInverseClosed :
      Bool
    externalApproximateInverseClosedIsFalse :
      externalApproximateInverseClosed ≡ false
    status :
      ReducerStatus

record ResidualCriterionClosureInputs : Setω where
  constructor mkResidualCriterionClosureInputs
  field
    lane :
      ReducerLane
    statement :
      String
    approximateInverseReceipt :
      Approx115.YMSprint115ApproximateInverseResidualCriterionReceipt
    commonCarrierFeedThroughReceipt :
      Feed115.YMSprint115CommonCarrierFeedThroughCriterionReceipt
    vanishingRateLedgerReceipt :
      Ledger115.YMSprint115VanishingRateLedgerReceipt
    suppliedCombinedResidualClosure :
      Ledger115.CombinedResidualClosure
    normResidualSectorInputs :
      Feed115.NormResidualSectorCriterionInputs
    approximateInverseCriterionInhabited :
      Bool
    approximateInverseCriterionInhabitedIsTrue :
      approximateInverseCriterionInhabited ≡ true
    combinedResidualClosureFromSupplies :
      Bool
    combinedResidualClosureFromSuppliesIsTrue :
      combinedResidualClosureFromSupplies ≡ true
    commonCarrierResidualCriterionClosed :
      Bool
    commonCarrierResidualCriterionClosedIsFalse :
      commonCarrierResidualCriterionClosed ≡ false
    residualCriterionClosedHereFlag :
      Bool
    residualCriterionClosedHereIsFalse :
      residualCriterionClosedHereFlag ≡ false
    status :
      ReducerStatus

record CommonCarrierEstimateClosureCompatibility : Setω where
  constructor mkCommonCarrierEstimateClosureCompatibility
  field
    lane :
      ReducerLane
    statement :
      String
    commonCarrierFeedThroughReceipt :
      Feed115.YMSprint115CommonCarrierFeedThroughCriterionReceipt
    vanishingRateLedgerReceipt :
      Ledger115.YMSprint115VanishingRateLedgerReceipt
    stableCommonCarrierEstimateReceipt :
      Carrier114.YMSprint114CommonCarrierEstimateClosureAssemblyReceipt
    feedThroughRoute :
      Feed115.CommonCarrierTransferFailClosedRoute
    stableTransferRoute :
      Carrier114.TransferLowerBoundFailClosedRoute
    sprint115CommonCarrierFeedThroughClosed :
      Bool
    sprint115CommonCarrierFeedThroughClosedIsFalse :
      sprint115CommonCarrierFeedThroughClosed ≡ false
    sprint115ExternalCommonCarrierConstructionClosed :
      Bool
    sprint115ExternalCommonCarrierConstructionClosedIsFalse :
      sprint115ExternalCommonCarrierConstructionClosed ≡ false
    ledgerCommonCarrierEstimateTheoremProved :
      Bool
    ledgerCommonCarrierEstimateTheoremProvedIsFalse :
      ledgerCommonCarrierEstimateTheoremProved ≡ false
    stableCommonCarrierEstimateClosed :
      Bool
    stableCommonCarrierEstimateClosedIsFalse :
      stableCommonCarrierEstimateClosed ≡ false
    commonCarrierEstimateClosureTheoremProvedHereFlag :
      Bool
    commonCarrierEstimateClosureTheoremProvedHereIsFalse :
      commonCarrierEstimateClosureTheoremProvedHereFlag ≡ false
    externalCommonCarrierClosedHereFlag :
      Bool
    externalCommonCarrierClosedHereIsFalse :
      externalCommonCarrierClosedHereFlag ≡ false
    status :
      ReducerStatus

record FailClosedReduction : Setω where
  constructor mkFailClosedReduction
  field
    lane :
      ReducerLane
    statement :
      String
    feeds :
      SuppliedSprintFeeds
    approximateInverseInputs :
      ApproximateInverseClosureInputs
    residualCriterionInputs :
      ResidualCriterionClosureInputs
    commonCarrierEstimateCompatibility :
      CommonCarrierEstimateClosureCompatibility
    reducerRecorded :
      Bool
    approximateInverseInputsInhabitedHere :
      Bool
    residualCriterionInputsInhabitedHere :
      Bool
    commonCarrierEstimateCompatibilityInhabitedHere :
      Bool
    externalApproximateInverseClosedHereFlag :
      Bool
    externalApproximateInverseClosedHereIsFalse :
      externalApproximateInverseClosedHereFlag ≡ false
    externalCommonCarrierClosedHereFlag :
      Bool
    externalCommonCarrierClosedHereIsFalse :
      externalCommonCarrierClosedHereFlag ≡ false
    residualCriterionClosedHereFlag :
      Bool
    residualCriterionClosedHereIsFalse :
      residualCriterionClosedHereFlag ≡ false
    commonCarrierEstimateClosureTheoremProvedHereFlag :
      Bool
    commonCarrierEstimateClosureTheoremProvedHereIsFalse :
      commonCarrierEstimateClosureTheoremProvedHereFlag ≡ false
    status :
      ReducerStatus

record TheoremBoundary : Set where
  constructor mkTheoremBoundary
  field
    lane :
      ReducerLane
    statement :
      String
    externalApproximateInverseClosedHereFlag :
      Bool
    externalApproximateInverseClosedHereIsFalse :
      externalApproximateInverseClosedHereFlag ≡ false
    externalCommonCarrierClosedHereFlag :
      Bool
    externalCommonCarrierClosedHereIsFalse :
      externalCommonCarrierClosedHereFlag ≡ false
    residualCriterionClosedHereFlag :
      Bool
    residualCriterionClosedHereIsFalse :
      residualCriterionClosedHereFlag ≡ false
    commonCarrierEstimateClosureTheoremProvedHereFlag :
      Bool
    commonCarrierEstimateClosureTheoremProvedHereIsFalse :
      commonCarrierEstimateClosureTheoremProvedHereFlag ≡ false
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

record YMSprint116ApproximateInverseClosureReducerReceipt : Setω where
  constructor mkYMSprint116ApproximateInverseClosureReducerReceipt
  field
    sprint :
      Nat
    evidencePath :
      String
    suppliedFeeds :
      SuppliedSprintFeeds
    approximateInverseInputs :
      ApproximateInverseClosureInputs
    residualCriterionInputs :
      ResidualCriterionClosureInputs
    commonCarrierEstimateCompatibility :
      CommonCarrierEstimateClosureCompatibility
    failClosedReduction :
      FailClosedReduction
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

open SuppliedSprintFeeds public
open ApproximateInverseClosureInputs public
open ResidualCriterionClosureInputs public
open CommonCarrierEstimateClosureCompatibility public
open FailClosedReduction public
open TheoremBoundary public
open YMSprint116ApproximateInverseClosureReducerReceipt public

canonicalSuppliedSprintFeeds : SuppliedSprintFeeds
canonicalSuppliedSprintFeeds =
  mkSuppliedSprintFeeds
    Approx115.canonicalReceipt
    Feed115.canonicalReceipt
    Ledger115.canonicalReceipt
    Carrier114.canonicalReceipt
    sprint115ApproximateInverseResidualCriterionPath
    sprint115CommonCarrierFeedThroughCriterionPath
    sprint115VanishingRateLedgerPath
    sprint114CommonCarrierEstimateClosureAssemblyPath
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    imported-supplied-feed

approximateInverseClosureInputsFrom :
  Approx115.YMSprint115ApproximateInverseResidualCriterionReceipt ->
  ApproximateInverseClosureInputs
approximateInverseClosureInputsFrom receipt =
  mkApproximateInverseClosureInputs
    approximate-inverse-closure-input-lane
    approximateInverseInputsText
    receipt
    (Approx115.leftResidualSupply receipt)
    (Approx115.rightResidualSupply receipt)
    (Approx115.adjointnessFeed receipt)
    (Approx115.approximateInverseSupply receipt)
    (Approx115.quadratureSeparation receipt)
    approximateInverseClosureInputsInhabited
    refl
    (Approx115.ResidualVanishingSupply.supplied
      (Approx115.leftResidualSupply receipt))
    (Approx115.ResidualVanishingSupply.suppliedIsTrue
      (Approx115.leftResidualSupply receipt))
    (Approx115.ResidualVanishingSupply.supplied
      (Approx115.rightResidualSupply receipt))
    (Approx115.ResidualVanishingSupply.suppliedIsTrue
      (Approx115.rightResidualSupply receipt))
    externalApproximateInverseClosedHere
    refl
    closure-input-inhabited

residualCriterionClosureInputsFrom :
  Approx115.YMSprint115ApproximateInverseResidualCriterionReceipt ->
  Feed115.YMSprint115CommonCarrierFeedThroughCriterionReceipt ->
  Ledger115.YMSprint115VanishingRateLedgerReceipt ->
  ResidualCriterionClosureInputs
residualCriterionClosureInputsFrom approxReceipt feedReceipt ledgerReceipt =
  mkResidualCriterionClosureInputs
    residual-criterion-closure-input-lane
    residualCriterionInputsText
    approxReceipt
    feedReceipt
    ledgerReceipt
    (Ledger115.suppliedImplication ledgerReceipt)
    (Feed115.normResidualSectorInputs feedReceipt)
    approximateInverseClosureInputsInhabited
    refl
    (Ledger115.CombinedResidualClosure.adjointnessClosureSatisfiedFromSupplies
      (Ledger115.suppliedImplication ledgerReceipt))
    (Ledger115.CombinedResidualClosure.adjointnessClosureSatisfiedFromSuppliesProof
      (Ledger115.suppliedImplication ledgerReceipt))
    (Feed115.NormResidualSectorCriterionInputs.residualCriterionClosed
      (Feed115.normResidualSectorInputs feedReceipt))
    (Feed115.NormResidualSectorCriterionInputs.residualCriterionClosedIsFalse
      (Feed115.normResidualSectorInputs feedReceipt))
    residualCriterionClosedHere
    refl
    residual-input-inhabited

commonCarrierEstimateCompatibilityFrom :
  Feed115.YMSprint115CommonCarrierFeedThroughCriterionReceipt ->
  Ledger115.YMSprint115VanishingRateLedgerReceipt ->
  Carrier114.YMSprint114CommonCarrierEstimateClosureAssemblyReceipt ->
  CommonCarrierEstimateClosureCompatibility
commonCarrierEstimateCompatibilityFrom feedReceipt ledgerReceipt carrierReceipt =
  mkCommonCarrierEstimateClosureCompatibility
    common-carrier-estimate-compatibility-lane
    commonCarrierCompatibilityText
    feedReceipt
    ledgerReceipt
    carrierReceipt
    (Feed115.transferRoute feedReceipt)
    (Carrier114.transferRoute carrierReceipt)
    (Feed115.TheoremBoundary.commonCarrierFeedThroughClosedHereFlag
      (Feed115.theoremBoundary feedReceipt))
    (Feed115.TheoremBoundary.commonCarrierFeedThroughClosedHereIsFalse
      (Feed115.theoremBoundary feedReceipt))
    (Feed115.TheoremBoundary.commonCarrierConstructionClosedExternallyHereFlag
      (Feed115.theoremBoundary feedReceipt))
    (Feed115.TheoremBoundary.commonCarrierConstructionClosedExternallyHereIsFalse
      (Feed115.theoremBoundary feedReceipt))
    (Ledger115.TheoremBoundary.commonCarrierEstimateClosureTheoremProvedHereFlag
      (Ledger115.theoremBoundary ledgerReceipt))
    (Ledger115.TheoremBoundary.commonCarrierEstimateClosureTheoremProvedHereIsFalse
      (Ledger115.theoremBoundary ledgerReceipt))
    (Carrier114.TheoremBoundary.commonCarrierEstimateClosureClosedHereFlag
      (Carrier114.theoremBoundary carrierReceipt))
    (Carrier114.TheoremBoundary.commonCarrierEstimateClosureClosedHereIsFalse
      (Carrier114.theoremBoundary carrierReceipt))
    commonCarrierEstimateClosureTheoremProvedHere
    refl
    externalCommonCarrierClosedHere
    refl
    common-carrier-compatibility-recorded

failClosedReductionFrom :
  SuppliedSprintFeeds ->
  FailClosedReduction
failClosedReductionFrom feeds =
  mkFailClosedReduction
    fail-closed-reducer-lane
    failClosedReducerText
    feeds
    approximateInputs
    residualInputs
    commonCarrierCompatibility
    failClosedReducerFromSuppliedFeedsRecorded
    approximateInverseClosureInputsInhabited
    residualCriterionClosureInputsInhabited
    commonCarrierEstimateCompatibilityInhabited
    externalApproximateInverseClosedHere
    refl
    externalCommonCarrierClosedHere
    refl
    residualCriterionClosedHere
    refl
    commonCarrierEstimateClosureTheoremProvedHere
    refl
    fail-closed-reduction-recorded
  where
    approximateReceipt :
      Approx115.YMSprint115ApproximateInverseResidualCriterionReceipt
    approximateReceipt =
      SuppliedSprintFeeds.approximateInverseReceipt feeds

    feedReceipt :
      Feed115.YMSprint115CommonCarrierFeedThroughCriterionReceipt
    feedReceipt =
      SuppliedSprintFeeds.commonCarrierFeedThroughReceipt feeds

    ledgerReceipt :
      Ledger115.YMSprint115VanishingRateLedgerReceipt
    ledgerReceipt =
      SuppliedSprintFeeds.vanishingRateLedgerReceipt feeds

    carrierReceipt :
      Carrier114.YMSprint114CommonCarrierEstimateClosureAssemblyReceipt
    carrierReceipt =
      SuppliedSprintFeeds.stableCommonCarrierEstimateReceipt feeds

    approximateInputs :
      ApproximateInverseClosureInputs
    approximateInputs =
      approximateInverseClosureInputsFrom approximateReceipt

    residualInputs :
      ResidualCriterionClosureInputs
    residualInputs =
      residualCriterionClosureInputsFrom
        approximateReceipt
        feedReceipt
        ledgerReceipt

    commonCarrierCompatibility :
      CommonCarrierEstimateClosureCompatibility
    commonCarrierCompatibility =
      commonCarrierEstimateCompatibilityFrom
        feedReceipt
        ledgerReceipt
        carrierReceipt

canonicalApproximateInverseClosureInputs :
  ApproximateInverseClosureInputs
canonicalApproximateInverseClosureInputs =
  approximateInverseClosureInputsFrom Approx115.canonicalReceipt

canonicalResidualCriterionClosureInputs :
  ResidualCriterionClosureInputs
canonicalResidualCriterionClosureInputs =
  residualCriterionClosureInputsFrom
    Approx115.canonicalReceipt
    Feed115.canonicalReceipt
    Ledger115.canonicalReceipt

canonicalCommonCarrierEstimateCompatibility :
  CommonCarrierEstimateClosureCompatibility
canonicalCommonCarrierEstimateCompatibility =
  commonCarrierEstimateCompatibilityFrom
    Feed115.canonicalReceipt
    Ledger115.canonicalReceipt
    Carrier114.canonicalReceipt

canonicalFailClosedReduction : FailClosedReduction
canonicalFailClosedReduction =
  failClosedReductionFrom canonicalSuppliedSprintFeeds

canonicalTheoremBoundary : TheoremBoundary
canonicalTheoremBoundary =
  mkTheoremBoundary
    theorem-boundary-lane
    failClosedReducerText
    externalApproximateInverseClosedHere
    refl
    externalCommonCarrierClosedHere
    refl
    residualCriterionClosedHere
    refl
    commonCarrierEstimateClosureTheoremProvedHere
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
  reducerStatementText
  ∷ approximateInverseInputsText
  ∷ residualCriterionInputsText
  ∷ commonCarrierCompatibilityText
  ∷ failClosedReducerText
  ∷ sprint115ApproximateInverseResidualCriterionPath
  ∷ sprint115CommonCarrierFeedThroughCriterionPath
  ∷ sprint115VanishingRateLedgerPath
  ∷ sprint114CommonCarrierEstimateClosureAssemblyPath
  ∷ []

canonicalYMSprint116ApproximateInverseClosureReducerReceipt :
  YMSprint116ApproximateInverseClosureReducerReceipt
canonicalYMSprint116ApproximateInverseClosureReducerReceipt =
  mkYMSprint116ApproximateInverseClosureReducerReceipt
    sprintNumber
    modulePath
    canonicalSuppliedSprintFeeds
    canonicalApproximateInverseClosureInputs
    canonicalResidualCriterionClosureInputs
    canonicalCommonCarrierEstimateCompatibility
    canonicalFailClosedReduction
    canonicalTheoremBoundary
    canonicalReducerLanes
    canonicalEvidenceLedger
    approximateInverseClosureReducerRecorded
    clayYangMillsPromoted
    refl

canonicalReceipt :
  YMSprint116ApproximateInverseClosureReducerReceipt
canonicalReceipt =
  canonicalYMSprint116ApproximateInverseClosureReducerReceipt

canonicalExternalApproximateInverseClosedHereIsFalse :
  TheoremBoundary.externalApproximateInverseClosedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalExternalApproximateInverseClosedHereIsFalse =
  refl

canonicalExternalCommonCarrierClosedHereIsFalse :
  TheoremBoundary.externalCommonCarrierClosedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalExternalCommonCarrierClosedHereIsFalse =
  refl

canonicalResidualCriterionClosedHereIsFalse :
  TheoremBoundary.residualCriterionClosedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalResidualCriterionClosedHereIsFalse =
  refl

canonicalCommonCarrierEstimateClosureTheoremProvedHereIsFalse :
  TheoremBoundary.commonCarrierEstimateClosureTheoremProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalCommonCarrierEstimateClosureTheoremProvedHereIsFalse =
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
