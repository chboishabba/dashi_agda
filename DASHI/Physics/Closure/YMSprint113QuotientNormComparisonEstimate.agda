module DASHI.Physics.Closure.YMSprint113QuotientNormComparisonEstimate where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint112UniformNormBoundReduction
  as Uniform112
import DASHI.Physics.Closure.YMSprint112QuotientIndependenceDiagramLedger
  as Quotient112

------------------------------------------------------------------------
-- Sprint113 quotient norm comparison estimate package.
--
-- This module records the exact package needed by the Sprint112 quotient
-- norm comparison lane: orbit infimum comparison, physical projection
-- contraction, representative-independence feed, finite/continuum quotient
-- descent, and fail-closed blockers.  It is a populated ledger.  No
-- analytic estimate, quotient-descent theorem, representative-independence
-- theorem, or Clay Yang-Mills promotion is proved here.

quotientNormComparisonEstimateRecorded : Bool
quotientNormComparisonEstimateRecorded = true

orbitInfimumComparisonRecorded : Bool
orbitInfimumComparisonRecorded = true

physicalProjectionContractionRecorded : Bool
physicalProjectionContractionRecorded = true

representativeIndependenceFeedRecorded : Bool
representativeIndependenceFeedRecorded = true

finiteQuotientDescentRecorded : Bool
finiteQuotientDescentRecorded = true

continuumQuotientDescentRecorded : Bool
continuumQuotientDescentRecorded = true

exactFailClosedBlockersRecorded : Bool
exactFailClosedBlockersRecorded = true

orbitInfimumComparisonProvedHere : Bool
orbitInfimumComparisonProvedHere = false

physicalProjectionContractionProvedHere : Bool
physicalProjectionContractionProvedHere = false

representativeIndependenceFeedClosedHere : Bool
representativeIndependenceFeedClosedHere = false

finiteQuotientDescentProvedHere : Bool
finiteQuotientDescentProvedHere = false

continuumQuotientDescentProvedHere : Bool
continuumQuotientDescentProvedHere = false

quotientNormComparisonEstimateClosedHere : Bool
quotientNormComparisonEstimateClosedHere = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

sprintNumber : Nat
sprintNumber = 113

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint113QuotientNormComparisonEstimate.agda"

uniform112ReceiptImported : Bool
uniform112ReceiptImported =
  Uniform112.uniformNormBoundReductionRecorded

quotient112ReceiptImported : Bool
quotient112ReceiptImported =
  Quotient112.quotientDiagramLedgerRecorded

orbitInfimumComparisonText : String
orbitInfimumComparisonText =
  "Orbit infimum comparison package: compare the finite quotient seminorm infimum over finite gauge orbits with the continuum physical-carrier norm after E_a/P_a, using one cutoff-independent comparison constant C_quot."

physicalProjectionContractionText : String
physicalProjectionContractionText =
  "Physical projection contraction package: record the needed estimate that Pi_a,phys and Pi_phys do not enlarge the quotient norm contribution before and after the finite/continuum comparison maps."

representativeIndependenceFeedText : String
representativeIndependenceFeedText =
  "Representative-independence feed: consume the Sprint112 quotient-independence diagram ledger as an input requirement for choosing orbit representatives without changing quotient norm values."

finiteQuotientDescentText : String
finiteQuotientDescentText =
  "Finite quotient descent package: require the finite E_a-side comparison to factor through [A_a] and the finite physical quotient norm, independent of the chosen finite gauge representative."

continuumQuotientDescentText : String
continuumQuotientDescentText =
  "Continuum quotient descent package: require the P_a-side comparison to factor through [A] and the continuum physical quotient carrier, independent of the chosen continuum gauge representative."

failClosedBlockersText : String
failClosedBlockersText =
  "Exact fail-closed blockers: no orbit infimum minimizer/approximating-net theorem, no projection contraction estimate, no representative-independence closure, and no finite/continuum quotient descent theorem are proved in this module."

nonPromotionBoundaryText : String
nonPromotionBoundaryText =
  "Sprint113 records the quotient norm comparison estimate package only; it does not close the Sprint112 uniform norm bound reduction, norm equivalence, weak compactness feed, mass gap, or Clay Yang-Mills promotion."

data ComparisonLane : Set where
  orbit-infimum-comparison-lane :
    ComparisonLane
  physical-projection-contraction-lane :
    ComparisonLane
  representative-independence-feed-lane :
    ComparisonLane
  finite-quotient-descent-lane :
    ComparisonLane
  continuum-quotient-descent-lane :
    ComparisonLane
  finite-continuum-quotient-descent-lane :
    ComparisonLane
  blocker-ledger-lane :
    ComparisonLane
  receipt-lane :
    ComparisonLane

data ComparisonStatus : Set where
  package-recorded :
    ComparisonStatus
  imported-uniform112-reduction :
    ComparisonStatus
  imported-quotient112-ledger :
    ComparisonStatus
  orbit-infimum-estimate-required :
    ComparisonStatus
  projection-contraction-estimate-required :
    ComparisonStatus
  representative-independence-required :
    ComparisonStatus
  quotient-descent-required :
    ComparisonStatus
  exact-blocker-recorded :
    ComparisonStatus
  fail-closed-nonpromotion :
    ComparisonStatus

data BlockerKind : Set where
  orbit-infimum-blocker :
    BlockerKind
  projection-contraction-blocker :
    BlockerKind
  representative-independence-blocker :
    BlockerKind
  finite-descent-blocker :
    BlockerKind
  continuum-descent-blocker :
    BlockerKind
  comparison-closure-blocker :
    BlockerKind
  promotion-blocker :
    BlockerKind

canonicalComparisonLanes : List ComparisonLane
canonicalComparisonLanes =
  orbit-infimum-comparison-lane
  ∷ physical-projection-contraction-lane
  ∷ representative-independence-feed-lane
  ∷ finite-quotient-descent-lane
  ∷ continuum-quotient-descent-lane
  ∷ finite-continuum-quotient-descent-lane
  ∷ blocker-ledger-lane
  ∷ receipt-lane
  ∷ []

record ImportedSprint112Inputs : Setω where
  constructor mkImportedSprint112Inputs
  field
    uniformNormReductionReceipt :
      Uniform112.YMSprint112UniformNormBoundReductionReceipt
    quotientIndependenceReceipt :
      Quotient112.YMSprint112QuotientIndependenceDiagramLedgerReceipt
    uniformNormReductionRecorded :
      Bool
    quotientIndependenceLedgerRecorded :
      Bool
    sprint112QuotientComparisonObligationRecorded :
      Bool
    sprint112QuotientIndependenceClosed :
      Bool
    sprint112QuotientIndependenceClosedIsFalse :
      sprint112QuotientIndependenceClosed ≡ false
    sprint112NormEquivalenceClosed :
      Bool
    sprint112NormEquivalenceClosedIsFalse :
      sprint112NormEquivalenceClosed ≡ false

record LaneStatus : Set where
  constructor mkLaneStatus
  field
    lane :
      ComparisonLane
    status :
      ComparisonStatus
    statement :
      String
    recorded :
      Bool
    provedHere :
      Bool
    provedHereIsFalse :
      provedHere ≡ false

record OrbitInfimumComparison : Set where
  constructor mkOrbitInfimumComparison
  field
    laneStatus :
      LaneStatus
    finiteOrbitInfimumSymbol :
      String
    continuumOrbitInfimumSymbol :
      String
    comparisonConstantSymbol :
      String
    finiteGaugeOrbitQuantified :
      Bool
    continuumGaugeOrbitQuantified :
      Bool
    cutoffIndependentConstantRequired :
      Bool
    representativesAllowedOnlyThroughInfimum :
      Bool
    recordedHere :
      Bool
    estimateProvedHere :
      Bool
    estimateProvedHereIsFalse :
      estimateProvedHere ≡ false

record PhysicalProjectionContraction : Set where
  constructor mkPhysicalProjectionContraction
  field
    laneStatus :
      LaneStatus
    finiteProjectionSymbol :
      String
    continuumProjectionSymbol :
      String
    contractionConstantSymbol :
      String
    finiteProjectionNonexpansiveRequired :
      Bool
    continuumProjectionNonexpansiveRequired :
      Bool
    compatibleWithSprint112Maps :
      Bool
    recordedHere :
      Bool
    contractionProvedHere :
      Bool
    contractionProvedHereIsFalse :
      contractionProvedHere ≡ false

record RepresentativeIndependenceFeed : Setω where
  constructor mkRepresentativeIndependenceFeed
  field
    laneStatus :
      LaneStatus
    quotientLedgerReceipt :
      Quotient112.YMSprint112QuotientIndependenceDiagramLedgerReceipt
    finiteRepresentativeDiagramRecorded :
      Bool
    continuumRepresentativeDiagramRecorded :
      Bool
    projectionCommutationDiagramRecorded :
      Bool
    quotientIndependenceRequired :
      Bool
    feedRecordedHere :
      Bool
    feedClosedHere :
      Bool
    feedClosedHereIsFalse :
      feedClosedHere ≡ false

record QuotientDescentPackage : Set where
  constructor mkQuotientDescentPackage
  field
    finiteLaneStatus :
      LaneStatus
    continuumLaneStatus :
      LaneStatus
    finiteStatement :
      String
    continuumStatement :
      String
    finiteQuotientCarrierSymbol :
      String
    continuumQuotientCarrierSymbol :
      String
    embeddingMapSymbol :
      String
    projectionMapSymbol :
      String
    finiteDescentRecordedHere :
      Bool
    continuumDescentRecordedHere :
      Bool
    finiteDescentProvedHere :
      Bool
    finiteDescentProvedHereIsFalse :
      finiteDescentProvedHere ≡ false
    continuumDescentProvedHere :
      Bool
    continuumDescentProvedHereIsFalse :
      continuumDescentProvedHere ≡ false

record FiniteContinuumQuotientDescent : Setω where
  constructor mkFiniteContinuumQuotientDescent
  field
    laneStatus :
      LaneStatus
    descentPackage :
      QuotientDescentPackage
    orbitComparison :
      OrbitInfimumComparison
    projectionContraction :
      PhysicalProjectionContraction
    representativeFeed :
      RepresentativeIndependenceFeed
    comparisonStatement :
      String
    quotientComparisonConstantSymbol :
      String
    finiteAndContinuumDescentRecorded :
      Bool
    closedHere :
      Bool
    closedHereIsFalse :
      closedHere ≡ false

record BlockerEntry : Set where
  constructor mkBlockerEntry
  field
    blocker :
      BlockerKind
    lane :
      ComparisonLane
    statement :
      String
    exactBlockerRecorded :
      Bool
    blocksQuotientNormComparison :
      Bool
    closedHere :
      Bool
    closedHereIsFalse :
      closedHere ≡ false
    status :
      ComparisonStatus

record FailClosedBlockerLedger : Set where
  constructor mkFailClosedBlockerLedger
  field
    laneStatus :
      LaneStatus
    entries :
      List BlockerEntry
    orbitInfimumBlocker :
      String
    projectionContractionBlocker :
      String
    representativeIndependenceBlocker :
      String
    finiteDescentBlocker :
      String
    continuumDescentBlocker :
      String
    comparisonClosureBlocker :
      String
    allBlockersExact :
      Bool
    theoremStillOpen :
      Bool

record TheoremBoundary : Set where
  constructor mkTheoremBoundary
  field
    targetStatement :
      String
    boundaryStatement :
      String
    orbitInfimumComparisonProvedHereFlag :
      Bool
    orbitInfimumComparisonProvedHereFlagIsFalse :
      orbitInfimumComparisonProvedHereFlag ≡ false
    physicalProjectionContractionProvedHereFlag :
      Bool
    physicalProjectionContractionProvedHereFlagIsFalse :
      physicalProjectionContractionProvedHereFlag ≡ false
    representativeIndependenceFeedClosedHereFlag :
      Bool
    representativeIndependenceFeedClosedHereFlagIsFalse :
      representativeIndependenceFeedClosedHereFlag ≡ false
    finiteQuotientDescentProvedHereFlag :
      Bool
    finiteQuotientDescentProvedHereFlagIsFalse :
      finiteQuotientDescentProvedHereFlag ≡ false
    continuumQuotientDescentProvedHereFlag :
      Bool
    continuumQuotientDescentProvedHereFlagIsFalse :
      continuumQuotientDescentProvedHereFlag ≡ false
    quotientNormComparisonEstimateClosedHereFlag :
      Bool
    quotientNormComparisonEstimateClosedHereFlagIsFalse :
      quotientNormComparisonEstimateClosedHereFlag ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    status :
      ComparisonStatus

record YMSprint113QuotientNormComparisonEstimateReceipt : Setω where
  constructor mkYMSprint113QuotientNormComparisonEstimateReceipt
  field
    sprint :
      Nat
    evidencePath :
      String
    importedInputs :
      ImportedSprint112Inputs
    orbitInfimumComparison :
      OrbitInfimumComparison
    physicalProjectionContraction :
      PhysicalProjectionContraction
    representativeIndependenceFeed :
      RepresentativeIndependenceFeed
    quotientDescentPackage :
      QuotientDescentPackage
    finiteContinuumQuotientDescent :
      FiniteContinuumQuotientDescent
    blockerLedger :
      FailClosedBlockerLedger
    theoremBoundary :
      TheoremBoundary
    lanes :
      List ComparisonLane
    evidenceLedger :
      List String
    receiptRecorded :
      Bool
    quotientNormComparisonEstimateRecordedHere :
      Bool
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false

open YMSprint113QuotientNormComparisonEstimateReceipt public

canonicalImportedSprint112Inputs : ImportedSprint112Inputs
canonicalImportedSprint112Inputs =
  mkImportedSprint112Inputs
    Uniform112.canonicalReceipt
    Quotient112.canonicalReceipt
    uniform112ReceiptImported
    quotient112ReceiptImported
    Uniform112.quotientNormComparisonRecorded
    Quotient112.quotientIndependenceClosedHere
    refl
    Uniform112.normEquivalenceTheoremProvedHere
    refl

canonicalOrbitLaneStatus : LaneStatus
canonicalOrbitLaneStatus =
  mkLaneStatus
    orbit-infimum-comparison-lane
    orbit-infimum-estimate-required
    orbitInfimumComparisonText
    orbitInfimumComparisonRecorded
    orbitInfimumComparisonProvedHere
    refl

canonicalProjectionLaneStatus : LaneStatus
canonicalProjectionLaneStatus =
  mkLaneStatus
    physical-projection-contraction-lane
    projection-contraction-estimate-required
    physicalProjectionContractionText
    physicalProjectionContractionRecorded
    physicalProjectionContractionProvedHere
    refl

canonicalRepresentativeFeedLaneStatus : LaneStatus
canonicalRepresentativeFeedLaneStatus =
  mkLaneStatus
    representative-independence-feed-lane
    representative-independence-required
    representativeIndependenceFeedText
    representativeIndependenceFeedRecorded
    representativeIndependenceFeedClosedHere
    refl

canonicalFiniteDescentLaneStatus : LaneStatus
canonicalFiniteDescentLaneStatus =
  mkLaneStatus
    finite-quotient-descent-lane
    quotient-descent-required
    finiteQuotientDescentText
    finiteQuotientDescentRecorded
    finiteQuotientDescentProvedHere
    refl

canonicalContinuumDescentLaneStatus : LaneStatus
canonicalContinuumDescentLaneStatus =
  mkLaneStatus
    continuum-quotient-descent-lane
    quotient-descent-required
    continuumQuotientDescentText
    continuumQuotientDescentRecorded
    continuumQuotientDescentProvedHere
    refl

canonicalFiniteContinuumDescentLaneStatus : LaneStatus
canonicalFiniteContinuumDescentLaneStatus =
  mkLaneStatus
    finite-continuum-quotient-descent-lane
    package-recorded
    "Finite/continuum quotient descent assembly: combine orbit infimum comparison, projection contraction, representative-independence feed, and both descent requirements into the Sprint113 quotient norm comparison package."
    quotientNormComparisonEstimateRecorded
    quotientNormComparisonEstimateClosedHere
    refl

canonicalBlockerLaneStatus : LaneStatus
canonicalBlockerLaneStatus =
  mkLaneStatus
    blocker-ledger-lane
    exact-blocker-recorded
    failClosedBlockersText
    exactFailClosedBlockersRecorded
    quotientNormComparisonEstimateClosedHere
    refl

canonicalOrbitInfimumComparison : OrbitInfimumComparison
canonicalOrbitInfimumComparison =
  mkOrbitInfimumComparison
    canonicalOrbitLaneStatus
    "inf_{g_a in G_a} ||g_a.A_a||_a,phys"
    "inf_{g in G} ||g.A||_H_phys"
    "C_quot"
    true
    true
    true
    true
    orbitInfimumComparisonRecorded
    orbitInfimumComparisonProvedHere
    refl

canonicalPhysicalProjectionContraction :
  PhysicalProjectionContraction
canonicalPhysicalProjectionContraction =
  mkPhysicalProjectionContraction
    canonicalProjectionLaneStatus
    "Pi_a,phys"
    "Pi_phys"
    "1"
    true
    true
    true
    physicalProjectionContractionRecorded
    physicalProjectionContractionProvedHere
    refl

canonicalRepresentativeIndependenceFeed :
  RepresentativeIndependenceFeed
canonicalRepresentativeIndependenceFeed =
  mkRepresentativeIndependenceFeed
    canonicalRepresentativeFeedLaneStatus
    Quotient112.canonicalReceipt
    Quotient112.finiteRepresentativeDiagramRecorded
    Quotient112.continuumRepresentativeDiagramRecorded
    Quotient112.physicalProjectionCommutationDiagramRecorded
    true
    representativeIndependenceFeedRecorded
    representativeIndependenceFeedClosedHere
    refl

canonicalQuotientDescentPackage : QuotientDescentPackage
canonicalQuotientDescentPackage =
  mkQuotientDescentPackage
    canonicalFiniteDescentLaneStatus
    canonicalContinuumDescentLaneStatus
    finiteQuotientDescentText
    continuumQuotientDescentText
    "A_a / G_a,phys"
    "A / G,phys"
    "E_a"
    "P_a"
    finiteQuotientDescentRecorded
    continuumQuotientDescentRecorded
    finiteQuotientDescentProvedHere
    refl
    continuumQuotientDescentProvedHere
    refl

canonicalFiniteContinuumQuotientDescent :
  FiniteContinuumQuotientDescent
canonicalFiniteContinuumQuotientDescent =
  mkFiniteContinuumQuotientDescent
    canonicalFiniteContinuumDescentLaneStatus
    canonicalQuotientDescentPackage
    canonicalOrbitInfimumComparison
    canonicalPhysicalProjectionContraction
    canonicalRepresentativeIndependenceFeed
    "Sprint113 quotient comparison assembly: descend E_a/P_a through finite and continuum quotient carriers, then compare the orbit-infimum quotient norms after physical projection."
    "C_quot"
    true
    quotientNormComparisonEstimateClosedHere
    refl

canonicalBlockerEntries : List BlockerEntry
canonicalBlockerEntries =
  mkBlockerEntry
    orbit-infimum-blocker
    orbit-infimum-comparison-lane
    orbitInfimumComparisonText
    true
    true
    orbitInfimumComparisonProvedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerEntry
    projection-contraction-blocker
    physical-projection-contraction-lane
    physicalProjectionContractionText
    true
    true
    physicalProjectionContractionProvedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerEntry
    representative-independence-blocker
    representative-independence-feed-lane
    representativeIndependenceFeedText
    true
    true
    representativeIndependenceFeedClosedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerEntry
    finite-descent-blocker
    finite-quotient-descent-lane
    finiteQuotientDescentText
    true
    true
    finiteQuotientDescentProvedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerEntry
    continuum-descent-blocker
    continuum-quotient-descent-lane
    continuumQuotientDescentText
    true
    true
    continuumQuotientDescentProvedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerEntry
    comparison-closure-blocker
    finite-continuum-quotient-descent-lane
    failClosedBlockersText
    true
    true
    quotientNormComparisonEstimateClosedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerEntry
    promotion-blocker
    receipt-lane
    nonPromotionBoundaryText
    true
    true
    clayYangMillsPromoted
    refl
    fail-closed-nonpromotion
  ∷ []

canonicalFailClosedBlockerLedger : FailClosedBlockerLedger
canonicalFailClosedBlockerLedger =
  mkFailClosedBlockerLedger
    canonicalBlockerLaneStatus
    canonicalBlockerEntries
    orbitInfimumComparisonText
    physicalProjectionContractionText
    Quotient112.exactBlockersText
    finiteQuotientDescentText
    continuumQuotientDescentText
    failClosedBlockersText
    true
    true

canonicalTheoremBoundary : TheoremBoundary
canonicalTheoremBoundary =
  mkTheoremBoundary
    "Sprint113 target: package the quotient norm comparison estimate needed by Sprint112, with orbit infimum comparison, projection contraction, representative-independence feed, and finite/continuum quotient descent."
    nonPromotionBoundaryText
    orbitInfimumComparisonProvedHere
    refl
    physicalProjectionContractionProvedHere
    refl
    representativeIndependenceFeedClosedHere
    refl
    finiteQuotientDescentProvedHere
    refl
    continuumQuotientDescentProvedHere
    refl
    quotientNormComparisonEstimateClosedHere
    refl
    clayYangMillsPromoted
    refl
    fail-closed-nonpromotion

canonicalYMSprint113QuotientNormComparisonEstimateReceipt :
  YMSprint113QuotientNormComparisonEstimateReceipt
canonicalYMSprint113QuotientNormComparisonEstimateReceipt =
  mkYMSprint113QuotientNormComparisonEstimateReceipt
    sprintNumber
    modulePath
    canonicalImportedSprint112Inputs
    canonicalOrbitInfimumComparison
    canonicalPhysicalProjectionContraction
    canonicalRepresentativeIndependenceFeed
    canonicalQuotientDescentPackage
    canonicalFiniteContinuumQuotientDescent
    canonicalFailClosedBlockerLedger
    canonicalTheoremBoundary
    canonicalComparisonLanes
    (orbitInfimumComparisonText
     ∷ physicalProjectionContractionText
     ∷ representativeIndependenceFeedText
     ∷ finiteQuotientDescentText
     ∷ continuumQuotientDescentText
     ∷ failClosedBlockersText
     ∷ nonPromotionBoundaryText
     ∷ [])
    quotientNormComparisonEstimateRecorded
    quotientNormComparisonEstimateRecorded
    clayYangMillsPromoted
    refl

canonicalReceipt :
  YMSprint113QuotientNormComparisonEstimateReceipt
canonicalReceipt =
  canonicalYMSprint113QuotientNormComparisonEstimateReceipt

canonicalOrbitInfimumComparisonProvedHereIsFalse :
  TheoremBoundary.orbitInfimumComparisonProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalOrbitInfimumComparisonProvedHereIsFalse =
  refl

canonicalPhysicalProjectionContractionProvedHereIsFalse :
  TheoremBoundary.physicalProjectionContractionProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalPhysicalProjectionContractionProvedHereIsFalse =
  refl

canonicalRepresentativeIndependenceFeedClosedHereIsFalse :
  TheoremBoundary.representativeIndependenceFeedClosedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalRepresentativeIndependenceFeedClosedHereIsFalse =
  refl

canonicalFiniteQuotientDescentProvedHereIsFalse :
  TheoremBoundary.finiteQuotientDescentProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalFiniteQuotientDescentProvedHereIsFalse =
  refl

canonicalContinuumQuotientDescentProvedHereIsFalse :
  TheoremBoundary.continuumQuotientDescentProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalContinuumQuotientDescentProvedHereIsFalse =
  refl

canonicalQuotientNormComparisonEstimateClosedHereIsFalse :
  TheoremBoundary.quotientNormComparisonEstimateClosedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalQuotientNormComparisonEstimateClosedHereIsFalse =
  refl

canonicalClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalClayYangMillsPromotedIsFalse =
  refl
