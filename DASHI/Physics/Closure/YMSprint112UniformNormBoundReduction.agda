module DASHI.Physics.Closure.YMSprint112UniformNormBoundReduction where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint111NormEquivalenceUniformAWindow
  as Norm111
import DASHI.Physics.Closure.YMSprint111FiniteContinuumEmbeddingProjectionMaps
  as Maps111
import DASHI.Physics.Closure.YMSprint110WeakCompactnessEnergyCore
  as Weak110

------------------------------------------------------------------------
-- Sprint112 uniform norm bound reduction.
--
-- This module reduces the Sprint111 uniform E_a/P_a norm-bound target to
-- concrete local estimate obligations: local Jacobian control, partition of
-- unity/multiplicity control, and quotient norm comparison.  It is a
-- fail-closed receipt only.  No local estimate, partition estimate, uniform
-- upper/lower theorem, norm-equivalence theorem, weak-compactness feed, or
-- Clay Yang-Mills promotion is proved here.

uniformNormBoundReductionRecorded : Bool
uniformNormBoundReductionRecorded = true

localJacobianEstimateRecorded : Bool
localJacobianEstimateRecorded = true

partitionOfUnityEstimateRecorded : Bool
partitionOfUnityEstimateRecorded = true

quotientNormComparisonRecorded : Bool
quotientNormComparisonRecorded = true

weakCompactnessUseRecorded : Bool
weakCompactnessUseRecorded = true

localJacobianEstimateProvedHere : Bool
localJacobianEstimateProvedHere = false

partitionEstimateProvedHere : Bool
partitionEstimateProvedHere = false

uniformUpperBoundReducedAndProvedHere : Bool
uniformUpperBoundReducedAndProvedHere = false

uniformLowerBoundReducedAndProvedHere : Bool
uniformLowerBoundReducedAndProvedHere = false

normEquivalenceTheoremProvedHere : Bool
normEquivalenceTheoremProvedHere = false

weakCompactnessFedHere : Bool
weakCompactnessFedHere = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

sprintNumber : Nat
sprintNumber = 112

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint112UniformNormBoundReduction.agda"

admissibleAWindowStatementText : String
admissibleAWindowStatementText =
  "Admissible a-window: reduce uniform norm bounds only over the Sprint111 window 0 < a <= a0, with the same finite physical quotient, continuum carrier, and renormalization convention used for E_a and P_a."

localJacobianEstimateStatementText : String
localJacobianEstimateStatementText =
  "Local Jacobian estimate obligation: on every admissible chart cell, prove an a-independent bound comparing renormalized finite cell volume, interpolation Jacobian, and continuum H_phys density for the E_a/P_a candidate maps."

partitionMultiplicityBoundStatementText : String
partitionMultiplicityBoundStatementText =
  "Partition/multiplicity bound obligation: choose a partition of unity with cutoff-independent overlap multiplicity and derivative losses, so local chart estimates sum without changing the uniform constants."

quotientNormComparisonStatementText : String
quotientNormComparisonStatementText =
  "Quotient norm comparison obligation: show that gauge-representative choices and physical projection do not increase the finite quotient norm beyond a cutoff-independent comparison constant."

upperBoundBlockerStatementText : String
upperBoundBlockerStatementText =
  "Upper bound blocker: the Sprint111 upper E_a norm bound is reduced to local Jacobian, partition/multiplicity, and quotient comparison estimates, but those estimates are not proved here."

lowerBoundBlockerStatementText : String
lowerBoundBlockerStatementText =
  "Lower bound blocker: the Sprint111 lower P_a/E_a comparison is reduced to quotient-compatible local inverse comparison and partition stability, but those estimates are not proved here."

weakCompactnessUseStatementText : String
weakCompactnessUseStatementText =
  "Weak compactness use: once the reduced uniform norm obligations are proved elsewhere, bounded finite transfer-form sequences can be compared in the Sprint110 common physical carrier."

nonPromotionBoundaryText : String
nonPromotionBoundaryText =
  "Sprint112 records a reduction of uniform norm bounds to concrete local estimate obligations only; it does not prove the local estimates, close norm equivalence, feed weak compactness, prove a mass gap, or promote Clay Yang-Mills."

data NormBoundLane : Set where
  admissible-a-window :
    NormBoundLane
  local-jacobian-estimate :
    NormBoundLane
  partition-of-unity-estimate :
    NormBoundLane
  quotient-norm-comparison :
    NormBoundLane
  upper-bound-reduction :
    NormBoundLane
  lower-bound-reduction :
    NormBoundLane
  weak-compactness-consumer :
    NormBoundLane
  blocker-ledger-lane :
    NormBoundLane
  receipt-lane :
    NormBoundLane

data NormBoundStatus : Set where
  imported-sprint111-norm-window :
    NormBoundStatus
  imported-sprint111-map-surface :
    NormBoundStatus
  imported-sprint110-weak-core :
    NormBoundStatus
  reduction-recorded :
    NormBoundStatus
  local-obligation-recorded :
    NormBoundStatus
  partition-obligation-recorded :
    NormBoundStatus
  quotient-obligation-recorded :
    NormBoundStatus
  analytic-proof-required :
    NormBoundStatus
  exact-blocker-recorded :
    NormBoundStatus
  fail-closed-nonpromotion :
    NormBoundStatus

data BoundDirection : Set where
  upper-direction :
    BoundDirection
  lower-direction :
    BoundDirection

data LocalEstimateKind : Set where
  jacobian-volume-density :
    LocalEstimateKind
  inverse-local-comparison :
    LocalEstimateKind

data BlockerKind : Set where
  local-jacobian-blocker :
    BlockerKind
  partition-multiplicity-blocker :
    BlockerKind
  quotient-comparison-blocker :
    BlockerKind
  upper-reduction-blocker :
    BlockerKind
  lower-reduction-blocker :
    BlockerKind
  weak-compactness-feed-blocker :
    BlockerKind
  norm-equivalence-blocker :
    BlockerKind

canonicalNormBoundLanes : List NormBoundLane
canonicalNormBoundLanes =
  admissible-a-window
  ∷ local-jacobian-estimate
  ∷ partition-of-unity-estimate
  ∷ quotient-norm-comparison
  ∷ upper-bound-reduction
  ∷ lower-bound-reduction
  ∷ weak-compactness-consumer
  ∷ blocker-ledger-lane
  ∷ receipt-lane
  ∷ []

record ImportedSprintInputs : Setω where
  constructor mkImportedSprintInputs
  field
    normWindowReceipt :
      Norm111.YMSprint111NormEquivalenceUniformAWindowReceipt
    mapsReceipt :
      Maps111.YMSprint111FiniteContinuumEmbeddingProjectionMapsReceipt
    weakCompactnessReceipt :
      Weak110.YMSprint110WeakCompactnessEnergyCoreReceipt
    normWindowRecorded :
      Bool
    embeddingProjectionMapsRecorded :
      Bool
    weakCompactnessRecorded :
      Bool
    sprint111UpperBoundClosed :
      Bool
    sprint111LowerBoundClosed :
      Bool
    sprint111EmbeddingBoundClosed :
      Bool
    sprint111ProjectionBoundClosed :
      Bool
    sprint110WeakExtractionClosed :
      Bool

record NormBoundLaneStatus : Set where
  constructor mkNormBoundLaneStatus
  field
    lane :
      NormBoundLane
    status :
      NormBoundStatus
    statement :
      String
    recorded :
      Bool
    theoremClosedHere :
      Bool
    theoremClosedHereIsFalse :
      theoremClosedHere ≡ false

record LocalEstimateObligation : Set where
  constructor mkLocalEstimateObligation
  field
    lane :
      NormBoundLane
    kind :
      LocalEstimateKind
    statement :
      String
    chartCellSymbol :
      String
    mapSymbols :
      String
    cutoffWindow :
      String
    jacobianConstantSymbol :
      String
    cutoffIndependentRequired :
      Bool
    physicalSectorCompatibleRequired :
      Bool
    gaugeQuotientCompatibleRequired :
      Bool
    recordedHere :
      Bool
    provedHere :
      Bool
    provedHereIsFalse :
      provedHere ≡ false
    status :
      NormBoundStatus

record PartitionEstimateObligation : Set where
  constructor mkPartitionEstimateObligation
  field
    lane :
      NormBoundLane
    statement :
      String
    partitionSymbol :
      String
    multiplicityConstantSymbol :
      String
    derivativeLossConstantSymbol :
      String
    cutoffIndependentMultiplicityRequired :
      Bool
    compatibleWithLocalChartsRequired :
      Bool
    summationStableRequired :
      Bool
    recordedHere :
      Bool
    provedHere :
      Bool
    provedHereIsFalse :
      provedHere ≡ false
    status :
      NormBoundStatus

record QuotientNormComparisonObligation : Set where
  constructor mkQuotientNormComparisonObligation
  field
    lane :
      NormBoundLane
    statement :
      String
    finiteQuotientNormSymbol :
      String
    continuumNormSymbol :
      String
    quotientComparisonConstantSymbol :
      String
    gaugeRepresentativeInvariantRequired :
      Bool
    physicalProjectionStableRequired :
      Bool
    compatibleWithMaps111Required :
      Bool
    recordedHere :
      Bool
    provedHere :
      Bool
    provedHereIsFalse :
      provedHere ≡ false
    status :
      NormBoundStatus

record UpperReductionCriterion : Set where
  constructor mkUpperReductionCriterion
  field
    lane :
      NormBoundLane
    direction :
      BoundDirection
    statement :
      String
    localEstimate :
      LocalEstimateObligation
    partitionEstimate :
      PartitionEstimateObligation
    quotientComparison :
      QuotientNormComparisonObligation
    targetMapSymbol :
      String
    targetConstantSymbol :
      String
    reducedToConcreteObligations :
      Bool
    provedHere :
      Bool
    provedHereIsFalse :
      provedHere ≡ false
    blocker :
      String
    status :
      NormBoundStatus

record LowerReductionCriterion : Set where
  constructor mkLowerReductionCriterion
  field
    lane :
      NormBoundLane
    direction :
      BoundDirection
    statement :
      String
    localEstimate :
      LocalEstimateObligation
    partitionEstimate :
      PartitionEstimateObligation
    quotientComparison :
      QuotientNormComparisonObligation
    targetMapSymbol :
      String
    targetConstantSymbol :
      String
    reducedToConcreteObligations :
      Bool
    provedHere :
      Bool
    provedHereIsFalse :
      provedHere ≡ false
    blocker :
      String
    status :
      NormBoundStatus

record WeakCompactnessConsumer : Setω where
  constructor mkWeakCompactnessConsumer
  field
    lane :
      NormBoundLane
    statement :
      String
    weakReceipt :
      Weak110.YMSprint110WeakCompactnessEnergyCoreReceipt
    normWindowReceipt :
      Norm111.YMSprint111NormEquivalenceUniformAWindowReceipt
    needsUpperReduction :
      Bool
    needsLowerReduction :
      Bool
    normalizedSequenceRecorded :
      Bool
    uniformEnergyBoundRecorded :
      Bool
    fedHere :
      Bool
    fedHereIsFalse :
      fedHere ≡ false
    status :
      NormBoundStatus

record BlockerLedgerEntry : Set where
  constructor mkBlockerLedgerEntry
  field
    blocker :
      BlockerKind
    lane :
      NormBoundLane
    statement :
      String
    blocksUniformNormBound :
      Bool
    closedHere :
      Bool
    closedHereIsFalse :
      closedHere ≡ false
    status :
      NormBoundStatus

record BlockerLedger : Set where
  constructor mkBlockerLedger
  field
    lane :
      NormBoundLane
    entries :
      List BlockerLedgerEntry
    localJacobianBlocker :
      String
    partitionBlocker :
      String
    quotientComparisonBlocker :
      String
    upperReductionBlocker :
      String
    lowerReductionBlocker :
      String
    allBlockersConcrete :
      Bool
    theoremStillOpen :
      Bool
    status :
      NormBoundStatus

record ReductionTheoremBoundary : Set where
  constructor mkReductionTheoremBoundary
  field
    targetStatement :
      String
    nonPromotionStatement :
      String
    localJacobianEstimateProvedHereFlag :
      Bool
    localJacobianEstimateProvedHereIsFalse :
      localJacobianEstimateProvedHereFlag ≡ false
    partitionEstimateProvedHereFlag :
      Bool
    partitionEstimateProvedHereIsFalse :
      partitionEstimateProvedHereFlag ≡ false
    uniformUpperBoundReducedAndProvedHereFlag :
      Bool
    uniformUpperBoundReducedAndProvedHereIsFalse :
      uniformUpperBoundReducedAndProvedHereFlag ≡ false
    uniformLowerBoundReducedAndProvedHereFlag :
      Bool
    uniformLowerBoundReducedAndProvedHereIsFalse :
      uniformLowerBoundReducedAndProvedHereFlag ≡ false
    normEquivalenceTheoremProvedHereFlag :
      Bool
    normEquivalenceTheoremProvedHereIsFalse :
      normEquivalenceTheoremProvedHereFlag ≡ false
    weakCompactnessFedHereFlag :
      Bool
    weakCompactnessFedHereIsFalse :
      weakCompactnessFedHereFlag ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    status :
      NormBoundStatus

record YMSprint112UniformNormBoundReductionReceipt : Setω where
  constructor mkYMSprint112UniformNormBoundReductionReceipt
  field
    sprint :
      Nat
    evidencePath :
      String
    importedInputs :
      ImportedSprintInputs
    admissibleWindowStatus :
      NormBoundLaneStatus
    localJacobianEstimate :
      LocalEstimateObligation
    partitionEstimate :
      PartitionEstimateObligation
    quotientComparison :
      QuotientNormComparisonObligation
    upperReduction :
      UpperReductionCriterion
    lowerReduction :
      LowerReductionCriterion
    weakCompactnessConsumer :
      WeakCompactnessConsumer
    blockerLedger :
      BlockerLedger
    theoremBoundary :
      ReductionTheoremBoundary
    lanes :
      List NormBoundLane
    receiptRecorded :
      Bool
    reductionRecordedHere :
      Bool
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    evidenceLedger :
      List String

open YMSprint112UniformNormBoundReductionReceipt public

canonicalImportedSprintInputs : ImportedSprintInputs
canonicalImportedSprintInputs =
  mkImportedSprintInputs
    Norm111.canonicalReceipt
    Maps111.canonicalReceipt
    Weak110.canonicalReceipt
    Norm111.normEquivalenceUniformAWindowRecorded
    Maps111.moduleReceiptRecorded
    Weak110.weakCompactnessEnergyCoreRecorded
    Norm111.uniformUpperNormBoundProvedHere
    Norm111.uniformLowerNormBoundProvedHere
    Maps111.boundedEmbeddingUniformInAProvedHere
    Maps111.boundedProjectionUniformInAProvedHere
    Weak110.weakSubsequenceExtractionProvedHere

canonicalAdmissibleWindowStatus : NormBoundLaneStatus
canonicalAdmissibleWindowStatus =
  mkNormBoundLaneStatus
    admissible-a-window
    imported-sprint111-norm-window
    admissibleAWindowStatementText
    true
    normEquivalenceTheoremProvedHere
    refl

canonicalLocalJacobianEstimate : LocalEstimateObligation
canonicalLocalJacobianEstimate =
  mkLocalEstimateObligation
    local-jacobian-estimate
    jacobian-volume-density
    localJacobianEstimateStatementText
    "U_a"
    "E_a, P_a"
    "0 < a <= a0"
    "C_J"
    true
    true
    true
    localJacobianEstimateRecorded
    localJacobianEstimateProvedHere
    refl
    local-obligation-recorded

canonicalPartitionEstimate : PartitionEstimateObligation
canonicalPartitionEstimate =
  mkPartitionEstimateObligation
    partition-of-unity-estimate
    partitionMultiplicityBoundStatementText
    "{chi_i,a}"
    "M_part"
    "C_dchi"
    true
    true
    true
    partitionOfUnityEstimateRecorded
    partitionEstimateProvedHere
    refl
    partition-obligation-recorded

canonicalQuotientNormComparison :
  QuotientNormComparisonObligation
canonicalQuotientNormComparison =
  mkQuotientNormComparisonObligation
    quotient-norm-comparison
    quotientNormComparisonStatementText
    "||-||_a,quot"
    "||-||_H_phys"
    "C_quot"
    true
    true
    true
    quotientNormComparisonRecorded
    normEquivalenceTheoremProvedHere
    refl
    quotient-obligation-recorded

canonicalUpperReductionCriterion : UpperReductionCriterion
canonicalUpperReductionCriterion =
  mkUpperReductionCriterion
    upper-bound-reduction
    upper-direction
    upperBoundBlockerStatementText
    canonicalLocalJacobianEstimate
    canonicalPartitionEstimate
    canonicalQuotientNormComparison
    "E_a"
    "C_upper"
    uniformNormBoundReductionRecorded
    uniformUpperBoundReducedAndProvedHere
    refl
    upperBoundBlockerStatementText
    reduction-recorded

canonicalLowerReductionCriterion : LowerReductionCriterion
canonicalLowerReductionCriterion =
  mkLowerReductionCriterion
    lower-bound-reduction
    lower-direction
    lowerBoundBlockerStatementText
    canonicalLocalJacobianEstimate
    canonicalPartitionEstimate
    canonicalQuotientNormComparison
    "P_a and E_a"
    "C_lower"
    uniformNormBoundReductionRecorded
    uniformLowerBoundReducedAndProvedHere
    refl
    lowerBoundBlockerStatementText
    reduction-recorded

canonicalWeakCompactnessConsumer : WeakCompactnessConsumer
canonicalWeakCompactnessConsumer =
  mkWeakCompactnessConsumer
    weak-compactness-consumer
    weakCompactnessUseStatementText
    Weak110.canonicalReceipt
    Norm111.canonicalReceipt
    true
    true
    Weak110.normalizedTransferFormSequenceDefinedHere
    Weak110.uniformFormEnergyBoundAssumedHere
    weakCompactnessFedHere
    refl
    imported-sprint110-weak-core

canonicalBlockerLedgerEntries : List BlockerLedgerEntry
canonicalBlockerLedgerEntries =
  mkBlockerLedgerEntry
    local-jacobian-blocker
    local-jacobian-estimate
    localJacobianEstimateStatementText
    true
    localJacobianEstimateProvedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerLedgerEntry
    partition-multiplicity-blocker
    partition-of-unity-estimate
    partitionMultiplicityBoundStatementText
    true
    partitionEstimateProvedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerLedgerEntry
    quotient-comparison-blocker
    quotient-norm-comparison
    quotientNormComparisonStatementText
    true
    normEquivalenceTheoremProvedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerLedgerEntry
    upper-reduction-blocker
    upper-bound-reduction
    upperBoundBlockerStatementText
    true
    uniformUpperBoundReducedAndProvedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerLedgerEntry
    lower-reduction-blocker
    lower-bound-reduction
    lowerBoundBlockerStatementText
    true
    uniformLowerBoundReducedAndProvedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerLedgerEntry
    weak-compactness-feed-blocker
    weak-compactness-consumer
    weakCompactnessUseStatementText
    true
    weakCompactnessFedHere
    refl
    exact-blocker-recorded
  ∷ mkBlockerLedgerEntry
    norm-equivalence-blocker
    receipt-lane
    Norm111.uniformNormEquivalenceBlockerText
    true
    normEquivalenceTheoremProvedHere
    refl
    exact-blocker-recorded
  ∷ []

canonicalBlockerLedger : BlockerLedger
canonicalBlockerLedger =
  mkBlockerLedger
    blocker-ledger-lane
    canonicalBlockerLedgerEntries
    localJacobianEstimateStatementText
    partitionMultiplicityBoundStatementText
    quotientNormComparisonStatementText
    upperBoundBlockerStatementText
    lowerBoundBlockerStatementText
    true
    true
    exact-blocker-recorded

canonicalReductionTheoremBoundary : ReductionTheoremBoundary
canonicalReductionTheoremBoundary =
  mkReductionTheoremBoundary
    "Uniform Sprint112 target: reduce the Sprint111 E_a/P_a upper and lower norm bounds to local Jacobian, partition/multiplicity, and quotient norm comparison obligations."
    nonPromotionBoundaryText
    localJacobianEstimateProvedHere
    refl
    partitionEstimateProvedHere
    refl
    uniformUpperBoundReducedAndProvedHere
    refl
    uniformLowerBoundReducedAndProvedHere
    refl
    normEquivalenceTheoremProvedHere
    refl
    weakCompactnessFedHere
    refl
    clayYangMillsPromoted
    refl
    fail-closed-nonpromotion

canonicalYMSprint112UniformNormBoundReductionReceipt :
  YMSprint112UniformNormBoundReductionReceipt
canonicalYMSprint112UniformNormBoundReductionReceipt =
  mkYMSprint112UniformNormBoundReductionReceipt
    sprintNumber
    modulePath
    canonicalImportedSprintInputs
    canonicalAdmissibleWindowStatus
    canonicalLocalJacobianEstimate
    canonicalPartitionEstimate
    canonicalQuotientNormComparison
    canonicalUpperReductionCriterion
    canonicalLowerReductionCriterion
    canonicalWeakCompactnessConsumer
    canonicalBlockerLedger
    canonicalReductionTheoremBoundary
    canonicalNormBoundLanes
    uniformNormBoundReductionRecorded
    uniformNormBoundReductionRecorded
    clayYangMillsPromoted
    refl
    (admissibleAWindowStatementText
     ∷ localJacobianEstimateStatementText
     ∷ partitionMultiplicityBoundStatementText
     ∷ quotientNormComparisonStatementText
     ∷ upperBoundBlockerStatementText
     ∷ lowerBoundBlockerStatementText
     ∷ weakCompactnessUseStatementText
     ∷ nonPromotionBoundaryText
     ∷ [])

canonicalReceipt :
  YMSprint112UniformNormBoundReductionReceipt
canonicalReceipt =
  canonicalYMSprint112UniformNormBoundReductionReceipt

canonicalReceiptLocalJacobianEstimateProvedHereIsFalse :
  ReductionTheoremBoundary.localJacobianEstimateProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalReceiptLocalJacobianEstimateProvedHereIsFalse =
  refl

canonicalReceiptPartitionEstimateProvedHereIsFalse :
  ReductionTheoremBoundary.partitionEstimateProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalReceiptPartitionEstimateProvedHereIsFalse =
  refl

canonicalReceiptUniformUpperBoundReducedAndProvedHereIsFalse :
  ReductionTheoremBoundary.uniformUpperBoundReducedAndProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalReceiptUniformUpperBoundReducedAndProvedHereIsFalse =
  refl

canonicalReceiptUniformLowerBoundReducedAndProvedHereIsFalse :
  ReductionTheoremBoundary.uniformLowerBoundReducedAndProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalReceiptUniformLowerBoundReducedAndProvedHereIsFalse =
  refl

canonicalReceiptNormEquivalenceTheoremProvedHereIsFalse :
  ReductionTheoremBoundary.normEquivalenceTheoremProvedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalReceiptNormEquivalenceTheoremProvedHereIsFalse =
  refl

canonicalReceiptWeakCompactnessFedHereIsFalse :
  ReductionTheoremBoundary.weakCompactnessFedHereFlag
    (theoremBoundary canonicalReceipt) ≡ false
canonicalReceiptWeakCompactnessFedHereIsFalse =
  refl

canonicalReceiptClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalReceiptClayYangMillsPromotedIsFalse =
  refl
