module DASHI.Physics.Closure.YMSprint115ApproximateInverseResidualCriterion where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint114QuadratureResidualClosureCriterion
  as Quad114
import DASHI.Physics.Closure.YMSprint114InverseProjectionClosureCriterion
  as Inv114
import DASHI.Physics.Closure.YMSprint113InverseProjectionResidualAssembly
  as Residual113
import DASHI.Physics.Closure.YMSprint112AdjointnessApproxInverseReduction
  as Reduction112

------------------------------------------------------------------------
-- Sprint115 approximate-inverse residual criterion.
--
-- This module joins the Sprint114 quadrature residual closure criterion and
-- the Sprint114 inverse/projection closure criterion into one explicit
-- approximate-inverse residual criterion.  It consumes supplied left and
-- right residual vanishing evidence, an adjointness residual feed, and an
-- explicit approximate-inverse supply.  It records that the quadrature
-- residual closure lane remains separated: adjointness closure alone does not
-- imply E_a P_a or P_a E_a closure.  Analytic closure theorems remain open
-- false flags, and no Clay Yang-Mills promotion is made here.

sprintNumber : Nat
sprintNumber = 115

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint115ApproximateInverseResidualCriterion.agda"

sprint114QuadratureResidualClosureCriterionPath : String
sprint114QuadratureResidualClosureCriterionPath =
  "DASHI/Physics/Closure/YMSprint114QuadratureResidualClosureCriterion.agda"

sprint114InverseProjectionClosureCriterionPath : String
sprint114InverseProjectionClosureCriterionPath =
  "DASHI/Physics/Closure/YMSprint114InverseProjectionClosureCriterion.agda"

sprint113InverseProjectionResidualAssemblyPath : String
sprint113InverseProjectionResidualAssemblyPath =
  "DASHI/Physics/Closure/YMSprint113InverseProjectionResidualAssembly.agda"

sprint112AdjointnessApproxInverseReductionPath : String
sprint112AdjointnessApproxInverseReductionPath =
  "DASHI/Physics/Closure/YMSprint112AdjointnessApproxInverseReduction.agda"

approximateInverseResidualCriterionRecorded : Bool
approximateInverseResidualCriterionRecorded = true

conditionalApproximateInverseBuilderRecorded : Bool
conditionalApproximateInverseBuilderRecorded = true

leftResidualVanishingSupplyRecorded : Bool
leftResidualVanishingSupplyRecorded = true

rightResidualVanishingSupplyRecorded : Bool
rightResidualVanishingSupplyRecorded = true

adjointnessResidualFeedRecorded : Bool
adjointnessResidualFeedRecorded = true

quadratureResidualClosureSeparated : Bool
quadratureResidualClosureSeparated = true

externalLeftResidualVanishingClosedHere : Bool
externalLeftResidualVanishingClosedHere = false

externalRightResidualVanishingClosedHere : Bool
externalRightResidualVanishingClosedHere = false

externalAdjointnessResidualClosedHere : Bool
externalAdjointnessResidualClosedHere = false

externalApproximateInverseClosedHere : Bool
externalApproximateInverseClosedHere = false

externalQuadratureResidualClosedHere : Bool
externalQuadratureResidualClosedHere = false

externalProjectionSectorClosedHere : Bool
externalProjectionSectorClosedHere = false

externalNormWindowClosedHere : Bool
externalNormWindowClosedHere = false

externalCommonCarrierClosedHere : Bool
externalCommonCarrierClosedHere = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

criterionStatementText : String
criterionStatementText =
  "Sprint115 criterion: supplied left and right approximate-inverse residual vanishing, supplied adjointness residual feed, and supplied projection/norm/common-carrier compatibility assemble an approximate-inverse residual criterion for E_a/P_a on the shared physical comparison window."

leftResidualVanishingSupplyText : String
leftResidualVanishingSupplyText =
  "Left residual supply: ||E_a(P_a v) - v||_H_phys tends to zero for continuum physical comparison vectors on the same admissible a-window."

rightResidualVanishingSupplyText : String
rightResidualVanishingSupplyText =
  "Right residual supply: ||P_a(E_a u) - u||_a,quot tends to zero for finite physical quotient vectors on the same admissible a-window."

adjointnessResidualFeedText : String
adjointnessResidualFeedText =
  "Adjointness feed: consume the Sprint114 quadrature residual closure criterion as a supplied compatibility feed for the E_a/P_a pairing, without using it to infer approximate inverse closure."

approximateInverseSupplyText : String
approximateInverseSupplyText =
  "Approximate-inverse supply: package the left and right residual vanishing supplies with Sprint114 inverse/projection compatibility evidence."

separationFromQuadratureText : String
separationFromQuadratureText =
  "Separation: quadrature residual closure records adjointness compatibility only; Sprint115 requires explicit left and right approximate-inverse residual supplies before the approximate-inverse criterion is inhabited."

conditionalBuilderText : String
conditionalBuilderText =
  "Conditional builder: supplied evidence is assembled into the criterion record, while all external analytic closure flags remain explicit and false in the canonical receipt."

failClosedBoundaryText : String
failClosedBoundaryText =
  "Sprint115 records a conditional approximate-inverse residual criterion only.  It proves no analytic residual vanishing theorem, no quadrature theorem, no projection-sector theorem, no norm-window theorem, no common-carrier theorem, and no Clay Yang-Mills promotion."

data CriterionLane : Set where
  sprint114-quadrature-input-lane :
    CriterionLane
  sprint114-inverse-projection-input-lane :
    CriterionLane
  sprint113-residual-assembly-input-lane :
    CriterionLane
  sprint112-reduction-input-lane :
    CriterionLane
  left-residual-vanishing-supply-lane :
    CriterionLane
  right-residual-vanishing-supply-lane :
    CriterionLane
  adjointness-residual-feed-lane :
    CriterionLane
  approximate-inverse-supply-lane :
    CriterionLane
  separation-from-quadrature-lane :
    CriterionLane
  conditional-builder-lane :
    CriterionLane
  fail-closed-boundary-lane :
    CriterionLane

data CriterionStatus : Set where
  imported-sprint114-quadrature-criterion :
    CriterionStatus
  imported-sprint114-inverse-projection-criterion :
    CriterionStatus
  imported-sprint113-residual-assembly :
    CriterionStatus
  imported-sprint112-reduction :
    CriterionStatus
  supplied-residual-vanishing :
    CriterionStatus
  supplied-adjointness-feed :
    CriterionStatus
  supplied-approximate-inverse-evidence :
    CriterionStatus
  separation-recorded :
    CriterionStatus
  conditional-criterion-inhabited :
    CriterionStatus
  external-analytic-closure-open :
    CriterionStatus
  fail-closed-nonpromotion :
    CriterionStatus

data ResidualSide : Set where
  left-continuum-side :
    ResidualSide
  right-finite-side :
    ResidualSide

canonicalCriterionLanes : List CriterionLane
canonicalCriterionLanes =
  sprint114-quadrature-input-lane
  ∷ sprint114-inverse-projection-input-lane
  ∷ sprint113-residual-assembly-input-lane
  ∷ sprint112-reduction-input-lane
  ∷ left-residual-vanishing-supply-lane
  ∷ right-residual-vanishing-supply-lane
  ∷ adjointness-residual-feed-lane
  ∷ approximate-inverse-supply-lane
  ∷ separation-from-quadrature-lane
  ∷ conditional-builder-lane
  ∷ fail-closed-boundary-lane
  ∷ []

record ImportedClosureBase : Setω where
  constructor mkImportedClosureBase
  field
    quadratureReceipt :
      Quad114.YMSprint114QuadratureResidualClosureCriterionReceipt
    inverseProjectionReceipt :
      Inv114.YMSprint114InverseProjectionClosureCriterionReceipt
    residualAssemblyReceipt :
      Residual113.YMSprint113InverseProjectionResidualAssemblyReceipt
    reductionReceipt :
      Reduction112.YMSprint112AdjointnessApproxInverseReductionReceipt
    quadraturePath :
      String
    inverseProjectionPath :
      String
    residualAssemblyPath :
      String
    reductionPath :
      String
    quadratureCriterionRecorded :
      Bool
    inverseProjectionCriterionRecorded :
      Bool
    residualAssemblyRecorded :
      Bool
    reductionRecorded :
      Bool
    quadratureClosureProvedHere :
      Bool
    quadratureClosureProvedHereIsFalse :
      quadratureClosureProvedHere ≡ false
    inverseProjectionTheoremProvedHere :
      Bool
    inverseProjectionTheoremProvedHereIsFalse :
      inverseProjectionTheoremProvedHere ≡ false
    residualAssemblyTheoremProvedHere :
      Bool
    residualAssemblyTheoremProvedHereIsFalse :
      residualAssemblyTheoremProvedHere ≡ false
    reductionTheoremProvedHere :
      Bool
    reductionTheoremProvedHereIsFalse :
      reductionTheoremProvedHere ≡ false
    status :
      CriterionStatus

record ResidualVanishingSupply : Setω where
  constructor mkResidualVanishingSupply
  field
    side :
      ResidualSide
    lane :
      CriterionLane
    statement :
      String
    sprint112Residual :
      Reduction112.ApproximateInverseResidual
    sprint113Assembly :
      Residual113.ResidualAssembly
    residualSymbol :
      String
    normSymbol :
      String
    admissibleWindow :
      String
    rateSymbol :
      String
    supplied :
      Bool
    suppliedIsTrue :
      supplied ≡ true
    externallyClosedHere :
      Bool
    externallyClosedHereIsFalse :
      externallyClosedHere ≡ false
    status :
      CriterionStatus

record AdjointnessResidualFeed : Setω where
  constructor mkAdjointnessResidualFeed
  field
    lane :
      CriterionLane
    statement :
      String
    quadratureCriterion :
      Quad114.AdjointnessResidualClosureCriterion
    sprint112QuadratureCriterion :
      Reduction112.QuadratureResidualCriterion
    feedSupplied :
      Bool
    feedSuppliedIsTrue :
      feedSupplied ≡ true
    quadratureClosureSeparated :
      Bool
    quadratureClosureSeparatedIsTrue :
      quadratureClosureSeparated ≡ true
    adjointnessClosureProvedHere :
      Bool
    adjointnessClosureProvedHereIsFalse :
      adjointnessClosureProvedHere ≡ false
    status :
      CriterionStatus

record ApproximateInverseSupply : Setω where
  constructor mkApproximateInverseSupply
  field
    lane :
      CriterionLane
    statement :
      String
    leftResidualSupply :
      ResidualVanishingSupply
    rightResidualSupply :
      ResidualVanishingSupply
    inverseProjectionCriterion :
      Inv114.YMSprint114InverseProjectionClosureCriterionReceipt
    residualCompatibility :
      Inv114.ResidualClosureCriterion
    projectionSectorCompatibility :
      Inv114.ProjectionSectorClosureCriterion
    normWindowCompatibility :
      Inv114.NormWindowClosureCriterion
    commonCarrierCompatibility :
      Inv114.CommonCarrierFeedThroughCriterion
    leftSupplyPresent :
      Bool
    leftSupplyPresentIsTrue :
      leftSupplyPresent ≡ true
    rightSupplyPresent :
      Bool
    rightSupplyPresentIsTrue :
      rightSupplyPresent ≡ true
    bothResidualSuppliesPresent :
      Bool
    bothResidualSuppliesPresentIsTrue :
      bothResidualSuppliesPresent ≡ true
    externalApproximateInverseClosedHereFlag :
      Bool
    externalApproximateInverseClosedHereIsFalse :
      externalApproximateInverseClosedHereFlag ≡ false
    status :
      CriterionStatus

record QuadratureResidualSeparation : Setω where
  constructor mkQuadratureResidualSeparation
  field
    lane :
      CriterionLane
    statement :
      String
    quadratureReceipt :
      Quad114.YMSprint114QuadratureResidualClosureCriterionReceipt
    approximateInverseKeptSeparate :
      Bool
    approximateInverseKeptSeparateIsTrue :
      approximateInverseKeptSeparate ≡ true
    approximateInverseClosedByQuadrature :
      Bool
    approximateInverseClosedByQuadratureIsFalse :
      approximateInverseClosedByQuadrature ≡ false
    explicitApproximateInverseSupplyRequired :
      Bool
    explicitApproximateInverseSupplyRequiredIsTrue :
      explicitApproximateInverseSupplyRequired ≡ true
    status :
      CriterionStatus

record ApproximateInverseResidualCriterion : Setω where
  constructor mkApproximateInverseResidualCriterion
  field
    lane :
      CriterionLane
    statement :
      String
    importedBase :
      ImportedClosureBase
    adjointnessFeed :
      AdjointnessResidualFeed
    approximateInverseSupply :
      ApproximateInverseSupply
    quadratureSeparation :
      QuadratureResidualSeparation
    sprint112LeftResidual :
      Reduction112.ApproximateInverseResidual
    sprint112RightResidual :
      Reduction112.ApproximateInverseResidual
    sprint114InverseProjectionReceipt :
      Inv114.YMSprint114InverseProjectionClosureCriterionReceipt
    leftResidualCriterionSatisfied :
      Bool
    leftResidualCriterionSatisfiedIsTrue :
      leftResidualCriterionSatisfied ≡ true
    rightResidualCriterionSatisfied :
      Bool
    rightResidualCriterionSatisfiedIsTrue :
      rightResidualCriterionSatisfied ≡ true
    criterionInhabited :
      Bool
    criterionInhabitedIsTrue :
      criterionInhabited ≡ true
    analyticClosureProvedHere :
      Bool
    analyticClosureProvedHereIsFalse :
      analyticClosureProvedHere ≡ false
    status :
      CriterionStatus

record TheoremBoundary : Set where
  constructor mkTheoremBoundary
  field
    lane :
      CriterionLane
    statement :
      String
    leftResidualVanishingClosedHere :
      Bool
    leftResidualVanishingClosedHereIsFalse :
      leftResidualVanishingClosedHere ≡ false
    rightResidualVanishingClosedHere :
      Bool
    rightResidualVanishingClosedHereIsFalse :
      rightResidualVanishingClosedHere ≡ false
    adjointnessResidualClosedHere :
      Bool
    adjointnessResidualClosedHereIsFalse :
      adjointnessResidualClosedHere ≡ false
    approximateInverseClosedHere :
      Bool
    approximateInverseClosedHereIsFalse :
      approximateInverseClosedHere ≡ false
    quadratureResidualClosedHere :
      Bool
    quadratureResidualClosedHereIsFalse :
      quadratureResidualClosedHere ≡ false
    projectionSectorClosedHere :
      Bool
    projectionSectorClosedHereIsFalse :
      projectionSectorClosedHere ≡ false
    normWindowClosedHere :
      Bool
    normWindowClosedHereIsFalse :
      normWindowClosedHere ≡ false
    commonCarrierClosedHere :
      Bool
    commonCarrierClosedHereIsFalse :
      commonCarrierClosedHere ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    status :
      CriterionStatus

record YMSprint115ApproximateInverseResidualCriterionReceipt : Setω where
  constructor mkYMSprint115ApproximateInverseResidualCriterionReceipt
  field
    sprint :
      Nat
    evidencePath :
      String
    importedBase :
      ImportedClosureBase
    leftResidualSupply :
      ResidualVanishingSupply
    rightResidualSupply :
      ResidualVanishingSupply
    adjointnessFeed :
      AdjointnessResidualFeed
    approximateInverseSupply :
      ApproximateInverseSupply
    quadratureSeparation :
      QuadratureResidualSeparation
    approximateInverseResidualCriterion :
      ApproximateInverseResidualCriterion
    theoremBoundary :
      TheoremBoundary
    lanes :
      List CriterionLane
    evidenceLedger :
      List String
    criterionRecorded :
      Bool
    criterionInhabited :
      Bool
    conditionalBuilderRecorded :
      Bool
    externalAnalyticClosuresOpen :
      Bool
    externalAnalyticClosuresOpenIsTrue :
      externalAnalyticClosuresOpen ≡ true
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false

open ImportedClosureBase public
open ResidualVanishingSupply public
open AdjointnessResidualFeed public
open ApproximateInverseSupply public
open QuadratureResidualSeparation public
open ApproximateInverseResidualCriterion public
open TheoremBoundary public
open YMSprint115ApproximateInverseResidualCriterionReceipt public

canonicalImportedClosureBase : ImportedClosureBase
canonicalImportedClosureBase =
  mkImportedClosureBase
    Quad114.canonicalReceipt
    Inv114.canonicalReceipt
    Residual113.canonicalReceipt
    Reduction112.canonicalReceipt
    sprint114QuadratureResidualClosureCriterionPath
    sprint114InverseProjectionClosureCriterionPath
    sprint113InverseProjectionResidualAssemblyPath
    sprint112AdjointnessApproxInverseReductionPath
    Quad114.quadratureResidualClosureCriterionRecorded
    Inv114.inverseProjectionClosureCriterionRecorded
    Residual113.inverseProjectionResidualAssemblyRecorded
    Reduction112.adjointnessReductionRecorded
    Quad114.adjointnessResidualClosureProvedHere
    refl
    Inv114.inverseProjectionClosureTheoremProvedHere
    refl
    Residual113.residualAssemblyTheoremProvedHere
    refl
    Reduction112.adjointnessReducedAndProvedHere
    refl
    imported-sprint114-quadrature-criterion

leftResidualVanishingSupplyFrom :
  ImportedClosureBase ->
  ResidualVanishingSupply
leftResidualVanishingSupplyFrom base =
  mkResidualVanishingSupply
    left-continuum-side
    left-residual-vanishing-supply-lane
    leftResidualVanishingSupplyText
    (Reduction112.leftInverseResidual
      (ImportedClosureBase.reductionReceipt base))
    (Residual113.canonicalLeftInverseResidual)
    "eps_left(a,v)"
    "||E_a(P_a v) - v||_H_phys"
    "continuum physical finite-energy comparison sector, 0 < a <= a0"
    "rho_left(a)"
    true
    refl
    externalLeftResidualVanishingClosedHere
    refl
    supplied-residual-vanishing

rightResidualVanishingSupplyFrom :
  ImportedClosureBase ->
  ResidualVanishingSupply
rightResidualVanishingSupplyFrom base =
  mkResidualVanishingSupply
    right-finite-side
    right-residual-vanishing-supply-lane
    rightResidualVanishingSupplyText
    (Reduction112.rightInverseResidual
      (ImportedClosureBase.reductionReceipt base))
    (Residual113.canonicalRightInverseResidual)
    "eps_right(a,u)"
    "||P_a(E_a u) - u||_a,quot"
    "finite physical gauge-quotient comparison sector, 0 < a <= a0"
    "rho_right(a)"
    true
    refl
    externalRightResidualVanishingClosedHere
    refl
    supplied-residual-vanishing

adjointnessResidualFeedFrom :
  ImportedClosureBase ->
  AdjointnessResidualFeed
adjointnessResidualFeedFrom base =
  mkAdjointnessResidualFeed
    adjointness-residual-feed-lane
    adjointnessResidualFeedText
    Quad114.canonicalConditionalAdjointnessCriterion
    (Reduction112.quadratureResidual
      (ImportedClosureBase.reductionReceipt base))
    true
    refl
    quadratureResidualClosureSeparated
    refl
    externalAdjointnessResidualClosedHere
    refl
    supplied-adjointness-feed

approximateInverseSupplyFrom :
  Inv114.YMSprint114InverseProjectionClosureCriterionReceipt ->
  ResidualVanishingSupply ->
  ResidualVanishingSupply ->
  ApproximateInverseSupply
approximateInverseSupplyFrom inverseReceipt leftSupply rightSupply =
  mkApproximateInverseSupply
    approximate-inverse-supply-lane
    approximateInverseSupplyText
    leftSupply
    rightSupply
    inverseReceipt
    (Inv114.residualCriterion inverseReceipt)
    (Inv114.projectionSectorCriterion inverseReceipt)
    (Inv114.normWindowCriterion inverseReceipt)
    (Inv114.commonCarrierFeedThroughCriterion inverseReceipt)
    (ResidualVanishingSupply.supplied leftSupply)
    (ResidualVanishingSupply.suppliedIsTrue leftSupply)
    (ResidualVanishingSupply.supplied rightSupply)
    (ResidualVanishingSupply.suppliedIsTrue rightSupply)
    true
    refl
    externalApproximateInverseClosedHere
    refl
    supplied-approximate-inverse-evidence

quadratureSeparationFrom :
  Quad114.YMSprint114QuadratureResidualClosureCriterionReceipt ->
  QuadratureResidualSeparation
quadratureSeparationFrom quadratureReceipt =
  mkQuadratureResidualSeparation
    separation-from-quadrature-lane
    separationFromQuadratureText
    quadratureReceipt
    Quad114.approximateInverseKeptSeparate
    refl
    (Quad114.approximateInverseClosedByThisCriterion
      Quad114.canonicalConditionalAdjointnessCriterion)
    Quad114.canonicalCriterionApproximateInverseClosedByThisIsFalse
    true
    refl
    separation-recorded

buildApproximateInverseResidualCriterion :
  ImportedClosureBase ->
  AdjointnessResidualFeed ->
  ApproximateInverseSupply ->
  QuadratureResidualSeparation ->
  ApproximateInverseResidualCriterion
buildApproximateInverseResidualCriterion base feed inverseSupply separation =
  mkApproximateInverseResidualCriterion
    conditional-builder-lane
    criterionStatementText
    base
    feed
    inverseSupply
    separation
    (ResidualVanishingSupply.sprint112Residual
      (ApproximateInverseSupply.leftResidualSupply inverseSupply))
    (ResidualVanishingSupply.sprint112Residual
      (ApproximateInverseSupply.rightResidualSupply inverseSupply))
    (ApproximateInverseSupply.inverseProjectionCriterion inverseSupply)
    (ApproximateInverseSupply.leftSupplyPresent inverseSupply)
    (ApproximateInverseSupply.leftSupplyPresentIsTrue inverseSupply)
    (ApproximateInverseSupply.rightSupplyPresent inverseSupply)
    (ApproximateInverseSupply.rightSupplyPresentIsTrue inverseSupply)
    (ApproximateInverseSupply.bothResidualSuppliesPresent inverseSupply)
    (ApproximateInverseSupply.bothResidualSuppliesPresentIsTrue inverseSupply)
    externalApproximateInverseClosedHere
    refl
    conditional-criterion-inhabited

canonicalTheoremBoundary : TheoremBoundary
canonicalTheoremBoundary =
  mkTheoremBoundary
    fail-closed-boundary-lane
    failClosedBoundaryText
    externalLeftResidualVanishingClosedHere
    refl
    externalRightResidualVanishingClosedHere
    refl
    externalAdjointnessResidualClosedHere
    refl
    externalApproximateInverseClosedHere
    refl
    externalQuadratureResidualClosedHere
    refl
    externalProjectionSectorClosedHere
    refl
    externalNormWindowClosedHere
    refl
    externalCommonCarrierClosedHere
    refl
    clayYangMillsPromoted
    refl
    fail-closed-nonpromotion

criterionReceiptFrom :
  ImportedClosureBase ->
  ResidualVanishingSupply ->
  ResidualVanishingSupply ->
  AdjointnessResidualFeed ->
  ApproximateInverseSupply ->
  QuadratureResidualSeparation ->
  YMSprint115ApproximateInverseResidualCriterionReceipt
criterionReceiptFrom base leftSupply rightSupply feed inverseSupply separation =
  mkYMSprint115ApproximateInverseResidualCriterionReceipt
    sprintNumber
    modulePath
    base
    leftSupply
    rightSupply
    feed
    inverseSupply
    separation
    (buildApproximateInverseResidualCriterion
      base
      feed
      inverseSupply
      separation)
    canonicalTheoremBoundary
    canonicalCriterionLanes
    (criterionStatementText
     ∷ leftResidualVanishingSupplyText
     ∷ rightResidualVanishingSupplyText
     ∷ adjointnessResidualFeedText
     ∷ approximateInverseSupplyText
     ∷ separationFromQuadratureText
     ∷ conditionalBuilderText
     ∷ failClosedBoundaryText
     ∷ sprint114QuadratureResidualClosureCriterionPath
     ∷ sprint114InverseProjectionClosureCriterionPath
     ∷ sprint113InverseProjectionResidualAssemblyPath
     ∷ sprint112AdjointnessApproxInverseReductionPath
     ∷ [])
    approximateInverseResidualCriterionRecorded
    (ApproximateInverseSupply.bothResidualSuppliesPresent inverseSupply)
    conditionalApproximateInverseBuilderRecorded
    true
    refl
    clayYangMillsPromoted
    refl

canonicalLeftResidualVanishingSupply : ResidualVanishingSupply
canonicalLeftResidualVanishingSupply =
  leftResidualVanishingSupplyFrom canonicalImportedClosureBase

canonicalRightResidualVanishingSupply : ResidualVanishingSupply
canonicalRightResidualVanishingSupply =
  rightResidualVanishingSupplyFrom canonicalImportedClosureBase

canonicalAdjointnessResidualFeed : AdjointnessResidualFeed
canonicalAdjointnessResidualFeed =
  adjointnessResidualFeedFrom canonicalImportedClosureBase

canonicalApproximateInverseSupply : ApproximateInverseSupply
canonicalApproximateInverseSupply =
  approximateInverseSupplyFrom
    Inv114.canonicalReceipt
    canonicalLeftResidualVanishingSupply
    canonicalRightResidualVanishingSupply

canonicalQuadratureSeparation : QuadratureResidualSeparation
canonicalQuadratureSeparation =
  quadratureSeparationFrom Quad114.canonicalReceipt

canonicalApproximateInverseResidualCriterion :
  ApproximateInverseResidualCriterion
canonicalApproximateInverseResidualCriterion =
  buildApproximateInverseResidualCriterion
    canonicalImportedClosureBase
    canonicalAdjointnessResidualFeed
    canonicalApproximateInverseSupply
    canonicalQuadratureSeparation

canonicalYMSprint115ApproximateInverseResidualCriterionReceipt :
  YMSprint115ApproximateInverseResidualCriterionReceipt
canonicalYMSprint115ApproximateInverseResidualCriterionReceipt =
  criterionReceiptFrom
    canonicalImportedClosureBase
    canonicalLeftResidualVanishingSupply
    canonicalRightResidualVanishingSupply
    canonicalAdjointnessResidualFeed
    canonicalApproximateInverseSupply
    canonicalQuadratureSeparation

canonicalReceipt :
  YMSprint115ApproximateInverseResidualCriterionReceipt
canonicalReceipt =
  canonicalYMSprint115ApproximateInverseResidualCriterionReceipt

canonicalCriterionInhabitedIsTrue :
  criterionInhabited canonicalReceipt ≡ true
canonicalCriterionInhabitedIsTrue =
  refl

canonicalLeftResidualSupplyIsTrue :
  ResidualVanishingSupply.supplied
    (leftResidualSupply canonicalReceipt) ≡ true
canonicalLeftResidualSupplyIsTrue =
  refl

canonicalRightResidualSupplyIsTrue :
  ResidualVanishingSupply.supplied
    (rightResidualSupply canonicalReceipt) ≡ true
canonicalRightResidualSupplyIsTrue =
  refl

canonicalAdjointnessFeedSuppliedIsTrue :
  AdjointnessResidualFeed.feedSupplied
    (adjointnessFeed canonicalReceipt) ≡ true
canonicalAdjointnessFeedSuppliedIsTrue =
  refl

canonicalQuadratureSeparationRecordedIsTrue :
  QuadratureResidualSeparation.approximateInverseKeptSeparate
    (quadratureSeparation canonicalReceipt) ≡ true
canonicalQuadratureSeparationRecordedIsTrue =
  refl

canonicalApproximateInverseNotClosedByQuadratureIsFalse :
  QuadratureResidualSeparation.approximateInverseClosedByQuadrature
    (quadratureSeparation canonicalReceipt) ≡ false
canonicalApproximateInverseNotClosedByQuadratureIsFalse =
  refl

canonicalExternalLeftResidualVanishingClosedHereIsFalse :
  TheoremBoundary.leftResidualVanishingClosedHere
    (theoremBoundary canonicalReceipt) ≡ false
canonicalExternalLeftResidualVanishingClosedHereIsFalse =
  refl

canonicalExternalRightResidualVanishingClosedHereIsFalse :
  TheoremBoundary.rightResidualVanishingClosedHere
    (theoremBoundary canonicalReceipt) ≡ false
canonicalExternalRightResidualVanishingClosedHereIsFalse =
  refl

canonicalExternalAdjointnessResidualClosedHereIsFalse :
  TheoremBoundary.adjointnessResidualClosedHere
    (theoremBoundary canonicalReceipt) ≡ false
canonicalExternalAdjointnessResidualClosedHereIsFalse =
  refl

canonicalExternalApproximateInverseClosedHereIsFalse :
  TheoremBoundary.approximateInverseClosedHere
    (theoremBoundary canonicalReceipt) ≡ false
canonicalExternalApproximateInverseClosedHereIsFalse =
  refl

canonicalExternalQuadratureResidualClosedHereIsFalse :
  TheoremBoundary.quadratureResidualClosedHere
    (theoremBoundary canonicalReceipt) ≡ false
canonicalExternalQuadratureResidualClosedHereIsFalse =
  refl

canonicalExternalProjectionSectorClosedHereIsFalse :
  TheoremBoundary.projectionSectorClosedHere
    (theoremBoundary canonicalReceipt) ≡ false
canonicalExternalProjectionSectorClosedHereIsFalse =
  refl

canonicalExternalNormWindowClosedHereIsFalse :
  TheoremBoundary.normWindowClosedHere
    (theoremBoundary canonicalReceipt) ≡ false
canonicalExternalNormWindowClosedHereIsFalse =
  refl

canonicalExternalCommonCarrierClosedHereIsFalse :
  TheoremBoundary.commonCarrierClosedHere
    (theoremBoundary canonicalReceipt) ≡ false
canonicalExternalCommonCarrierClosedHereIsFalse =
  refl

canonicalClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalClayYangMillsPromotedIsFalse =
  refl

canonicalReceiptEvidenceLedger : List String
canonicalReceiptEvidenceLedger =
  evidenceLedger canonicalReceipt
