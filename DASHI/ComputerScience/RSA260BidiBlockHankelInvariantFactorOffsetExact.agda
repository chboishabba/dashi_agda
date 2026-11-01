module DASHI.ComputerScience.RSA260BidiBlockHankelInvariantFactorOffsetExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiKrylovFiniteHorizonSaturationExact as FiniteHorizon
import DASHI.ComputerScience.RSA260BidiIntrospectiveOffsetRepairExact as IntrospectiveRepair

------------------------------------------------------------------------
-- RSA-260 BIDI BLOCK-HANKEL / MINIMAL-GENERATOR OFFSET REFINEMENT
--
-- The introspective scheduler selected block invariant-factor /
-- minimal-generator structure for the live finite-horizon residual.
--
-- The executed local discriminator uses projected block Hankel matrices
--
--   H_m = ( S_{i+j} )_{0 <= i,j < m},
--   S_k = X^T B^k Y,
--
-- and compares rank(H_{d-1}), rank(H_d), rank(H_{d+1}) against the already
-- paid shared-generator degree d.
--
-- Result:
--   * 15/18 training carriers have their first tested local Hankel plateau
--     exactly at d;
--   * the remaining 3/18 training carriers gain exactly one further Hankel
--     rank at d+1 before plateauing;
--   * 6/6 held-out carriers plateau at d;
--   * 15/15 preparation/projection cases plateau at d.
--
-- In particular, the concrete (r80,h80)=(512,65) collision is separated:
-- a d=65 case plateaus at order 65, while the tested d=66 cases continue to
-- gain rank at order 66 and plateau afterwards.
--
-- A second rectangular-Hankel probe localises all three training exceptions:
--
--   rank(H_{d+1,d}) - rank(H_{d,d}) = 1
--   rank(H_{d,d+1}) - rank(H_{d,d}) = 0.
--
-- Matched non-exception witnesses have extension signature (0,0).  Thus the
-- surviving square-Hankel rank is entirely row-side / left-extension
-- asymmetry on the tested witnesses.  This is still an observed finite
-- minimal-index signature, not yet a universal invariant-factor theorem.
------------------------------------------------------------------------

finiteHorizonBoundary : FiniteHorizon.FiniteHorizonInterpretationBoundary
finiteHorizonBoundary = FiniteHorizon.canonicalFiniteHorizonInterpretationBoundary

introspectiveBoundary : IntrospectiveRepair.OffsetRepairIntrospectiveBoundary
introspectiveBoundary = IntrospectiveRepair.canonicalOffsetRepairIntrospectiveBoundary

record BlockHankelRuntimeReceipt : Set where
  constructor block-hankel-runtime-receipt
  field
    runtimePath : String
    localGitBlob : String
    runtimeSHA256 : String
    trainingOutputSHA256 : String
    heldoutOutputSHA256 : String
    presentationOutputSHA256 : String
    exactLocalRuntimeBlobExecuted : Bool
    runtimeCommittedToProducerRepository : Bool
open BlockHankelRuntimeReceipt public

currentBlockHankelRuntimeReceipt : BlockHankelRuntimeReceipt
currentBlockHankelRuntimeReceipt = block-hankel-runtime-receipt
  "/mnt/data/rsa260_bidi_hankel_degree_validation.py"
  "bd86d122973158c0144d32e9d8329d1d003ba485"
  "07fed3cce86833dccb67aa74756e1f37cf63b9a42f66f14f9732ef0550d3e04a"
  "943303d8859c4b8e972ea373707de433187ffaac170a16b1bbb38066ca1e341f"
  "9892d967d699e5994d8e344b60963cacb47a5e4f02c1af15fc027d36892b3573"
  "9e3fcaa94ec26dc18bd5172e54df8461b3a3e4892ee4c010e46deb0da2b96c85"
  true
  false

record RectangularHankelRuntimeReceipt : Set where
  constructor rectangular-hankel-runtime-receipt
  field
    runtimePath : String
    localGitBlob : String
    runtimeSHA256 : String
    outputSHA256 : String
    exactLocalRuntimeBlobExecuted : Bool
    runtimeCommittedToProducerRepository : Bool
open RectangularHankelRuntimeReceipt public

currentRectangularHankelRuntimeReceipt : RectangularHankelRuntimeReceipt
currentRectangularHankelRuntimeReceipt = rectangular-hankel-runtime-receipt
  "/mnt/data/rsa260_bidi_rect_hankel_probe.py"
  "32c3ebf74476d6af226ccb4ae1c2cb2b7bf3307a"
  "4e0c88743adcce414bbe3e05781c15ed17c81deefafdb3076a1a000e23e4c685"
  "d591fb9cc0cb60d78e69219715882099bb6e88a48dbad11a0496173cdd176f2f"
  true
  false

record BlockHankelPortfolioReceipt : Set where
  constructor block-hankel-portfolio-receipt
  field
    trainingCases : Nat
    trainingPlateauExactlyAtGeneratorDegree : Nat
    trainingOneRankExtensionAfterGeneratorDegree : Nat
    heldoutCases : Nat
    heldoutPlateauExactlyAtGeneratorDegree : Nat
    presentationCases : Nat
    presentationPlateauExactlyAtGeneratorDegree : Nat
    sharedR80H80CollisionSeparated : Bool
    everyObservedFailureIsExactlyOneExtraHankelRank : Bool
open BlockHankelPortfolioReceipt public

currentBlockHankelPortfolioReceipt : BlockHankelPortfolioReceipt
currentBlockHankelPortfolioReceipt = block-hankel-portfolio-receipt
  18 15 3
  6 6
  15 15
  true
  true

record SharedDynamicCollisionReceipt : Set where
  constructor shared-dynamic-collision-receipt
  field
    reachableRank80 : Nat
    finiteHorizon80 : Nat
    degree65CaseRankH64 : Nat
    degree65CaseRankH65 : Nat
    degree65CaseRankH66 : Nat
    degree66CaseRankH64 : Nat
    degree66CaseRankH65 : Nat
    degree66CaseRankH66 : Nat
    degree66CaseRankH67 : Nat
    projectedHankelProfileSeparatesDegree65FromDegree66 : Bool
open SharedDynamicCollisionReceipt public

currentSharedDynamicCollisionReceipt : SharedDynamicCollisionReceipt
currentSharedDynamicCollisionReceipt = shared-dynamic-collision-receipt
  512 65
  511 519 519
  512 518 520 520
  true

record RectangularHankelAsymmetryReceipt : Set where
  constructor rectangular-hankel-asymmetry-receipt
  field
    exceptionWitnessesChecked : Nat
    matchedNonExceptionWitnessesChecked : Nat
    everyExceptionRowExtension : Nat
    everyExceptionColumnExtension : Nat
    everyExceptionSquareExtension : Nat
    everyMatchedNonExceptionRowExtension : Nat
    everyMatchedNonExceptionColumnExtension : Nat
    everyMatchedNonExceptionSquareExtension : Nat
    oneRankSquareExtensionFactorsThroughRowSideOnlyOnCheckedWitnesses : Bool
open RectangularHankelAsymmetryReceipt public

currentRectangularHankelAsymmetryReceipt : RectangularHankelAsymmetryReceipt
currentRectangularHankelAsymmetryReceipt = rectangular-hankel-asymmetry-receipt
  3 6
  1 0 1
  0 0 0
  true

record BlockHankelOffsetInterpretationBoundary : Set where
  constructor block-hankel-offset-interpretation-boundary
  field
    scheduledInvariantFactorCoordinateWasExecuted : Bool
    blockHankelProfileRefinesR80H80Observer : Bool
    originalSharedDynamicCollisionIsSeparated : Bool
    localPlateauEqualsGeneratorDegreeOnAll39Cases : Bool
    localPlateauEqualsGeneratorDegreeOnHeldoutAndPresentationCases : Bool
    threeTrainingExceptionsRemain : Bool
    threeTrainingExceptionsAreOneRankExtensions : Bool
    rectangularHankelProbeExecuted : Bool
    threeExceptionsShareLeftExtensionOneRightExtensionZero : Bool
    matchedNonExceptionsHaveZeroZeroExtension : Bool
    blockHankelPlateauIsUniversalGeneratorFormula : Bool
    leftExtensionSignatureIsUniversalMinimalIndexTheorem : Bool
    localExecutionPaysProductionSameObjectIdentity : Bool
    localExecutionPaysHistoricalMatrixCustody : Bool
    consumerRefinementReceiptPaid : Bool
    liveOffsetResidualClosed : Bool
open BlockHankelOffsetInterpretationBoundary public

canonicalBlockHankelOffsetInterpretationBoundary : BlockHankelOffsetInterpretationBoundary
canonicalBlockHankelOffsetInterpretationBoundary =
  block-hankel-offset-interpretation-boundary
    true
    true
    true
    false
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false

------------------------------------------------------------------------
-- The introspective residual has become smaller and more specific.
------------------------------------------------------------------------

data BlockHankelOffsetResidual : Set where
  deriveLeftMinimalIndexAsymmetryStatement : BlockHankelOffsetResidual
  explainWhyThreeTrainingProjectionsCarryLeftExtension : BlockHankelOffsetResidual
  bindExecutedRuntimeIntoProducerRepository : BlockHankelOffsetResidual
  compileBlockHankelCoordinateIntoRefinedObserver : BlockHankelOffsetResidual
  proveConsumerDescendsThroughRefinedObserver : BlockHankelOffsetResidual
  acquireSameObjectAStarOrFSolsForProductionHankelDiagnostic : BlockHankelOffsetResidual

firstBlockHankelOffsetResidual : BlockHankelOffsetResidual
firstBlockHankelOffsetResidual = deriveLeftMinimalIndexAsymmetryStatement

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data LocalHankelFitImpliesUniversalGeneratorTheorem : Set where
data LeftExtensionObservationImpliesUniversalMinimalIndexTheorem : Set where
data SyntheticHankelProfileImpliesProductionIdentity : Set where
data CollisionSeparationImpliesConsumerClosure : Set where
data OutputHashImpliesProducerRepositoryCustody : Set where

localFitDoesNotCreateUniversalGeneratorTheorem :
  LocalHankelFitImpliesUniversalGeneratorTheorem → ⊥
localFitDoesNotCreateUniversalGeneratorTheorem ()

leftExtensionObservationDoesNotCreateUniversalMinimalIndexTheorem :
  LeftExtensionObservationImpliesUniversalMinimalIndexTheorem → ⊥
leftExtensionObservationDoesNotCreateUniversalMinimalIndexTheorem ()

syntheticHankelProfileDoesNotCreateProductionIdentity :
  SyntheticHankelProfileImpliesProductionIdentity → ⊥
syntheticHankelProfileDoesNotCreateProductionIdentity ()

collisionSeparationDoesNotCloseConsumer :
  CollisionSeparationImpliesConsumerClosure → ⊥
collisionSeparationDoesNotCloseConsumer ()

outputHashDoesNotCreateProducerRepositoryCustody :
  OutputHashImpliesProducerRepositoryCustody → ⊥
outputHashDoesNotCreateProducerRepositoryCustody ()
