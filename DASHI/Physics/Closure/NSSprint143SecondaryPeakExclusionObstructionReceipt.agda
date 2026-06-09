module DASHI.Physics.Closure.NSSprint143SecondaryPeakExclusionObstructionReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSSprint142GlobalConcavityObstructionReceipt
  as S142

------------------------------------------------------------------------
-- NS Sprint 143 secondary-peak exclusion obstruction receipt.
--
-- This disjoint receipt anchors to Sprint 142 and records
-- SecondaryPeakExclusion as still false/open and fail-closed:
--
--   * the Sprint 142 global-concavity obstruction remains closed;
--   * local single-peak, symmetry, and parabolic support are accepted;
--   * global secondary peak exclusion is not proved;
--   * nonlinear shoulder formation remains uncontrolled;
--   * off-center positive v crossings remain possible;
--   * no coupled axisymmetric zero-number/Sturm theorem is available;
--   * boundary and annular migration remain uncontrolled;
--   * no compatible constants/theorem are present;
--   * global axial monotonicity is not promoted;
--   * no full Clay Navier-Stokes solution is constructed;
--   * no Clay promotion is recorded.

sprint143SecondaryPeakExclusionObstructionLedgerClosed : Bool
sprint143SecondaryPeakExclusionObstructionLedgerClosed = true

sprint142GlobalConcavityObstructionAnchored : Bool
sprint142GlobalConcavityObstructionAnchored = true

SecondaryPeakExclusionAttemptRecorded : Bool
SecondaryPeakExclusionAttemptRecorded = true

localSinglePeakSupport : Bool
localSinglePeakSupport = true

localSymmetrySupport : Bool
localSymmetrySupport = true

localParabolicSupport : Bool
localParabolicSupport = true

localSinglePeakSymmetryParabolicSupportAccepted : Bool
localSinglePeakSymmetryParabolicSupportAccepted = true

SecondaryPeakExclusion : Bool
SecondaryPeakExclusion = false

SecondaryPeakExclusionProved : Bool
SecondaryPeakExclusionProved = false

SecondaryPeakExclusionOpen : Bool
SecondaryPeakExclusionOpen = true

SecondaryPeakExclusionStillObstructed : Bool
SecondaryPeakExclusionStillObstructed = true

nonlinearShoulderFormationExcluded : Bool
nonlinearShoulderFormationExcluded = false

nonlinearShoulderFormationObstructsExclusion : Bool
nonlinearShoulderFormationObstructsExclusion = true

offCenterPositiveVCrossingsExcluded : Bool
offCenterPositiveVCrossingsExcluded = false

offCenterPositiveVCrossingsObstructExclusion : Bool
offCenterPositiveVCrossingsObstructExclusion = true

coupledAxisymmetricZeroNumberSturmTheoremAvailable : Bool
coupledAxisymmetricZeroNumberSturmTheoremAvailable = false

missingCoupledAxisymmetricZeroNumberSturmTheorem : Bool
missingCoupledAxisymmetricZeroNumberSturmTheorem = true

boundaryMigrationControlled : Bool
boundaryMigrationControlled = false

annularMigrationControlled : Bool
annularMigrationControlled = false

boundaryAnnularMigrationObstructsExclusion : Bool
boundaryAnnularMigrationObstructsExclusion = true

compatibleSecondaryPeakConstantsAvailable : Bool
compatibleSecondaryPeakConstantsAvailable = false

compatibleSecondaryPeakTheoremAvailable : Bool
compatibleSecondaryPeakTheoremAvailable = false

absentCompatibleConstantsAndTheorem : Bool
absentCompatibleConstantsAndTheorem = true

globalAxialMonotonicity : Bool
globalAxialMonotonicity = false

globalAxialMonotonicityProved : Bool
globalAxialMonotonicityProved = false

globalAxialMonotonicityPromoted : Bool
globalAxialMonotonicityPromoted = false

fullNavierStokesSolutionConstructed : Bool
fullNavierStokesSolutionConstructed = false

full_clay_ns_solved : Bool
full_clay_ns_solved = false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

sprint143KeepsSecondaryPeakExclusionFalse :
  SecondaryPeakExclusion ≡ false
sprint143KeepsSecondaryPeakExclusionFalse = refl

sprint143KeepsSecondaryPeakExclusionOpen :
  SecondaryPeakExclusionOpen ≡ true
sprint143KeepsSecondaryPeakExclusionOpen = refl

sprint143KeepsGlobalAxialMonotonicityFalse :
  globalAxialMonotonicity ≡ false
sprint143KeepsGlobalAxialMonotonicityFalse = refl

sprint143KeepsFullNSSolutionFalse :
  fullNavierStokesSolutionConstructed ≡ false
sprint143KeepsFullNSSolutionFalse = refl

sprint143KeepsFullClayNSFalse :
  full_clay_ns_solved ≡ false
sprint143KeepsFullClayNSFalse = refl

sprint143KeepsClayPromotionFalse :
  clayNavierStokesPromoted ≡ false
sprint143KeepsClayPromotionFalse = refl

data SecondaryPeakExclusionObstructionStep : Set where
  anchorSprint142GlobalConcavityObstruction :
    SecondaryPeakExclusionObstructionStep

  acceptLocalSinglePeakSupport :
    SecondaryPeakExclusionObstructionStep

  acceptLocalSymmetrySupport :
    SecondaryPeakExclusionObstructionStep

  acceptLocalParabolicSupport :
    SecondaryPeakExclusionObstructionStep

  replaySecondaryPeakExclusionAttempt :
    SecondaryPeakExclusionObstructionStep

  recordNonlinearShoulderFormationObstruction :
    SecondaryPeakExclusionObstructionStep

  recordOffCenterPositiveVCrossingObstruction :
    SecondaryPeakExclusionObstructionStep

  recordMissingCoupledZeroNumberSturmTheorem :
    SecondaryPeakExclusionObstructionStep

  recordBoundaryAnnularMigrationObstruction :
    SecondaryPeakExclusionObstructionStep

  recordAbsentCompatibleConstantsAndTheorem :
    SecondaryPeakExclusionObstructionStep

  refuseGlobalAxialMonotonicity :
    SecondaryPeakExclusionObstructionStep

  refuseFullNavierStokesSolutionClaim :
    SecondaryPeakExclusionObstructionStep

  keepClayPromotionFlagsFalse :
    SecondaryPeakExclusionObstructionStep

canonicalSecondaryPeakExclusionObstructionSteps :
  List SecondaryPeakExclusionObstructionStep
canonicalSecondaryPeakExclusionObstructionSteps =
  anchorSprint142GlobalConcavityObstruction
  ∷ acceptLocalSinglePeakSupport
  ∷ acceptLocalSymmetrySupport
  ∷ acceptLocalParabolicSupport
  ∷ replaySecondaryPeakExclusionAttempt
  ∷ recordNonlinearShoulderFormationObstruction
  ∷ recordOffCenterPositiveVCrossingObstruction
  ∷ recordMissingCoupledZeroNumberSturmTheorem
  ∷ recordBoundaryAnnularMigrationObstruction
  ∷ recordAbsentCompatibleConstantsAndTheorem
  ∷ refuseGlobalAxialMonotonicity
  ∷ refuseFullNavierStokesSolutionClaim
  ∷ keepClayPromotionFlagsFalse
  ∷ []

data SecondaryPeakExclusionObstruction : Set where
  NonlinearShoulderFormationObstruction :
    SecondaryPeakExclusionObstruction

  OffCenterPositiveVCrossingsObstruction :
    SecondaryPeakExclusionObstruction

  MissingCoupledAxisymmetricZeroNumberSturmTheoremObstruction :
    SecondaryPeakExclusionObstruction

  BoundaryAnnularMigrationObstruction :
    SecondaryPeakExclusionObstruction

  AbsentCompatibleConstantsAndTheoremObstruction :
    SecondaryPeakExclusionObstruction

canonicalSecondaryPeakExclusionObstructions :
  List SecondaryPeakExclusionObstruction
canonicalSecondaryPeakExclusionObstructions =
  NonlinearShoulderFormationObstruction
  ∷ OffCenterPositiveVCrossingsObstruction
  ∷ MissingCoupledAxisymmetricZeroNumberSturmTheoremObstruction
  ∷ BoundaryAnnularMigrationObstruction
  ∷ AbsentCompatibleConstantsAndTheoremObstruction
  ∷ []

data SecondaryPeakExclusionOpenBoundary : Set where
  secondaryPeakExclusionNotProvedHere :
    SecondaryPeakExclusionOpenBoundary

  nonlinearShoulderFormationNotExcludedHere :
    SecondaryPeakExclusionOpenBoundary

  offCenterPositiveVCrossingsNotExcludedHere :
    SecondaryPeakExclusionOpenBoundary

  coupledAxisymmetricZeroNumberSturmTheoremAbsentHere :
    SecondaryPeakExclusionOpenBoundary

  boundaryAnnularMigrationNotControlledHere :
    SecondaryPeakExclusionOpenBoundary

  compatibleConstantsAndTheoremAbsentHere :
    SecondaryPeakExclusionOpenBoundary

  noGlobalAxialMonotonicityHere :
    SecondaryPeakExclusionOpenBoundary

  noFullClayNavierStokesSolutionHere :
    SecondaryPeakExclusionOpenBoundary

  noClayPromotionHere :
    SecondaryPeakExclusionOpenBoundary

canonicalSecondaryPeakExclusionOpenBoundaries :
  List SecondaryPeakExclusionOpenBoundary
canonicalSecondaryPeakExclusionOpenBoundaries =
  secondaryPeakExclusionNotProvedHere
  ∷ nonlinearShoulderFormationNotExcludedHere
  ∷ offCenterPositiveVCrossingsNotExcludedHere
  ∷ coupledAxisymmetricZeroNumberSturmTheoremAbsentHere
  ∷ boundaryAnnularMigrationNotControlledHere
  ∷ compatibleConstantsAndTheoremAbsentHere
  ∷ noGlobalAxialMonotonicityHere
  ∷ noFullClayNavierStokesSolutionHere
  ∷ noClayPromotionHere
  ∷ []

data SecondaryPeakExclusionPromotion : Set where

secondaryPeakExclusionPromotionImpossibleHere :
  SecondaryPeakExclusionPromotion →
  ⊥
secondaryPeakExclusionPromotionImpossibleHere ()

sprint142AnchorStatement : String
sprint142AnchorStatement =
  "Sprint143 anchors to canonical Sprint142 global-concavity obstruction receipt"

secondaryPeakAttemptStatement : String
secondaryPeakAttemptStatement =
  "SecondaryPeakExclusion has local single-peak, symmetry, and parabolic support but remains false, open, and globally obstructed"

secondaryPeakObstructionStatement : String
secondaryPeakObstructionStatement =
  "The obstruction is nonlinear shoulder formation, off-center positive v crossings, missing coupled axisymmetric zero-number/Sturm theorem, boundary/annular migration, and absent compatible constants/theorem"

promotionBoundaryStatement : String
promotionBoundaryStatement =
  "No global axial monotonicity, no full Clay Navier-Stokes solution, and no Clay promotion are recorded"

record Sprint142SecondaryPeakExclusionAnchor : Set where
  constructor sprint142SecondaryPeakExclusionAnchorReceipt
  field
    anchorStatement :
      String
    anchorStatementIsCanonical :
      anchorStatement ≡ sprint142AnchorStatement
    sprint142Receipt :
      S142.NSSprint142GlobalConcavityObstructionReceipt
    sprint142ReceiptIsCanonical :
      sprint142Receipt ≡
      S142.canonicalNSSprint142GlobalConcavityObstructionReceipt
    sprint142LedgerClosed :
      S142.sprint142GlobalConcavityObstructionLedgerClosed ≡ true
    sprint142GlobalConcavityStillObstructed :
      S142.GlobalConcavityOfPsi1StillObstructed ≡ true
    sprint142NoGlobalAxialMonotonicity :
      S142.globalAxialMonotonicityPromoted ≡ false
    sprint142NoFullNSSolution :
      S142.fullNavierStokesSolutionConstructed ≡ false
    sprint142NoFullClayNS :
      S142.full_clay_ns_solved ≡ false
    sprint142NoClayPromotion :
      S142.clayNavierStokesPromoted ≡ false

open Sprint142SecondaryPeakExclusionAnchor public

canonicalSprint142SecondaryPeakExclusionAnchor :
  Sprint142SecondaryPeakExclusionAnchor
canonicalSprint142SecondaryPeakExclusionAnchor =
  sprint142SecondaryPeakExclusionAnchorReceipt
    sprint142AnchorStatement
    refl
    S142.canonicalNSSprint142GlobalConcavityObstructionReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl

record LocalSinglePeakSymmetryParabolicSupport : Set where
  constructor localSinglePeakSymmetryParabolicSupportReceipt
  field
    supportStatement :
      String
    supportStatementIsCanonical :
      supportStatement ≡ secondaryPeakAttemptStatement
    localSinglePeakSupportField :
      localSinglePeakSupport ≡ true
    localSymmetrySupportField :
      localSymmetrySupport ≡ true
    localParabolicSupportField :
      localParabolicSupport ≡ true
    localSupportAcceptedField :
      localSinglePeakSymmetryParabolicSupportAccepted ≡ true

open LocalSinglePeakSymmetryParabolicSupport public

canonicalLocalSinglePeakSymmetryParabolicSupport :
  LocalSinglePeakSymmetryParabolicSupport
canonicalLocalSinglePeakSymmetryParabolicSupport =
  localSinglePeakSymmetryParabolicSupportReceipt
    secondaryPeakAttemptStatement
    refl
    refl
    refl
    refl
    refl

record SecondaryPeakExclusionAttemptBoundary : Set where
  constructor secondaryPeakExclusionAttemptBoundaryReceipt
  field
    attemptStatement :
      String
    attemptStatementIsCanonical :
      attemptStatement ≡ secondaryPeakAttemptStatement
    secondaryPeakExclusionField :
      SecondaryPeakExclusion ≡ false
    secondaryPeakExclusionProvedField :
      SecondaryPeakExclusionProved ≡ false
    secondaryPeakExclusionOpenField :
      SecondaryPeakExclusionOpen ≡ true
    secondaryPeakExclusionStillObstructedField :
      SecondaryPeakExclusionStillObstructed ≡ true

open SecondaryPeakExclusionAttemptBoundary public

canonicalSecondaryPeakExclusionAttemptBoundary :
  SecondaryPeakExclusionAttemptBoundary
canonicalSecondaryPeakExclusionAttemptBoundary =
  secondaryPeakExclusionAttemptBoundaryReceipt
    secondaryPeakAttemptStatement
    refl
    refl
    refl
    refl
    refl

record FiveSecondaryPeakExclusionObstructions : Set where
  constructor fiveSecondaryPeakExclusionObstructionsReceipt
  field
    blockerStatement :
      String
    blockerStatementIsCanonical :
      blockerStatement ≡ secondaryPeakObstructionStatement
    obstructions :
      List SecondaryPeakExclusionObstruction
    obstructionsAreCanonical :
      obstructions ≡ canonicalSecondaryPeakExclusionObstructions
    nonlinearShoulderFormationExcludedField :
      nonlinearShoulderFormationExcluded ≡ false
    nonlinearShoulderFormationObstructsExclusionField :
      nonlinearShoulderFormationObstructsExclusion ≡ true
    offCenterPositiveVCrossingsExcludedField :
      offCenterPositiveVCrossingsExcluded ≡ false
    offCenterPositiveVCrossingsObstructExclusionField :
      offCenterPositiveVCrossingsObstructExclusion ≡ true
    coupledAxisymmetricZeroNumberSturmTheoremAvailableField :
      coupledAxisymmetricZeroNumberSturmTheoremAvailable ≡ false
    missingCoupledAxisymmetricZeroNumberSturmTheoremField :
      missingCoupledAxisymmetricZeroNumberSturmTheorem ≡ true
    boundaryMigrationControlledField :
      boundaryMigrationControlled ≡ false
    annularMigrationControlledField :
      annularMigrationControlled ≡ false
    boundaryAnnularMigrationObstructsExclusionField :
      boundaryAnnularMigrationObstructsExclusion ≡ true
    compatibleConstantsAvailableField :
      compatibleSecondaryPeakConstantsAvailable ≡ false
    compatibleTheoremAvailableField :
      compatibleSecondaryPeakTheoremAvailable ≡ false
    absentCompatibleConstantsAndTheoremField :
      absentCompatibleConstantsAndTheorem ≡ true

open FiveSecondaryPeakExclusionObstructions public

canonicalFiveSecondaryPeakExclusionObstructions :
  FiveSecondaryPeakExclusionObstructions
canonicalFiveSecondaryPeakExclusionObstructions =
  fiveSecondaryPeakExclusionObstructionsReceipt
    secondaryPeakObstructionStatement
    refl
    canonicalSecondaryPeakExclusionObstructions
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

record FailClosedSecondaryPeakExclusionBoundary : Set where
  constructor failClosedSecondaryPeakExclusionBoundaryReceipt
  field
    boundaryStatement :
      String
    boundaryStatementIsCanonical :
      boundaryStatement ≡ promotionBoundaryStatement
    openBoundaries :
      List SecondaryPeakExclusionOpenBoundary
    openBoundariesAreCanonical :
      openBoundaries ≡ canonicalSecondaryPeakExclusionOpenBoundaries
    globalAxialMonotonicityField :
      globalAxialMonotonicity ≡ false
    globalAxialMonotonicityProvedField :
      globalAxialMonotonicityProved ≡ false
    globalAxialMonotonicityPromotedField :
      globalAxialMonotonicityPromoted ≡ false
    fullNavierStokesSolutionConstructedField :
      fullNavierStokesSolutionConstructed ≡ false
    fullClayNSSolvedField :
      full_clay_ns_solved ≡ false
    clayPromotionField :
      clayNavierStokesPromoted ≡ false
    promotionFlags :
      List SecondaryPeakExclusionPromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []
    noPromotionPossibleHere :
      SecondaryPeakExclusionPromotion →
      ⊥

open FailClosedSecondaryPeakExclusionBoundary public

canonicalFailClosedSecondaryPeakExclusionBoundary :
  FailClosedSecondaryPeakExclusionBoundary
canonicalFailClosedSecondaryPeakExclusionBoundary =
  failClosedSecondaryPeakExclusionBoundaryReceipt
    promotionBoundaryStatement
    refl
    canonicalSecondaryPeakExclusionOpenBoundaries
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    []
    refl
    secondaryPeakExclusionPromotionImpossibleHere

record Sprint143SecondaryPeakExclusionObstructionStatuses : Set where
  constructor sprint143SecondaryPeakExclusionObstructionStatuses
  field
    ledgerClosedField :
      sprint143SecondaryPeakExclusionObstructionLedgerClosed ≡ true
    sprint142AnchoredField :
      sprint142GlobalConcavityObstructionAnchored ≡ true
    attemptRecordedField :
      SecondaryPeakExclusionAttemptRecorded ≡ true
    localSinglePeakSupportField :
      localSinglePeakSupport ≡ true
    localSymmetrySupportField :
      localSymmetrySupport ≡ true
    localParabolicSupportField :
      localParabolicSupport ≡ true
    localSupportAcceptedField :
      localSinglePeakSymmetryParabolicSupportAccepted ≡ true
    secondaryPeakExclusionField :
      SecondaryPeakExclusion ≡ false
    secondaryPeakExclusionProvedField :
      SecondaryPeakExclusionProved ≡ false
    secondaryPeakExclusionOpenField :
      SecondaryPeakExclusionOpen ≡ true
    secondaryPeakExclusionStillObstructedField :
      SecondaryPeakExclusionStillObstructed ≡ true
    nonlinearShoulderFormationExcludedField :
      nonlinearShoulderFormationExcluded ≡ false
    nonlinearShoulderFormationObstructsExclusionField :
      nonlinearShoulderFormationObstructsExclusion ≡ true
    offCenterPositiveVCrossingsExcludedField :
      offCenterPositiveVCrossingsExcluded ≡ false
    offCenterPositiveVCrossingsObstructExclusionField :
      offCenterPositiveVCrossingsObstructExclusion ≡ true
    coupledAxisymmetricZeroNumberSturmTheoremAvailableField :
      coupledAxisymmetricZeroNumberSturmTheoremAvailable ≡ false
    missingCoupledAxisymmetricZeroNumberSturmTheoremField :
      missingCoupledAxisymmetricZeroNumberSturmTheorem ≡ true
    boundaryMigrationControlledField :
      boundaryMigrationControlled ≡ false
    annularMigrationControlledField :
      annularMigrationControlled ≡ false
    boundaryAnnularMigrationObstructsExclusionField :
      boundaryAnnularMigrationObstructsExclusion ≡ true
    compatibleConstantsAvailableField :
      compatibleSecondaryPeakConstantsAvailable ≡ false
    compatibleTheoremAvailableField :
      compatibleSecondaryPeakTheoremAvailable ≡ false
    absentCompatibleConstantsAndTheoremField :
      absentCompatibleConstantsAndTheorem ≡ true
    globalAxialMonotonicityField :
      globalAxialMonotonicity ≡ false
    globalAxialMonotonicityProvedField :
      globalAxialMonotonicityProved ≡ false
    globalAxialMonotonicityPromotedField :
      globalAxialMonotonicityPromoted ≡ false
    fullNavierStokesSolutionConstructedField :
      fullNavierStokesSolutionConstructed ≡ false
    fullClayNSSolvedField :
      full_clay_ns_solved ≡ false
    clayPromotionField :
      clayNavierStokesPromoted ≡ false

open Sprint143SecondaryPeakExclusionObstructionStatuses public

canonicalSprint143SecondaryPeakExclusionObstructionStatuses :
  Sprint143SecondaryPeakExclusionObstructionStatuses
canonicalSprint143SecondaryPeakExclusionObstructionStatuses =
  sprint143SecondaryPeakExclusionObstructionStatuses
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

record NSSprint143SecondaryPeakExclusionObstructionReceipt : Set where
  constructor nsSprint143SecondaryPeakExclusionObstructionReceipt
  field
    sprint142Anchor :
      Sprint142SecondaryPeakExclusionAnchor
    localSupport :
      LocalSinglePeakSymmetryParabolicSupport
    attemptBoundary :
      SecondaryPeakExclusionAttemptBoundary
    obstructions :
      FiveSecondaryPeakExclusionObstructions
    failClosedBoundary :
      FailClosedSecondaryPeakExclusionBoundary
    statuses :
      Sprint143SecondaryPeakExclusionObstructionStatuses
    statusesAreCanonical :
      statuses ≡ canonicalSprint143SecondaryPeakExclusionObstructionStatuses
    steps :
      List SecondaryPeakExclusionObstructionStep
    stepsAreCanonical :
      steps ≡ canonicalSecondaryPeakExclusionObstructionSteps
    receiptSummary :
      String
    receiptSummaryIsCanonical :
      receiptSummary
      ≡
      "Sprint143 anchors to Sprint142 and records SecondaryPeakExclusion as false/open: local single-peak, symmetry, and parabolic support are true, but global exclusion remains obstructed by nonlinear shoulder formation, off-center positive v crossings, missing coupled axisymmetric zero-number/Sturm theorem, boundary/annular migration, and absent compatible constants/theorem; globalAxialMonotonicity, full_clay_ns_solved, and clayNavierStokesPromoted remain false."

open NSSprint143SecondaryPeakExclusionObstructionReceipt public

canonicalNSSprint143SecondaryPeakExclusionObstructionReceipt :
  NSSprint143SecondaryPeakExclusionObstructionReceipt
canonicalNSSprint143SecondaryPeakExclusionObstructionReceipt =
  nsSprint143SecondaryPeakExclusionObstructionReceipt
    canonicalSprint142SecondaryPeakExclusionAnchor
    canonicalLocalSinglePeakSymmetryParabolicSupport
    canonicalSecondaryPeakExclusionAttemptBoundary
    canonicalFiveSecondaryPeakExclusionObstructions
    canonicalFailClosedSecondaryPeakExclusionBoundary
    canonicalSprint143SecondaryPeakExclusionObstructionStatuses
    refl
    canonicalSecondaryPeakExclusionObstructionSteps
    refl
    "Sprint143 anchors to Sprint142 and records SecondaryPeakExclusion as false/open: local single-peak, symmetry, and parabolic support are true, but global exclusion remains obstructed by nonlinear shoulder formation, off-center positive v crossings, missing coupled axisymmetric zero-number/Sturm theorem, boundary/annular migration, and absent compatible constants/theorem; globalAxialMonotonicity, full_clay_ns_solved, and clayNavierStokesPromoted remain false."
    refl

sprint143SecondaryPeakExclusionObstructionSummary :
  Sprint142SecondaryPeakExclusionAnchor
  × LocalSinglePeakSymmetryParabolicSupport
  × SecondaryPeakExclusionAttemptBoundary
  × FiveSecondaryPeakExclusionObstructions
  × FailClosedSecondaryPeakExclusionBoundary
  × Sprint143SecondaryPeakExclusionObstructionStatuses
sprint143SecondaryPeakExclusionObstructionSummary =
  canonicalSprint142SecondaryPeakExclusionAnchor ,
  canonicalLocalSinglePeakSymmetryParabolicSupport ,
  canonicalSecondaryPeakExclusionAttemptBoundary ,
  canonicalFiveSecondaryPeakExclusionObstructions ,
  canonicalFailClosedSecondaryPeakExclusionBoundary ,
  canonicalSprint143SecondaryPeakExclusionObstructionStatuses

sprint143AllRequiredStatuses :
  (sprint143SecondaryPeakExclusionObstructionLedgerClosed ≡ true)
  × (sprint142GlobalConcavityObstructionAnchored ≡ true)
  × (SecondaryPeakExclusionAttemptRecorded ≡ true)
  × (localSinglePeakSupport ≡ true)
  × (localSymmetrySupport ≡ true)
  × (localParabolicSupport ≡ true)
  × (localSinglePeakSymmetryParabolicSupportAccepted ≡ true)
  × (SecondaryPeakExclusion ≡ false)
  × (SecondaryPeakExclusionProved ≡ false)
  × (SecondaryPeakExclusionOpen ≡ true)
  × (SecondaryPeakExclusionStillObstructed ≡ true)
  × (nonlinearShoulderFormationExcluded ≡ false)
  × (nonlinearShoulderFormationObstructsExclusion ≡ true)
  × (offCenterPositiveVCrossingsExcluded ≡ false)
  × (offCenterPositiveVCrossingsObstructExclusion ≡ true)
  × (coupledAxisymmetricZeroNumberSturmTheoremAvailable ≡ false)
  × (missingCoupledAxisymmetricZeroNumberSturmTheorem ≡ true)
  × (boundaryMigrationControlled ≡ false)
  × (annularMigrationControlled ≡ false)
  × (boundaryAnnularMigrationObstructsExclusion ≡ true)
  × (compatibleSecondaryPeakConstantsAvailable ≡ false)
  × (compatibleSecondaryPeakTheoremAvailable ≡ false)
  × (absentCompatibleConstantsAndTheorem ≡ true)
  × (globalAxialMonotonicity ≡ false)
  × (globalAxialMonotonicityProved ≡ false)
  × (globalAxialMonotonicityPromoted ≡ false)
  × (fullNavierStokesSolutionConstructed ≡ false)
  × (full_clay_ns_solved ≡ false)
  × (clayNavierStokesPromoted ≡ false)
sprint143AllRequiredStatuses =
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl
