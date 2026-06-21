module DASHI.Physics.Closure.NSAlignmentProjectionODEReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- Fail-closed receipt for the exact eigenframe projection ODE lane.
--
-- This module records the qualitative ledger for the exact eigenframe
-- projection ODE on omega_j and the derived Dt(omega_1^2 - omega_3^2)
-- structure.  The ledger keeps three ingredients separate:
--
--   * the eigenvalue spreading term;
--   * the pressure/viscous correction;
--   * the rotation-term cancellation recorded explicitly.
--
-- No promoted theorem is claimed.  The file exists only as a local
-- receipt and blocker ledger.

data Void : Set where

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

------------------------------------------------------------------------
-- Canonical receipt status, stages, assumptions, and blockers.

data NSAlignmentProjectionODEStatus : Set where
  receiptRecorded :
    NSAlignmentProjectionODEStatus

data NSAlignmentProjectionODEStage : Set where
  exactEigenframeProjectionEquationRecorded :
    NSAlignmentProjectionODEStage
  omegaJComponentwiseReadoutRecorded :
    NSAlignmentProjectionODEStage
  squaredDifferenceDtStructureRecorded :
    NSAlignmentProjectionODEStage
  eigenvalueSpreadingTermIsolated :
    NSAlignmentProjectionODEStage
  pressureViscousCorrectionIsolated :
    NSAlignmentProjectionODEStage
  rotationTermCancellationRecorded :
    NSAlignmentProjectionODEStage
  qualitativeAbsorptionRouteRecorded :
    NSAlignmentProjectionODEStage
  theoremPromotionBlockedRecorded :
    NSAlignmentProjectionODEStage

canonicalNSAlignmentProjectionODEStages :
  List NSAlignmentProjectionODEStage
canonicalNSAlignmentProjectionODEStages =
  exactEigenframeProjectionEquationRecorded
  ∷ omegaJComponentwiseReadoutRecorded
  ∷ squaredDifferenceDtStructureRecorded
  ∷ eigenvalueSpreadingTermIsolated
  ∷ pressureViscousCorrectionIsolated
  ∷ rotationTermCancellationRecorded
  ∷ qualitativeAbsorptionRouteRecorded
  ∷ theoremPromotionBlockedRecorded
  ∷ []

NSAlignmentProjectionODEStageCount : Nat
NSAlignmentProjectionODEStageCount =
  listLength canonicalNSAlignmentProjectionODEStages

NSAlignmentProjectionODEStageCountIs8 :
  NSAlignmentProjectionODEStageCount ≡ 8
NSAlignmentProjectionODEStageCountIs8 = refl

data NSAlignmentProjectionODEAssumption : Set where
  exactStrainEigenframeAvailable :
    NSAlignmentProjectionODEAssumption
  eigenvaluesOrderedLambda1ToLambda3 :
    NSAlignmentProjectionODEAssumption
  projectionIndexedByOmegaJ :
    NSAlignmentProjectionODEAssumption
  pressureAndViscosityKeptAsResidualCorrection :
    NSAlignmentProjectionODEAssumption
  frameRotationContributionTracked :
    NSAlignmentProjectionODEAssumption
  rotationCancellationReadAsLedgerEquality :
    NSAlignmentProjectionODEAssumption

canonicalNSAlignmentProjectionODEAssumptions :
  List NSAlignmentProjectionODEAssumption
canonicalNSAlignmentProjectionODEAssumptions =
  exactStrainEigenframeAvailable
  ∷ eigenvaluesOrderedLambda1ToLambda3
  ∷ projectionIndexedByOmegaJ
  ∷ pressureAndViscosityKeptAsResidualCorrection
  ∷ frameRotationContributionTracked
  ∷ rotationCancellationReadAsLedgerEquality
  ∷ []

NSAlignmentProjectionODEAssumptionCount : Nat
NSAlignmentProjectionODEAssumptionCount =
  listLength canonicalNSAlignmentProjectionODEAssumptions

NSAlignmentProjectionODEAssumptionCountIs6 :
  NSAlignmentProjectionODEAssumptionCount ≡ 6
NSAlignmentProjectionODEAssumptionCountIs6 = refl

data NSAlignmentProjectionODEBlocker : Set where
  noPromotedExactFormula :
    NSAlignmentProjectionODEBlocker
  noClosedPressureViscousSignControl :
    NSAlignmentProjectionODEBlocker
  noClosedRotationToEigenvalueTransfer :
    NSAlignmentProjectionODEBlocker
  noDerivedMonotoneControlForSquaredDifference :
    NSAlignmentProjectionODEBlocker
  noClayPromotionFromThisReceipt :
    NSAlignmentProjectionODEBlocker

canonicalNSAlignmentProjectionODEBlockers :
  List NSAlignmentProjectionODEBlocker
canonicalNSAlignmentProjectionODEBlockers =
  noPromotedExactFormula
  ∷ noClosedPressureViscousSignControl
  ∷ noClosedRotationToEigenvalueTransfer
  ∷ noDerivedMonotoneControlForSquaredDifference
  ∷ noClayPromotionFromThisReceipt
  ∷ []

NSAlignmentProjectionODEBlockerCount : Nat
NSAlignmentProjectionODEBlockerCount =
  listLength canonicalNSAlignmentProjectionODEBlockers

NSAlignmentProjectionODEBlockerCountIs5 :
  NSAlignmentProjectionODEBlockerCount ≡ 5
NSAlignmentProjectionODEBlockerCountIs5 = refl

------------------------------------------------------------------------
-- Canonical ledger text.

exactEigenframeProjectionEquationText : String
exactEigenframeProjectionEquationText =
  "Exact eigenframe projection ODE: D_t omega_j is recorded componentwise in the strain eigenframe, with the frame-rotation contribution tracked separately from the residual pressure/viscous correction."

omegaJComponentwiseText : String
omegaJComponentwiseText =
  "omega_j lane: the projection is indexed by j, not collapsed to a scalar surrogate; the ledger keeps each component available for later comparison."

squaredDifferenceDtStructureText : String
squaredDifferenceDtStructureText =
  "Dt(omega_1^2 - omega_3^2) structure: the derivative is tracked as a signed difference ledger rather than a closed estimate."

eigenvalueSpreadingTermText : String
eigenvalueSpreadingTermText =
  "eigenvalue spreading term: the leading strain-eigenvalue separation contribution is isolated as the growth/shaping driver in the difference ledger."

pressureViscousCorrectionText : String
pressureViscousCorrectionText =
  "pressure/viscous correction: the non-spreading residual is kept qualitative and is not converted into a closed sign estimate here."

rotationTermCancellationText : String
rotationTermCancellationText =
  "rotation-term cancellation: the eigenframe rotation piece is recorded explicitly as cancelling in the Dt(omega_1^2 - omega_3^2) bookkeeping."

qualitativeAbsorptionRouteText : String
qualitativeAbsorptionRouteText =
  "qualitative absorption route: any future closure would need a separate sign or domination input for the pressure/viscous correction after rotation cancellation is accounted for."

receiptBoundaryText : String
receiptBoundaryText =
  "This receipt records the exact eigenframe projection ODE lane and the Dt(omega_1^2 - omega_3^2) decomposition qualitatively: componentwise omega_j projection, eigenvalue spreading term, pressure/viscous correction, and explicit rotation-term cancellation. It is fail-closed and does not promote a theorem."

------------------------------------------------------------------------
-- O/R/C/S/L/P/G/F strings.

organizationString : String
organizationString =
  "O: Worker lane 3 records the exact eigenframe projection ODE as a fail-closed Navier--Stokes receipt."

requirementString : String
requirementString =
  "R: Keep the omega_j projection lane exact in the strain eigenframe, and record Dt(omega_1^2 - omega_3^2) as eigenvalue spreading plus pressure/viscous correction with explicit rotation-term cancellation."

codeArtifactString : String
codeArtifactString =
  "C: This standalone Agda file owns only the local stage ledger, assumption ledger, blocker ledger, canonical strings, and the non-promoting receipt boundary."

stateString : String
stateString =
  "S: The exact projection ODE, the squared-difference derivative structure, and the rotation cancellation are recorded; theorem promotion and Clay promotion stay false."

latticeString : String
latticeString =
  "L: strain eigenframe -> componentwise omega_j projection -> Dt(omega_1^2 - omega_3^2) -> eigenvalue spreading term + pressure/viscous correction -> explicit rotation-term cancellation -> blocked promotion."

proposalString : String
proposalString =
  "P: Treat this as a ledger surface only; any promotion would require a separate theorem-bearing module with closed analytic control."

governanceString : String
governanceString =
  "G: Fail closed: the module records the qualitative decomposition and the cancellation ledger, but does not claim a closed estimate or theorem."

gapString : String
gapString =
  "F: Remaining gap is a closed estimate for the pressure/viscous correction after the rotation contribution has been canceled; no theorem promotion is discharged here."

record NSAlignmentProjectionODEORCSLPGF : Set where
  constructor mkNSAlignmentProjectionODEORCSLPGF
  field
    O : String
    OIsCanonical : O ≡ organizationString
    R : String
    RIsCanonical : R ≡ requirementString
    C : String
    CIsCanonical : C ≡ codeArtifactString
    S : String
    SIsCanonical : S ≡ stateString
    L : String
    LIsCanonical : L ≡ latticeString
    P : String
    PIsCanonical : P ≡ proposalString
    G : String
    GIsCanonical : G ≡ governanceString
    F : String
    FIsCanonical : F ≡ gapString

canonicalNSAlignmentProjectionODEORCSLPGF :
  NSAlignmentProjectionODEORCSLPGF
canonicalNSAlignmentProjectionODEORCSLPGF =
  mkNSAlignmentProjectionODEORCSLPGF
    organizationString
    refl
    requirementString
    refl
    codeArtifactString
    refl
    stateString
    refl
    latticeString
    refl
    proposalString
    refl
    governanceString
    refl
    gapString
    refl

------------------------------------------------------------------------
-- Receipt record.

data NSAlignmentProjectionODEPromotion : Set where

nsAlignmentProjectionODEPromotionImpossibleHere :
  NSAlignmentProjectionODEPromotion →
  Void
nsAlignmentProjectionODEPromotionImpossibleHere ()

record NSAlignmentProjectionODEReceipt : Setω where
  field
    status :
      NSAlignmentProjectionODEStatus
    statusIsCanonical :
      status ≡ receiptRecorded

    stageLedger :
      List NSAlignmentProjectionODEStage
    stageLedgerIsCanonical :
      stageLedger ≡ canonicalNSAlignmentProjectionODEStages

    assumptionLedger :
      List NSAlignmentProjectionODEAssumption
    assumptionLedgerIsCanonical :
      assumptionLedger ≡ canonicalNSAlignmentProjectionODEAssumptions

    exactEigenframeProjectionEquation :
      String
    exactEigenframeProjectionEquationIsCanonical :
      exactEigenframeProjectionEquation ≡
      exactEigenframeProjectionEquationText

    omegaJComponentwiseReadout :
      String
    omegaJComponentwiseReadoutIsCanonical :
      omegaJComponentwiseReadout ≡ omegaJComponentwiseText

    squaredDifferenceDtStructure :
      String
    squaredDifferenceDtStructureIsCanonical :
      squaredDifferenceDtStructure ≡ squaredDifferenceDtStructureText

    eigenvalueSpreadingTerm :
      String
    eigenvalueSpreadingTermIsCanonical :
      eigenvalueSpreadingTerm ≡ eigenvalueSpreadingTermText

    pressureViscousCorrection :
      String
    pressureViscousCorrectionIsCanonical :
      pressureViscousCorrection ≡ pressureViscousCorrectionText

    rotationTermCancellation :
      String
    rotationTermCancellationIsCanonical :
      rotationTermCancellation ≡ rotationTermCancellationText

    qualitativeAbsorptionRoute :
      String
    qualitativeAbsorptionRouteIsCanonical :
      qualitativeAbsorptionRoute ≡ qualitativeAbsorptionRouteText

    stageCountIsCanonical :
      NSAlignmentProjectionODEStageCount ≡ 8

    assumptionCountIsCanonical :
      NSAlignmentProjectionODEAssumptionCount ≡ 6

    blockerLedger :
      List NSAlignmentProjectionODEBlocker
    blockerLedgerIsCanonical :
      blockerLedger ≡ canonicalNSAlignmentProjectionODEBlockers

    blockerCountIsCanonical :
      NSAlignmentProjectionODEBlockerCount ≡ 5

    theoremPromoted :
      Bool
    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

    oracleBoundaryText :
      String
    oracleBoundaryTextIsCanonical :
      oracleBoundaryText ≡ receiptBoundaryText

    orcslpgf :
      NSAlignmentProjectionODEORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSAlignmentProjectionODEORCSLPGF

open NSAlignmentProjectionODEReceipt public

canonicalNSAlignmentProjectionODEReceipt :
  NSAlignmentProjectionODEReceipt
canonicalNSAlignmentProjectionODEReceipt =
  record
    { status = receiptRecorded
    ; statusIsCanonical = refl
    ; stageLedger = canonicalNSAlignmentProjectionODEStages
    ; stageLedgerIsCanonical = refl
    ; assumptionLedger = canonicalNSAlignmentProjectionODEAssumptions
    ; assumptionLedgerIsCanonical = refl
    ; exactEigenframeProjectionEquation =
        exactEigenframeProjectionEquationText
    ; exactEigenframeProjectionEquationIsCanonical = refl
    ; omegaJComponentwiseReadout = omegaJComponentwiseText
    ; omegaJComponentwiseReadoutIsCanonical = refl
    ; squaredDifferenceDtStructure = squaredDifferenceDtStructureText
    ; squaredDifferenceDtStructureIsCanonical = refl
    ; eigenvalueSpreadingTerm = eigenvalueSpreadingTermText
    ; eigenvalueSpreadingTermIsCanonical = refl
    ; pressureViscousCorrection = pressureViscousCorrectionText
    ; pressureViscousCorrectionIsCanonical = refl
    ; rotationTermCancellation = rotationTermCancellationText
    ; rotationTermCancellationIsCanonical = refl
    ; qualitativeAbsorptionRoute = qualitativeAbsorptionRouteText
    ; qualitativeAbsorptionRouteIsCanonical = refl
    ; stageCountIsCanonical = refl
    ; assumptionCountIsCanonical = refl
    ; blockerLedger = canonicalNSAlignmentProjectionODEBlockers
    ; blockerLedgerIsCanonical = refl
    ; blockerCountIsCanonical = refl
    ; theoremPromoted = false
    ; theoremPromotedIsFalse = refl
    ; clayPromoted = false
    ; clayPromotedIsFalse = refl
    ; oracleBoundaryText = receiptBoundaryText
    ; oracleBoundaryTextIsCanonical = refl
    ; orcslpgf = canonicalNSAlignmentProjectionODEORCSLPGF
    ; orcslpgfIsCanonical = refl
    }
