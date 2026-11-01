module DASHI.Physics.Closure.NSQuantitativeMassOutsideZeroModesBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSMicrolocalDefectMassConstructionBoundary as Micro
import DASHI.Physics.Closure.NSZeroModeSetClassificationBoundary as Zero

------------------------------------------------------------------------
-- Quantitative mass outside NS zero modes boundary.
--
-- Qualitative great-circle geometry says a singular high-vorticity
-- direction set cannot be fully trapped in the leakage-zero curves.  This
-- module records the sharper remaining analytic gap:
--
--   blowup critical residual
--     -> LP / semiclassical defect measure
--     -> quantitative LRT-to-measure transfer
--     -> positive mass on S^2 \ Z_NS
--     -> residual depletion
--
-- Target estimate, recorded as data and text:
--
--   mu(S^2 \ Z_NS) >= c(epsilon0, C0) > 0
--
-- This is a boundary module only.  It consumes the microlocal defect-mass
-- construction boundary and the zero-mode set classification boundary.
-- It does not prove LP tightness, pressure nonlocality bootstrap,
-- quantitative great-circle-to-measure transfer, residual depletion,
-- full local defect monotonicity, mechanism exhaustion, or Clay NS.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Carriers for the sharpened target.

data CriticalResidualLowerBoundCarrier : Set where
  epsilonZeroPositiveCriticalResidual :
    CriticalResidualLowerBoundCarrier

data GreatCircleAvoidanceWitnessCarrier : Set where
  zeroModeCurvesMissGreatCircleC0 :
    Zero.NSZeroModeSet →
    GreatCircleAvoidanceWitnessCarrier

data QuantitativeConstantCarrier : Set where
  cEpsilonZeroC0Positive :
    CriticalResidualLowerBoundCarrier →
    GreatCircleAvoidanceWitnessCarrier →
    QuantitativeConstantCarrier

data OutsideZeroModeRegionCarrier : Set where
  sphereTwoComplementOfZNS :
    List Zero.NSZeroModeSet →
    OutsideZeroModeRegionCarrier

data QuantitativeMassEstimateTarget : Set where
  muOutsideZNSBoundedBelow :
    Micro.SemiclassicalDefectMeasureCarrier →
    OutsideZeroModeRegionCarrier →
    QuantitativeConstantCarrier →
    QuantitativeMassEstimateTarget

canonicalCriticalResidualLowerBound :
  CriticalResidualLowerBoundCarrier
canonicalCriticalResidualLowerBound =
  epsilonZeroPositiveCriticalResidual

canonicalGreatCircleAvoidanceWitness :
  GreatCircleAvoidanceWitnessCarrier
canonicalGreatCircleAvoidanceWitness =
  zeroModeCurvesMissGreatCircleC0 Zero.canonicalRadialZeroModeSet

canonicalQuantitativeConstant :
  QuantitativeConstantCarrier
canonicalQuantitativeConstant =
  cEpsilonZeroC0Positive
    canonicalCriticalResidualLowerBound
    canonicalGreatCircleAvoidanceWitness

canonicalOutsideZeroModeRegion :
  OutsideZeroModeRegionCarrier
canonicalOutsideZeroModeRegion =
  sphereTwoComplementOfZNS Zero.canonicalNSZeroModeSetComponents

canonicalQuantitativeMassEstimateTarget :
  QuantitativeMassEstimateTarget
canonicalQuantitativeMassEstimateTarget =
  muOutsideZNSBoundedBelow
    Micro.canonicalDefectMeasure
    canonicalOutsideZeroModeRegion
    canonicalQuantitativeConstant

targetEstimateText : String
targetEstimateText =
  "mu(S^2 \\ Z_NS) >= c(epsilon0, C0) > 0"

qualitativeGeometryText : String
qualitativeGeometryText =
  "Qualitative LRT/great-circle geometry blocks complete trapping in zero-mode curves; it does not by itself supply quantitative defect-measure mass."

quantitativeGapText : String
quantitativeGapText =
  "Remaining analytic gap: transfer blowup critical residual and LP/semiclassical compactness into positive mass on S^2 minus Z_NS."

------------------------------------------------------------------------
-- Lattice of proof stages.

data QuantitativeMassStage : Set where
  criticalResidualLowerBoundStage :
    QuantitativeMassStage
  zeroModeCurvesMissGreatCircleStage :
    QuantitativeMassStage
  lpLocalizedVorticityTightnessStage :
    QuantitativeMassStage
  semiclassicalDefectMeasureStage :
    QuantitativeMassStage
  pressureNonlocalityBootstrapStage :
    QuantitativeMassStage
  quantitativeLRTToMeasureTransferStage :
    QuantitativeMassStage
  positiveMassOutsideZeroModesStage :
    QuantitativeMassStage
  leakageConsumerStage :
    QuantitativeMassStage
  residualDepletionStage :
    QuantitativeMassStage
  fullLocalDefectMonotonicityStage :
    QuantitativeMassStage
  mechanismExhaustionStage :
    QuantitativeMassStage

canonicalQuantitativeMassStages :
  List QuantitativeMassStage
canonicalQuantitativeMassStages =
  criticalResidualLowerBoundStage
  ∷ zeroModeCurvesMissGreatCircleStage
  ∷ lpLocalizedVorticityTightnessStage
  ∷ semiclassicalDefectMeasureStage
  ∷ pressureNonlocalityBootstrapStage
  ∷ quantitativeLRTToMeasureTransferStage
  ∷ positiveMassOutsideZeroModesStage
  ∷ leakageConsumerStage
  ∷ residualDepletionStage
  ∷ fullLocalDefectMonotonicityStage
  ∷ mechanismExhaustionStage
  ∷ []

quantitativeMassStageCount : Nat
quantitativeMassStageCount =
  listLength canonicalQuantitativeMassStages

quantitativeMassStageCountIs11 :
  quantitativeMassStageCount ≡ 11
quantitativeMassStageCountIs11 =
  refl

------------------------------------------------------------------------
-- Blockers and support rows.

data QuantitativeMassOutsideZeroModesBlocker : Set where
  missingBlowupProfileCompactness :
    QuantitativeMassOutsideZeroModesBlocker
  missingLittlewoodPaleyTightness :
    QuantitativeMassOutsideZeroModesBlocker
  missingPressureNonlocalityBootstrap :
    QuantitativeMassOutsideZeroModesBlocker
  missingQuantitativeLRTToMeasureTransfer :
    QuantitativeMassOutsideZeroModesBlocker
  missingPositiveMassOutsideZeroModeCurves :
    QuantitativeMassOutsideZeroModesBlocker
  missingLeakageConsumerFromPositiveOutsideMass :
    QuantitativeMassOutsideZeroModesBlocker
  missingResidualDepletion :
    QuantitativeMassOutsideZeroModesBlocker
  missingFullLocalDefectMonotonicity :
    QuantitativeMassOutsideZeroModesBlocker
  missingMechanismExhaustionForFullClayNS :
    QuantitativeMassOutsideZeroModesBlocker
  clayNavierStokesPromotionClosed :
    QuantitativeMassOutsideZeroModesBlocker

canonicalQuantitativeMassBlockers :
  List QuantitativeMassOutsideZeroModesBlocker
canonicalQuantitativeMassBlockers =
  missingBlowupProfileCompactness
  ∷ missingLittlewoodPaleyTightness
  ∷ missingPressureNonlocalityBootstrap
  ∷ missingQuantitativeLRTToMeasureTransfer
  ∷ missingPositiveMassOutsideZeroModeCurves
  ∷ missingLeakageConsumerFromPositiveOutsideMass
  ∷ missingResidualDepletion
  ∷ missingFullLocalDefectMonotonicity
  ∷ missingMechanismExhaustionForFullClayNS
  ∷ clayNavierStokesPromotionClosed
  ∷ []

quantitativeMassBlockerCount : Nat
quantitativeMassBlockerCount =
  listLength canonicalQuantitativeMassBlockers

quantitativeMassBlockerCountIs10 :
  quantitativeMassBlockerCount ≡ 10
quantitativeMassBlockerCountIs10 =
  refl

data QuantitativeMassSupportRow : Set where
  microlocalDefectMassBoundarySupport :
    QuantitativeMassSupportRow
  zeroModeSetClassificationBoundarySupport :
    QuantitativeMassSupportRow
  qualitativeGreatCircleGeometrySupport :
    QuantitativeMassSupportRow
  targetEstimateMuOutsideZNSSupport :
    QuantitativeMassSupportRow
  residualDepletionConsumerSupport :
    QuantitativeMassSupportRow
  failClosedClayBoundarySupport :
    QuantitativeMassSupportRow

canonicalQuantitativeMassSupportRows :
  List QuantitativeMassSupportRow
canonicalQuantitativeMassSupportRows =
  microlocalDefectMassBoundarySupport
  ∷ zeroModeSetClassificationBoundarySupport
  ∷ qualitativeGreatCircleGeometrySupport
  ∷ targetEstimateMuOutsideZNSSupport
  ∷ residualDepletionConsumerSupport
  ∷ failClosedClayBoundarySupport
  ∷ []

quantitativeMassSupportRowCount : Nat
quantitativeMassSupportRowCount =
  listLength canonicalQuantitativeMassSupportRows

quantitativeMassSupportRowCountIs6 :
  quantitativeMassSupportRowCount ≡ 6
quantitativeMassSupportRowCountIs6 =
  refl

data QuantitativeMassStatusRow : Set where
  targetEstimateRecordedStatus :
    QuantitativeMassStatusRow
  consumedMicrolocalBoundaryStatus :
    QuantitativeMassStatusRow
  consumedZeroModeClassificationStatus :
    QuantitativeMassStatusRow
  qualitativeGeometryNotQuantitativeMassStatus :
    QuantitativeMassStatusRow
  lpPressureBootstrapStillOpenStatus :
    QuantitativeMassStatusRow
  quantitativeTransferStillOpenStatus :
    QuantitativeMassStatusRow
  residualDepletionStillFalseStatus :
    QuantitativeMassStatusRow
  clayPromotionFalseStatus :
    QuantitativeMassStatusRow

canonicalQuantitativeMassStatusRows :
  List QuantitativeMassStatusRow
canonicalQuantitativeMassStatusRows =
  targetEstimateRecordedStatus
  ∷ consumedMicrolocalBoundaryStatus
  ∷ consumedZeroModeClassificationStatus
  ∷ qualitativeGeometryNotQuantitativeMassStatus
  ∷ lpPressureBootstrapStillOpenStatus
  ∷ quantitativeTransferStillOpenStatus
  ∷ residualDepletionStillFalseStatus
  ∷ clayPromotionFalseStatus
  ∷ []

quantitativeMassStatusRowCount : Nat
quantitativeMassStatusRowCount =
  listLength canonicalQuantitativeMassStatusRows

quantitativeMassStatusRowCountIs8 :
  quantitativeMassStatusRowCount ≡ 8
quantitativeMassStatusRowCountIs8 =
  refl

------------------------------------------------------------------------
-- Fail-closed gates.

NSQuantitativeMassOutsideZeroModesBoundaryRecorded : Bool
NSQuantitativeMassOutsideZeroModesBoundaryRecorded =
  true

MicrolocalDefectMassBoundaryConsumed : Bool
MicrolocalDefectMassBoundaryConsumed =
  true

ZeroModeSetClassificationBoundaryConsumed : Bool
ZeroModeSetClassificationBoundaryConsumed =
  true

QualitativeGreatCircleGeometryRecorded : Bool
QualitativeGreatCircleGeometryRecorded =
  true

TargetEstimateMuOutsideZNSRecorded : Bool
TargetEstimateMuOutsideZNSRecorded =
  true

BlowupProfileCompactnessProved : Bool
BlowupProfileCompactnessProved =
  false

LittlewoodPaleyTightnessProved : Bool
LittlewoodPaleyTightnessProved =
  false

PressureNonlocalityBootstrapClosed : Bool
PressureNonlocalityBootstrapClosed =
  false

QuantitativeLRTToMeasureTransferProved : Bool
QuantitativeLRTToMeasureTransferProved =
  false

PositiveMassOutsideZeroModesProved : Bool
PositiveMassOutsideZeroModesProved =
  false

ResidualDepletionFromOutsideZeroModeMass : Bool
ResidualDepletionFromOutsideZeroModeMass =
  false

NSCriticalResidualNonPositive : Bool
NSCriticalResidualNonPositive =
  false

FullLocalDefectMonotonicity : Bool
FullLocalDefectMonotonicity =
  false

MechanismExhaustionForFullClayNS : Bool
MechanismExhaustionForFullClayNS =
  false

fullClayNSSolved : Bool
fullClayNSSolved =
  false

full_clay_ns_solved : Bool
full_clay_ns_solved =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

------------------------------------------------------------------------
-- Control card.

organizationString : String
organizationString =
  "O: Worker lane 5 owns the quantitative mass-outside-zero-modes boundary module only."

requirementString : String
requirementString =
  "R: Encode the sharpened remaining NS analytic gap: qualitative great-circle geometry must be upgraded to mu(S^2 \\ Z_NS) >= c(epsilon0,C0) > 0 through LP/semiclassical compactness and pressure bootstrap."

codeArtifactString : String
codeArtifactString =
  "C: DASHI.Physics.Closure.NSQuantitativeMassOutsideZeroModesBoundary exports target carriers, stage/blocker/support/status rows, ORCSLPGF, and a canonical fail-closed receipt."

stateString : String
stateString =
  "S: NSMicrolocalDefectMassConstructionBoundary and NSZeroModeSetClassificationBoundary are consumed; qualitative geometry is recorded, but quantitative measure mass and residual depletion remain unproved."

latticeString : String
latticeString =
  "L: critical residual -> zero-mode great-circle avoidance -> LP tightness -> semiclassical measure -> quantitative LRT-to-measure transfer -> positive outside-Z_NS mass -> leakage -> residual depletion."

proposalString : String
proposalString =
  "P: Promote only the exact quantitative target and blockers; keep all analytic completion and Clay flags false."

governanceString : String
governanceString =
  "G: A qualitative topological exclusion is not treated as quantitative PDE evidence; proof promotion requires compactness, LP tightness, pressure bootstrap, quantitative transfer, and residual depletion."

gapString : String
gapString =
  "F: Missing evidence is the quantitative lower bound mu(S^2 \\ Z_NS) >= c(epsilon0,C0) > 0 and its use in NSCriticalResidualNonPositive."

record NSQuantitativeMassOutsideZeroModesORCSLPGF : Set where
  constructor nsQuantitativeMassOutsideZeroModesORCSLPGF
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

open NSQuantitativeMassOutsideZeroModesORCSLPGF public

canonicalNSQuantitativeMassOutsideZeroModesORCSLPGF :
  NSQuantitativeMassOutsideZeroModesORCSLPGF
canonicalNSQuantitativeMassOutsideZeroModesORCSLPGF =
  nsQuantitativeMassOutsideZeroModesORCSLPGF
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

record NSQuantitativeMassOutsideZeroModesBoundaryReceipt : Setω where
  constructor nsQuantitativeMassOutsideZeroModesBoundaryReceipt
  field
    theoremName :
      String
    theoremNameIsCanonical :
      theoremName ≡ "NSQuantitativeMassOutsideZeroModesBoundary"

    microlocalBoundaryAnchor :
      Micro.NSMicrolocalDefectMassConstructionBoundaryReceipt
    microlocalBoundaryRecorded :
      Micro.NSMicrolocalDefectMassConstructionBoundaryRecorded ≡ true
    microlocalMassStillFalse :
      Micro.MicrolocalDefectMassConstructed ≡ false
    microPressureBootstrapStillFalse :
      Micro.PressureNonlocalityBootstrapClosed ≡ false

    zeroModeClassificationAnchor :
      Zero.NSZeroModeSetClassificationBoundaryReceipt
    zeroModeClassificationRecorded :
      Zero.NSZeroModeSetClassificationBoundaryRecorded ≡ true
    zeroModeSetDefined :
      Zero.ZeroModeSetDefined ≡ true
    zeroModeSupportStillUnexhausted :
      Zero.SupportClassificationExhausted ≡ false
    zeroModeCriticalResidualStillFalse :
      Zero.NSCriticalResidualNonPositive ≡ false

    criticalResidualLowerBound :
      CriticalResidualLowerBoundCarrier
    criticalResidualLowerBoundIsCanonical :
      criticalResidualLowerBound ≡ canonicalCriticalResidualLowerBound
    greatCircleAvoidanceWitness :
      GreatCircleAvoidanceWitnessCarrier
    greatCircleAvoidanceWitnessIsCanonical :
      greatCircleAvoidanceWitness ≡ canonicalGreatCircleAvoidanceWitness
    quantitativeConstant :
      QuantitativeConstantCarrier
    quantitativeConstantIsCanonical :
      quantitativeConstant ≡ canonicalQuantitativeConstant
    outsideZeroModeRegion :
      OutsideZeroModeRegionCarrier
    outsideZeroModeRegionIsCanonical :
      outsideZeroModeRegion ≡ canonicalOutsideZeroModeRegion
    targetEstimate :
      QuantitativeMassEstimateTarget
    targetEstimateIsCanonical :
      targetEstimate ≡ canonicalQuantitativeMassEstimateTarget
    targetEstimateDescription :
      String
    targetEstimateDescriptionIsCanonical :
      targetEstimateDescription ≡ targetEstimateText
    qualitativeGeometryDescription :
      String
    qualitativeGeometryDescriptionIsCanonical :
      qualitativeGeometryDescription ≡ qualitativeGeometryText
    quantitativeGapDescription :
      String
    quantitativeGapDescriptionIsCanonical :
      quantitativeGapDescription ≡ quantitativeGapText

    stages :
      List QuantitativeMassStage
    stagesAreCanonical :
      stages ≡ canonicalQuantitativeMassStages
    stageCount :
      Nat
    stageCountIs11 :
      stageCount ≡ 11
    blockers :
      List QuantitativeMassOutsideZeroModesBlocker
    blockersAreCanonical :
      blockers ≡ canonicalQuantitativeMassBlockers
    blockerCount :
      Nat
    blockerCountIs10 :
      blockerCount ≡ 10
    supportRows :
      List QuantitativeMassSupportRow
    supportRowsAreCanonical :
      supportRows ≡ canonicalQuantitativeMassSupportRows
    supportRowCount :
      Nat
    supportRowCountIs6 :
      supportRowCount ≡ 6
    statusRows :
      List QuantitativeMassStatusRow
    statusRowsAreCanonical :
      statusRows ≡ canonicalQuantitativeMassStatusRows
    statusRowCount :
      Nat
    statusRowCountIs8 :
      statusRowCount ≡ 8

    boundaryRecorded :
      NSQuantitativeMassOutsideZeroModesBoundaryRecorded ≡ true
    microlocalBoundaryConsumed :
      MicrolocalDefectMassBoundaryConsumed ≡ true
    zeroModeBoundaryConsumed :
      ZeroModeSetClassificationBoundaryConsumed ≡ true
    qualitativeGeometryRecorded :
      QualitativeGreatCircleGeometryRecorded ≡ true
    targetEstimateRecorded :
      TargetEstimateMuOutsideZNSRecorded ≡ true

    blowupProfileCompactnessStillFalse :
      BlowupProfileCompactnessProved ≡ false
    littlewoodPaleyTightnessStillFalse :
      LittlewoodPaleyTightnessProved ≡ false
    pressureNonlocalityBootstrapStillFalse :
      PressureNonlocalityBootstrapClosed ≡ false
    quantitativeLRTToMeasureTransferStillFalse :
      QuantitativeLRTToMeasureTransferProved ≡ false
    positiveMassOutsideZeroModesStillFalse :
      PositiveMassOutsideZeroModesProved ≡ false
    residualDepletionStillFalse :
      ResidualDepletionFromOutsideZeroModeMass ≡ false
    nsCriticalResidualNonPositiveStillFalse :
      NSCriticalResidualNonPositive ≡ false
    fullLocalDefectMonotonicityStillFalse :
      FullLocalDefectMonotonicity ≡ false
    mechanismExhaustionForFullClayNSStillFalse :
      MechanismExhaustionForFullClayNS ≡ false
    fullClayNSSolvedFalse :
      fullClayNSSolved ≡ false
    fullClayNSSolvedSnakeFalse :
      full_clay_ns_solved ≡ false
    clayNavierStokesPromotedFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionFalse :
      terminalPromotion ≡ false

    orcslpgf :
      NSQuantitativeMassOutsideZeroModesORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSQuantitativeMassOutsideZeroModesORCSLPGF
    remainingProofObligations :
      List String

open NSQuantitativeMassOutsideZeroModesBoundaryReceipt public

canonicalNSQuantitativeMassOutsideZeroModesBoundaryReceipt :
  NSQuantitativeMassOutsideZeroModesBoundaryReceipt
canonicalNSQuantitativeMassOutsideZeroModesBoundaryReceipt =
  record
    { theoremName =
        "NSQuantitativeMassOutsideZeroModesBoundary"
    ; theoremNameIsCanonical =
        refl
    ; microlocalBoundaryAnchor =
        Micro.canonicalNSMicrolocalDefectMassConstructionBoundaryReceipt
    ; microlocalBoundaryRecorded =
        refl
    ; microlocalMassStillFalse =
        refl
    ; microPressureBootstrapStillFalse =
        refl
    ; zeroModeClassificationAnchor =
        Zero.canonicalNSZeroModeSetClassificationBoundaryReceipt
    ; zeroModeClassificationRecorded =
        refl
    ; zeroModeSetDefined =
        refl
    ; zeroModeSupportStillUnexhausted =
        refl
    ; zeroModeCriticalResidualStillFalse =
        refl
    ; criticalResidualLowerBound =
        canonicalCriticalResidualLowerBound
    ; criticalResidualLowerBoundIsCanonical =
        refl
    ; greatCircleAvoidanceWitness =
        canonicalGreatCircleAvoidanceWitness
    ; greatCircleAvoidanceWitnessIsCanonical =
        refl
    ; quantitativeConstant =
        canonicalQuantitativeConstant
    ; quantitativeConstantIsCanonical =
        refl
    ; outsideZeroModeRegion =
        canonicalOutsideZeroModeRegion
    ; outsideZeroModeRegionIsCanonical =
        refl
    ; targetEstimate =
        canonicalQuantitativeMassEstimateTarget
    ; targetEstimateIsCanonical =
        refl
    ; targetEstimateDescription =
        targetEstimateText
    ; targetEstimateDescriptionIsCanonical =
        refl
    ; qualitativeGeometryDescription =
        qualitativeGeometryText
    ; qualitativeGeometryDescriptionIsCanonical =
        refl
    ; quantitativeGapDescription =
        quantitativeGapText
    ; quantitativeGapDescriptionIsCanonical =
        refl
    ; stages =
        canonicalQuantitativeMassStages
    ; stagesAreCanonical =
        refl
    ; stageCount =
        quantitativeMassStageCount
    ; stageCountIs11 =
        refl
    ; blockers =
        canonicalQuantitativeMassBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCount =
        quantitativeMassBlockerCount
    ; blockerCountIs10 =
        refl
    ; supportRows =
        canonicalQuantitativeMassSupportRows
    ; supportRowsAreCanonical =
        refl
    ; supportRowCount =
        quantitativeMassSupportRowCount
    ; supportRowCountIs6 =
        refl
    ; statusRows =
        canonicalQuantitativeMassStatusRows
    ; statusRowsAreCanonical =
        refl
    ; statusRowCount =
        quantitativeMassStatusRowCount
    ; statusRowCountIs8 =
        refl
    ; boundaryRecorded =
        refl
    ; microlocalBoundaryConsumed =
        refl
    ; zeroModeBoundaryConsumed =
        refl
    ; qualitativeGeometryRecorded =
        refl
    ; targetEstimateRecorded =
        refl
    ; blowupProfileCompactnessStillFalse =
        refl
    ; littlewoodPaleyTightnessStillFalse =
        refl
    ; pressureNonlocalityBootstrapStillFalse =
        refl
    ; quantitativeLRTToMeasureTransferStillFalse =
        refl
    ; positiveMassOutsideZeroModesStillFalse =
        refl
    ; residualDepletionStillFalse =
        refl
    ; nsCriticalResidualNonPositiveStillFalse =
        refl
    ; fullLocalDefectMonotonicityStillFalse =
        refl
    ; mechanismExhaustionForFullClayNSStillFalse =
        refl
    ; fullClayNSSolvedFalse =
        refl
    ; fullClayNSSolvedSnakeFalse =
        refl
    ; clayNavierStokesPromotedFalse =
        refl
    ; terminalPromotionFalse =
        refl
    ; orcslpgf =
        canonicalNSQuantitativeMassOutsideZeroModesORCSLPGF
    ; orcslpgfIsCanonical =
        refl
    ; remainingProofObligations =
        "prove compactness of the blowup profile at positive critical residual"
        ∷ "prove LP tightness for the critical vorticity shell"
        ∷ "close the pressure nonlocality bootstrap for the semiclassical construction"
        ∷ "upgrade qualitative great-circle avoidance to quantitative Radon-measure mass"
        ∷ "prove mu(S^2 \\ Z_NS) >= c(epsilon0,C0) > 0"
        ∷ "feed the outside-zero-mode mass into leakage and residual depletion"
        ∷ "derive NSCriticalResidualNonPositive and FullLocalDefectMonotonicity"
        ∷ []
    }

nsQuantitativeMassOutsideZeroModesBoundaryIsRecorded :
  NSQuantitativeMassOutsideZeroModesBoundaryRecorded ≡ true
nsQuantitativeMassOutsideZeroModesBoundaryIsRecorded =
  refl

nsQuantitativeMassOutsideZeroModesTargetIsRecorded :
  TargetEstimateMuOutsideZNSRecorded ≡ true
nsQuantitativeMassOutsideZeroModesTargetIsRecorded =
  refl

nsQuantitativeMassOutsideZeroModesKeepsQuantitativeTransferFalse :
  quantitativeLRTToMeasureTransferStillFalse
    canonicalNSQuantitativeMassOutsideZeroModesBoundaryReceipt
  ≡
  refl
nsQuantitativeMassOutsideZeroModesKeepsQuantitativeTransferFalse =
  refl

nsQuantitativeMassOutsideZeroModesKeepsMassFalse :
  positiveMassOutsideZeroModesStillFalse
    canonicalNSQuantitativeMassOutsideZeroModesBoundaryReceipt
  ≡
  refl
nsQuantitativeMassOutsideZeroModesKeepsMassFalse =
  refl

nsQuantitativeMassOutsideZeroModesKeepsResidualFalse :
  nsCriticalResidualNonPositiveStillFalse
    canonicalNSQuantitativeMassOutsideZeroModesBoundaryReceipt
  ≡
  refl
nsQuantitativeMassOutsideZeroModesKeepsResidualFalse =
  refl

nsQuantitativeMassOutsideZeroModesKeepsClayFalse :
  clayNavierStokesPromotedFalse
    canonicalNSQuantitativeMassOutsideZeroModesBoundaryReceipt
  ≡
  refl
nsQuantitativeMassOutsideZeroModesKeepsClayFalse =
  refl
