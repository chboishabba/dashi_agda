module DASHI.Physics.Closure.NSZeroModeGreatCircleGeometryTheorem where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSLeiRenTianRadialZeroModeAuthorityBoundary as LRT
import DASHI.Physics.Closure.NSMicrolocalDefectMassConstructionBoundary as Micro
import DASHI.Physics.Closure.NSRankOneProjectionCommutatorFormula as RankOne
import DASHI.Physics.Closure.NSZeroModeSetClassificationBoundary as ZSet

------------------------------------------------------------------------
-- NS zero-mode great-circle geometry theorem boundary.
--
-- This module records the corrected finite-dimensional geometry target for
-- the NS pressure / maximal-strain defect Laplacian:
--
--   lambda_Delta(theta) = one-quarter sin^2(2 alpha(theta)).
--
-- The angle alpha is not the naive full-space angle between e_+ and theta.
-- In the divergence-free sector that naive reading risks collapsing the
-- tangential branch into the whole sphere.  The theorem target here uses the
-- intrinsic tangential/tensor-channel comparison angle between the selected
-- maximal-strain channel and the pressure/Riesz tensor channel.
--
-- This surface records the level-set geometry and great-circle classification
-- obligations only.  It does not prove level-set regularity, does not prove
-- that all zero-mode components miss a great circle, does not transfer
-- Lei-Ren-Tian direction-set information to a quantitative defect measure,
-- and does not promote Clay Navier-Stokes.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Corrected angle model.

data DefectLaplacianScalarLaw : Set where
  lambdaDeltaOneQuarterSinSquaredTwoAlpha :
    DefectLaplacianScalarLaw

canonicalDefectLaplacianScalarLaw : DefectLaplacianScalarLaw
canonicalDefectLaplacianScalarLaw =
  lambdaDeltaOneQuarterSinSquaredTwoAlpha

data AngleComparisonFrame : Set where
  naiveFullSpaceEPlusThetaAngle :
    AngleComparisonFrame

  intrinsicTangentialTensorChannelAngle :
    AngleComparisonFrame

data AngleFrameGovernance : Set where
  rejectedNaiveTangentialWholeSphereCollapse :
    AngleComparisonFrame →
    AngleFrameGovernance

  selectedIntrinsicPressureStrainChannelFrame :
    AngleComparisonFrame →
    AngleFrameGovernance

canonicalNaiveFrame : AngleComparisonFrame
canonicalNaiveFrame =
  naiveFullSpaceEPlusThetaAngle

canonicalIntrinsicFrame : AngleComparisonFrame
canonicalIntrinsicFrame =
  intrinsicTangentialTensorChannelAngle

canonicalNaiveFrameRejection : AngleFrameGovernance
canonicalNaiveFrameRejection =
  rejectedNaiveTangentialWholeSphereCollapse canonicalNaiveFrame

canonicalIntrinsicFrameSelection : AngleFrameGovernance
canonicalIntrinsicFrameSelection =
  selectedIntrinsicPressureStrainChannelFrame canonicalIntrinsicFrame

data TensorChannel : Set where
  maximalStrainEigenChannel :
    TensorChannel

  pressureRieszTensorChannel :
    TensorChannel

canonicalTensorChannels : List TensorChannel
canonicalTensorChannels =
  maximalStrainEigenChannel
  ∷ pressureRieszTensorChannel
  ∷ []

tensorChannelCount : Nat
tensorChannelCount =
  listLength canonicalTensorChannels

tensorChannelCountIs2 :
  tensorChannelCount ≡ 2
tensorChannelCountIs2 =
  refl

data IntrinsicAngleSlot : Set where
  alphaBetweenSelectedTensorChannels :
    TensorChannel →
    TensorChannel →
    IntrinsicAngleSlot

canonicalIntrinsicAlpha : IntrinsicAngleSlot
canonicalIntrinsicAlpha =
  alphaBetweenSelectedTensorChannels
    maximalStrainEigenChannel
    pressureRieszTensorChannel

------------------------------------------------------------------------
-- Zero-mode level-set geometry.

data ZeroModeLevelSetEquation : Set where
  sinTwoAlphaEqualsZero :
    IntrinsicAngleSlot →
    ZeroModeLevelSetEquation

canonicalZeroModeLevelSetEquation : ZeroModeLevelSetEquation
canonicalZeroModeLevelSetEquation =
  sinTwoAlphaEqualsZero canonicalIntrinsicAlpha

data ZeroModeGeometryCarrier : Set where
  intrinsicPressureStrainZeroModeLevelSet :
    ZeroModeLevelSetEquation →
    ZeroModeGeometryCarrier

canonicalZeroModeGeometryCarrier : ZeroModeGeometryCarrier
canonicalZeroModeGeometryCarrier =
  intrinsicPressureStrainZeroModeLevelSet
    canonicalZeroModeLevelSetEquation

data LevelSetRegularityStatus : Set where
  finiteUnionOfClosedCurvesTarget :
    ZeroModeGeometryCarrier →
    LevelSetRegularityStatus

  levelSetRegularityStillOpen :
    ZeroModeGeometryCarrier →
    LevelSetRegularityStatus

canonicalFiniteClosedCurveTarget : LevelSetRegularityStatus
canonicalFiniteClosedCurveTarget =
  finiteUnionOfClosedCurvesTarget canonicalZeroModeGeometryCarrier

canonicalLevelSetRegularityOpen : LevelSetRegularityStatus
canonicalLevelSetRegularityOpen =
  levelSetRegularityStillOpen canonicalZeroModeGeometryCarrier

data GreatCircleClassification : Set where
  hitsEveryGreatCircle :
    ZeroModeGeometryCarrier →
    GreatCircleClassification

  missesSomeGreatCircle :
    ZeroModeGeometryCarrier →
    GreatCircleClassification

  greatCircleHittingUnclassified :
    ZeroModeGeometryCarrier →
    GreatCircleClassification

canonicalGreatCircleHittingClassificationTarget :
  GreatCircleClassification
canonicalGreatCircleHittingClassificationTarget =
  greatCircleHittingUnclassified canonicalZeroModeGeometryCarrier

data LeiRenTianTransferTarget : Set where
  ifZeroModeTrapMissesGreatCircleThenNoSingularity :
    GreatCircleClassification →
    LeiRenTianTransferTarget

  missingDefectMeasureSupportTransfer :
    ZeroModeGeometryCarrier →
    LeiRenTianTransferTarget

canonicalLeiRenTianZeroModeTrapTarget :
  LeiRenTianTransferTarget
canonicalLeiRenTianZeroModeTrapTarget =
  ifZeroModeTrapMissesGreatCircleThenNoSingularity
    (missesSomeGreatCircle canonicalZeroModeGeometryCarrier)

canonicalDefectMeasureSupportTransferTarget :
  LeiRenTianTransferTarget
canonicalDefectMeasureSupportTransferTarget =
  missingDefectMeasureSupportTransfer canonicalZeroModeGeometryCarrier

------------------------------------------------------------------------
-- Geometry rows, blockers, and status.

data NSZeroModeGreatCircleGeometryRow : Set where
  rankOneDefectLaplacianFormulaAnchorRow :
    NSZeroModeGreatCircleGeometryRow

  lambdaDeltaOneQuarterSinSquaredTwoAlphaRow :
    NSZeroModeGreatCircleGeometryRow

  naiveFullSpaceAngleRejectedRow :
    NSZeroModeGreatCircleGeometryRow

  intrinsicTangentialTensorChannelAngleSelectedRow :
    NSZeroModeGreatCircleGeometryRow

  pressureRieszTensorChannelRow :
    NSZeroModeGreatCircleGeometryRow

  maximalStrainTensorChannelRow :
    NSZeroModeGreatCircleGeometryRow

  zeroModeIntrinsicLevelSetEquationRow :
    NSZeroModeGreatCircleGeometryRow

  finiteUnionOfClosedCurvesTheoremTargetRow :
    NSZeroModeGreatCircleGeometryRow

  greatCircleHittingClassificationTargetRow :
    NSZeroModeGreatCircleGeometryRow

  leiRenTianGreatCircleAuthorityAnchorRow :
    NSZeroModeGreatCircleGeometryRow

  zeroModeSetClassificationBoundaryAnchorRow :
    NSZeroModeGreatCircleGeometryRow

  microlocalDefectMassBoundaryAnchorRow :
    NSZeroModeGreatCircleGeometryRow

  defectMeasureTransferTargetRow :
    NSZeroModeGreatCircleGeometryRow

  clayNavierStokesNonPromotionRow :
    NSZeroModeGreatCircleGeometryRow

canonicalNSZeroModeGreatCircleGeometryRows :
  List NSZeroModeGreatCircleGeometryRow
canonicalNSZeroModeGreatCircleGeometryRows =
  rankOneDefectLaplacianFormulaAnchorRow
  ∷ lambdaDeltaOneQuarterSinSquaredTwoAlphaRow
  ∷ naiveFullSpaceAngleRejectedRow
  ∷ intrinsicTangentialTensorChannelAngleSelectedRow
  ∷ pressureRieszTensorChannelRow
  ∷ maximalStrainTensorChannelRow
  ∷ zeroModeIntrinsicLevelSetEquationRow
  ∷ finiteUnionOfClosedCurvesTheoremTargetRow
  ∷ greatCircleHittingClassificationTargetRow
  ∷ leiRenTianGreatCircleAuthorityAnchorRow
  ∷ zeroModeSetClassificationBoundaryAnchorRow
  ∷ microlocalDefectMassBoundaryAnchorRow
  ∷ defectMeasureTransferTargetRow
  ∷ clayNavierStokesNonPromotionRow
  ∷ []

zeroModeGreatCircleGeometryRowCount : Nat
zeroModeGreatCircleGeometryRowCount =
  listLength canonicalNSZeroModeGreatCircleGeometryRows

zeroModeGreatCircleGeometryRowCountIs14 :
  zeroModeGreatCircleGeometryRowCount ≡ 14
zeroModeGreatCircleGeometryRowCountIs14 =
  refl

data NSZeroModeGreatCircleGeometryBlocker : Set where
  missingIntrinsicTensorChannelFormalization :
    NSZeroModeGreatCircleGeometryBlocker

  missingLevelSetRegularityProof :
    NSZeroModeGreatCircleGeometryBlocker

  missingFiniteUnionClosedCurvesProof :
    NSZeroModeGreatCircleGeometryBlocker

  missingExclusionOfGreatCircleHittingComponents :
    NSZeroModeGreatCircleGeometryBlocker

  missingZeroModeTrapMissesGreatCircleProof :
    NSZeroModeGreatCircleGeometryBlocker

  missingLeiRenTianInternalFormalization :
    NSZeroModeGreatCircleGeometryBlocker

  missingVorticityDirectionSetToDefectMeasureTransfer :
    NSZeroModeGreatCircleGeometryBlocker

  missingQuantitativeMassOutsideZeroModeSet :
    NSZeroModeGreatCircleGeometryBlocker

  missingMicrolocalDefectMassConstruction :
    NSZeroModeGreatCircleGeometryBlocker

  missingLeakageAwayFromZeroModesEstimate :
    NSZeroModeGreatCircleGeometryBlocker

  missingNSCriticalResidualNonPositive :
    NSZeroModeGreatCircleGeometryBlocker

  missingFullLocalDefectMonotonicity :
    NSZeroModeGreatCircleGeometryBlocker

  missingMechanismExhaustionForFullClayNS :
    NSZeroModeGreatCircleGeometryBlocker

  clayNavierStokesPromotionClosed :
    NSZeroModeGreatCircleGeometryBlocker

canonicalNSZeroModeGreatCircleGeometryBlockers :
  List NSZeroModeGreatCircleGeometryBlocker
canonicalNSZeroModeGreatCircleGeometryBlockers =
  missingIntrinsicTensorChannelFormalization
  ∷ missingLevelSetRegularityProof
  ∷ missingFiniteUnionClosedCurvesProof
  ∷ missingExclusionOfGreatCircleHittingComponents
  ∷ missingZeroModeTrapMissesGreatCircleProof
  ∷ missingLeiRenTianInternalFormalization
  ∷ missingVorticityDirectionSetToDefectMeasureTransfer
  ∷ missingQuantitativeMassOutsideZeroModeSet
  ∷ missingMicrolocalDefectMassConstruction
  ∷ missingLeakageAwayFromZeroModesEstimate
  ∷ missingNSCriticalResidualNonPositive
  ∷ missingFullLocalDefectMonotonicity
  ∷ missingMechanismExhaustionForFullClayNS
  ∷ clayNavierStokesPromotionClosed
  ∷ []

zeroModeGreatCircleGeometryBlockerCount : Nat
zeroModeGreatCircleGeometryBlockerCount =
  listLength canonicalNSZeroModeGreatCircleGeometryBlockers

zeroModeGreatCircleGeometryBlockerCountIs14 :
  zeroModeGreatCircleGeometryBlockerCount ≡ 14
zeroModeGreatCircleGeometryBlockerCountIs14 =
  refl

data NSZeroModeGreatCircleGeometryStatus : Set where
  rankOneFormulaImportedStatus :
    NSZeroModeGreatCircleGeometryStatus

  zeroModeSetClassificationImportedStatus :
    NSZeroModeGreatCircleGeometryStatus

  leiRenTianAuthorityImportedStatus :
    NSZeroModeGreatCircleGeometryStatus

  microlocalBoundaryImportedStatus :
    NSZeroModeGreatCircleGeometryStatus

  intrinsicAngleCorrectionRecordedStatus :
    NSZeroModeGreatCircleGeometryStatus

  naiveTangentialWholeSphereClaimRejectedStatus :
    NSZeroModeGreatCircleGeometryStatus

  finiteClosedCurveTargetRecordedStatus :
    NSZeroModeGreatCircleGeometryStatus

  greatCircleClassificationTargetRecordedStatus :
    NSZeroModeGreatCircleGeometryStatus

  transferToDefectMeasureStillFalseStatus :
    NSZeroModeGreatCircleGeometryStatus

  clayPromotionFalseStatus :
    NSZeroModeGreatCircleGeometryStatus

canonicalNSZeroModeGreatCircleGeometryStatuses :
  List NSZeroModeGreatCircleGeometryStatus
canonicalNSZeroModeGreatCircleGeometryStatuses =
  rankOneFormulaImportedStatus
  ∷ zeroModeSetClassificationImportedStatus
  ∷ leiRenTianAuthorityImportedStatus
  ∷ microlocalBoundaryImportedStatus
  ∷ intrinsicAngleCorrectionRecordedStatus
  ∷ naiveTangentialWholeSphereClaimRejectedStatus
  ∷ finiteClosedCurveTargetRecordedStatus
  ∷ greatCircleClassificationTargetRecordedStatus
  ∷ transferToDefectMeasureStillFalseStatus
  ∷ clayPromotionFalseStatus
  ∷ []

zeroModeGreatCircleGeometryStatusCount : Nat
zeroModeGreatCircleGeometryStatusCount =
  listLength canonicalNSZeroModeGreatCircleGeometryStatuses

zeroModeGreatCircleGeometryStatusCountIs10 :
  zeroModeGreatCircleGeometryStatusCount ≡ 10
zeroModeGreatCircleGeometryStatusCountIs10 =
  refl

------------------------------------------------------------------------
-- Promotion and proof guards.

NSZeroModeGreatCircleGeometryTheoremRecorded : Bool
NSZeroModeGreatCircleGeometryTheoremRecorded =
  true

RankOneDefectLaplacianFormulaImported : Bool
RankOneDefectLaplacianFormulaImported =
  true

ZeroModeSetClassificationBoundaryImported : Bool
ZeroModeSetClassificationBoundaryImported =
  true

LeiRenTianAuthorityBoundaryImported : Bool
LeiRenTianAuthorityBoundaryImported =
  true

MicrolocalDefectMassBoundaryImported : Bool
MicrolocalDefectMassBoundaryImported =
  true

IntrinsicAngleCorrectionRecorded : Bool
IntrinsicAngleCorrectionRecorded =
  true

NaiveTangentialWholeSphereClaimRejected : Bool
NaiveTangentialWholeSphereClaimRejected =
  true

FiniteUnionClosedCurvesTargetRecorded : Bool
FiniteUnionClosedCurvesTargetRecorded =
  true

GreatCircleHittingClassificationTargetRecorded : Bool
GreatCircleHittingClassificationTargetRecorded =
  true

DefectMeasureTransferTargetRecorded : Bool
DefectMeasureTransferTargetRecorded =
  true

IntrinsicTensorChannelFormalized : Bool
IntrinsicTensorChannelFormalized =
  false

LevelSetRegularityProved : Bool
LevelSetRegularityProved =
  false

FiniteUnionClosedCurvesProved : Bool
FiniteUnionClosedCurvesProved =
  false

GreatCircleHittingComponentsExcluded : Bool
GreatCircleHittingComponentsExcluded =
  false

ZeroModeTrapMissesGreatCircleProved : Bool
ZeroModeTrapMissesGreatCircleProved =
  false

LeiRenTianTheoremInternallyFormalized : Bool
LeiRenTianTheoremInternallyFormalized =
  false

VorticityDirectionSetToDefectMeasureTransferProved : Bool
VorticityDirectionSetToDefectMeasureTransferProved =
  false

QuantitativeMassOutsideZeroModeSetProved : Bool
QuantitativeMassOutsideZeroModeSetProved =
  false

MicrolocalDefectMassConstructed : Bool
MicrolocalDefectMassConstructed =
  false

LeakageAwayFromZeroModesProved : Bool
LeakageAwayFromZeroModesProved =
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

full_clay_ns_solved : Bool
full_clay_ns_solved =
  false

fullClayNSSolved : Bool
fullClayNSSolved =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

recordedIsTrue :
  NSZeroModeGreatCircleGeometryTheoremRecorded ≡ true
recordedIsTrue =
  refl

intrinsicAngleCorrectionRecordedIsTrue :
  IntrinsicAngleCorrectionRecorded ≡ true
intrinsicAngleCorrectionRecordedIsTrue =
  refl

naiveTangentialWholeSphereClaimRejectedIsTrue :
  NaiveTangentialWholeSphereClaimRejected ≡ true
naiveTangentialWholeSphereClaimRejectedIsTrue =
  refl

finiteUnionClosedCurvesTargetRecordedIsTrue :
  FiniteUnionClosedCurvesTargetRecorded ≡ true
finiteUnionClosedCurvesTargetRecordedIsTrue =
  refl

greatCircleHittingClassificationTargetRecordedIsTrue :
  GreatCircleHittingClassificationTargetRecorded ≡ true
greatCircleHittingClassificationTargetRecordedIsTrue =
  refl

intrinsicTensorChannelFormalizedIsFalse :
  IntrinsicTensorChannelFormalized ≡ false
intrinsicTensorChannelFormalizedIsFalse =
  refl

levelSetRegularityProvedIsFalse :
  LevelSetRegularityProved ≡ false
levelSetRegularityProvedIsFalse =
  refl

finiteUnionClosedCurvesProvedIsFalse :
  FiniteUnionClosedCurvesProved ≡ false
finiteUnionClosedCurvesProvedIsFalse =
  refl

greatCircleHittingComponentsExcludedIsFalse :
  GreatCircleHittingComponentsExcluded ≡ false
greatCircleHittingComponentsExcludedIsFalse =
  refl

zeroModeTrapMissesGreatCircleProvedIsFalse :
  ZeroModeTrapMissesGreatCircleProved ≡ false
zeroModeTrapMissesGreatCircleProvedIsFalse =
  refl

vorticityDirectionSetToDefectMeasureTransferProvedIsFalse :
  VorticityDirectionSetToDefectMeasureTransferProved ≡ false
vorticityDirectionSetToDefectMeasureTransferProvedIsFalse =
  refl

quantitativeMassOutsideZeroModeSetProvedIsFalse :
  QuantitativeMassOutsideZeroModeSetProved ≡ false
quantitativeMassOutsideZeroModeSetProvedIsFalse =
  refl

microlocalDefectMassConstructedIsFalse :
  MicrolocalDefectMassConstructed ≡ false
microlocalDefectMassConstructedIsFalse =
  refl

nsCriticalResidualNonPositiveIsFalse :
  NSCriticalResidualNonPositive ≡ false
nsCriticalResidualNonPositiveIsFalse =
  refl

mechanismExhaustionForFullClayNSIsFalse :
  MechanismExhaustionForFullClayNS ≡ false
mechanismExhaustionForFullClayNSIsFalse =
  refl

clayNavierStokesPromotedIsFalse :
  clayNavierStokesPromoted ≡ false
clayNavierStokesPromotedIsFalse =
  refl

terminalPromotionIsFalse :
  terminalPromotion ≡ false
terminalPromotionIsFalse =
  refl

data NSZeroModeGreatCircleGeometryPromotion : Set where

nsZeroModeGreatCircleGeometryPromotionImpossibleHere :
  NSZeroModeGreatCircleGeometryPromotion →
  ⊥
nsZeroModeGreatCircleGeometryPromotionImpossibleHere ()

------------------------------------------------------------------------
-- ORCSLPGF.

organizationString : String
organizationString =
  "O: Worker lane 2 owns only the NS zero-mode great-circle geometry theorem boundary module."

requirementString : String
requirementString =
  "R: Record the corrected intrinsic/tensor-channel zero-mode geometry target, including lambda_Delta, level-set rows, great-circle classification, and blockers."

codeArtifactString : String
codeArtifactString =
  "C: DASHI.Physics.Closure.NSZeroModeGreatCircleGeometryTheorem exports corrected angle carriers, zero-mode level-set geometry, great-circle targets, blockers, status rows, guards, ORCSLPGF, and a non-promoting receipt."

stateString : String
stateString =
  "S: Rank-one algebra, zero-mode classification boundary, Lei-Ren-Tian authority boundary, and microlocal defect-mass boundary are imported; finite level-set regularity and quantitative transfer remain open."

latticeString : String
latticeString =
  "L: rank-one lambda_Delta -> intrinsic tensor-channel alpha -> zero-mode level set -> finite closed-curve target -> great-circle classification -> Lei-Ren-Tian trap exclusion target -> defect-measure transfer blocker."

proposalString : String
proposalString =
  "P: Promote only the corrected finite-dimensional theorem target; reject the naive e_+ perpendicular theta equals whole sphere interpretation and keep all Clay gates false."

governanceString : String
governanceString =
  "G: This is a fail-closed boundary surface. Level-set regularity, great-circle avoidance, microlocal mass transfer, residual depletion, full Clay NS, and terminal promotion are false."

gapString : String
gapString =
  "F: Remaining gaps are intrinsic tensor-channel formalization, regular-level-set proof, exclusion of great-circle-hitting zero-mode components, quantitative mass outside Z_NS, and the full pressure/residual bootstrap."

record NSZeroModeGreatCircleGeometryORCSLPGF : Set where
  constructor nsZeroModeGreatCircleGeometryORCSLPGF
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

open NSZeroModeGreatCircleGeometryORCSLPGF public

canonicalNSZeroModeGreatCircleGeometryORCSLPGF :
  NSZeroModeGreatCircleGeometryORCSLPGF
canonicalNSZeroModeGreatCircleGeometryORCSLPGF =
  nsZeroModeGreatCircleGeometryORCSLPGF
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
-- Canonical receipt.

record NSZeroModeGreatCircleGeometryTheoremReceipt : Set₁ where
  constructor nsZeroModeGreatCircleGeometryTheoremReceipt
  field
    gateName :
      String
    gateNameIsCanonical :
      gateName ≡ "NSZeroModeGreatCircleGeometryTheorem"

    scalarLaw :
      DefectLaplacianScalarLaw
    scalarLawIsCanonical :
      scalarLaw ≡ canonicalDefectLaplacianScalarLaw

    intrinsicAlpha :
      IntrinsicAngleSlot
    intrinsicAlphaIsCanonical :
      intrinsicAlpha ≡ canonicalIntrinsicAlpha

    zeroModeEquation :
      ZeroModeLevelSetEquation
    zeroModeEquationIsCanonical :
      zeroModeEquation ≡ canonicalZeroModeLevelSetEquation

    zeroModeCarrier :
      ZeroModeGeometryCarrier
    zeroModeCarrierIsCanonical :
      zeroModeCarrier ≡ canonicalZeroModeGeometryCarrier

    finiteClosedCurveTarget :
      LevelSetRegularityStatus
    finiteClosedCurveTargetIsCanonical :
      finiteClosedCurveTarget ≡ canonicalFiniteClosedCurveTarget

    greatCircleClassificationTarget :
      GreatCircleClassification
    greatCircleClassificationTargetIsCanonical :
      greatCircleClassificationTarget
      ≡
      canonicalGreatCircleHittingClassificationTarget

    leiRenTianTrapTarget :
      LeiRenTianTransferTarget
    leiRenTianTrapTargetIsCanonical :
      leiRenTianTrapTarget ≡ canonicalLeiRenTianZeroModeTrapTarget

    defectMeasureTransferTarget :
      LeiRenTianTransferTarget
    defectMeasureTransferTargetIsCanonical :
      defectMeasureTransferTarget
      ≡
      canonicalDefectMeasureSupportTransferTarget

    geometryRows :
      List NSZeroModeGreatCircleGeometryRow
    geometryRowsAreCanonical :
      geometryRows ≡ canonicalNSZeroModeGreatCircleGeometryRows
    geometryRowCount :
      Nat
    geometryRowCountIsCanonical :
      geometryRowCount ≡ zeroModeGreatCircleGeometryRowCount
    geometryRowCountProof :
      geometryRowCount ≡ 14

    blockerRows :
      List NSZeroModeGreatCircleGeometryBlocker
    blockerRowsAreCanonical :
      blockerRows ≡ canonicalNSZeroModeGreatCircleGeometryBlockers
    blockerRowCount :
      Nat
    blockerRowCountIsCanonical :
      blockerRowCount ≡ zeroModeGreatCircleGeometryBlockerCount
    blockerRowCountProof :
      blockerRowCount ≡ 14

    statusRows :
      List NSZeroModeGreatCircleGeometryStatus
    statusRowsAreCanonical :
      statusRows ≡ canonicalNSZeroModeGreatCircleGeometryStatuses
    statusRowCount :
      Nat
    statusRowCountIsCanonical :
      statusRowCount ≡ zeroModeGreatCircleGeometryStatusCount
    statusRowCountProof :
      statusRowCount ≡ 10

    rankOneRows :
      List RankOne.RankOneProjectionCommutatorStatus
    rankOneRowsAreCanonical :
      rankOneRows
      ≡
      RankOne.canonicalRankOneProjectionCommutatorStatus

    zeroModeClassificationRows :
      List ZSet.NSZeroModeSetClassificationRow
    zeroModeClassificationRowsAreCanonical :
      zeroModeClassificationRows
      ≡
      ZSet.canonicalNSZeroModeSetClassificationRows

    leiRenTianAuthorityRows :
      List LRT.RadialZeroModeAuthoritySupportRow
    leiRenTianAuthorityRowsAreCanonical :
      leiRenTianAuthorityRows
      ≡
      LRT.canonicalRadialZeroModeAuthoritySupportRows

    microlocalBoundaryRecorded :
      Micro.NSMicrolocalDefectMassConstructionBoundaryRecorded ≡ true

    intrinsicCorrectionRecordedTrue :
      IntrinsicAngleCorrectionRecorded ≡ true
    naiveClaimRejectedTrue :
      NaiveTangentialWholeSphereClaimRejected ≡ true
    finiteClosedCurveTargetRecordedTrue :
      FiniteUnionClosedCurvesTargetRecorded ≡ true
    greatCircleClassificationTargetRecordedTrue :
      GreatCircleHittingClassificationTargetRecorded ≡ true

    levelSetRegularityFalse :
      LevelSetRegularityProved ≡ false
    finiteUnionClosedCurvesFalse :
      FiniteUnionClosedCurvesProved ≡ false
    greatCircleHittingComponentsExcludedFalse :
      GreatCircleHittingComponentsExcluded ≡ false
    defectMeasureTransferFalse :
      VorticityDirectionSetToDefectMeasureTransferProved ≡ false
    quantitativeMassOutsideZeroModeSetFalse :
      QuantitativeMassOutsideZeroModeSetProved ≡ false
    microlocalDefectMassConstructedFalse :
      MicrolocalDefectMassConstructed ≡ false
    nsCriticalResidualNonPositiveFalse :
      NSCriticalResidualNonPositive ≡ false
    clayNavierStokesPromotedFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionFalse :
      terminalPromotion ≡ false

    orcslpgf :
      NSZeroModeGreatCircleGeometryORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSZeroModeGreatCircleGeometryORCSLPGF

open NSZeroModeGreatCircleGeometryTheoremReceipt public

canonicalNSZeroModeGreatCircleGeometryTheoremReceipt :
  NSZeroModeGreatCircleGeometryTheoremReceipt
canonicalNSZeroModeGreatCircleGeometryTheoremReceipt =
  nsZeroModeGreatCircleGeometryTheoremReceipt
    "NSZeroModeGreatCircleGeometryTheorem"
    refl
    canonicalDefectLaplacianScalarLaw
    refl
    canonicalIntrinsicAlpha
    refl
    canonicalZeroModeLevelSetEquation
    refl
    canonicalZeroModeGeometryCarrier
    refl
    canonicalFiniteClosedCurveTarget
    refl
    canonicalGreatCircleHittingClassificationTarget
    refl
    canonicalLeiRenTianZeroModeTrapTarget
    refl
    canonicalDefectMeasureSupportTransferTarget
    refl
    canonicalNSZeroModeGreatCircleGeometryRows
    refl
    zeroModeGreatCircleGeometryRowCount
    refl
    zeroModeGreatCircleGeometryRowCountIs14
    canonicalNSZeroModeGreatCircleGeometryBlockers
    refl
    zeroModeGreatCircleGeometryBlockerCount
    refl
    zeroModeGreatCircleGeometryBlockerCountIs14
    canonicalNSZeroModeGreatCircleGeometryStatuses
    refl
    zeroModeGreatCircleGeometryStatusCount
    refl
    zeroModeGreatCircleGeometryStatusCountIs10
    RankOne.canonicalRankOneProjectionCommutatorStatus
    refl
    ZSet.canonicalNSZeroModeSetClassificationRows
    refl
    LRT.canonicalRadialZeroModeAuthoritySupportRows
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
    canonicalNSZeroModeGreatCircleGeometryORCSLPGF
    refl

------------------------------------------------------------------------
-- Explicit fail-closed boundary envelope.

canonicalNSZeroModeGreatCircleGeometryObligations :
  List String
canonicalNSZeroModeGreatCircleGeometryObligations =
  "formalize the intrinsic tangential tensor-channel angle alpha"
  ∷ "prove regularity of the zero-mode level set sin(2 alpha) equals zero"
  ∷ "prove the finite-union-of-closed-curves theorem target"
  ∷ "classify which zero-mode components miss some great circle"
  ∷ "exclude or deplete great-circle-hitting zero-mode components"
  ∷ "transfer LRT direction-set information to quantitative defect-measure support"
  ∷ "prove quantitative mass outside the NS zero-mode set"
  ∷ "construct microlocal defect mass and leakage away from zero modes"
  ∷ "derive NSCriticalResidualNonPositive and FullLocalDefectMonotonicity"
  ∷ "keep Clay Navier-Stokes and terminal promotion false"
  ∷ []

zeroModeGreatCircleGeometryObligationCount : Nat
zeroModeGreatCircleGeometryObligationCount =
  listLength canonicalNSZeroModeGreatCircleGeometryObligations

zeroModeGreatCircleGeometryObligationCountIs10 :
  zeroModeGreatCircleGeometryObligationCount ≡ 10
zeroModeGreatCircleGeometryObligationCountIs10 =
  refl

record NSZeroModeGreatCircleGeometryFailClosedEnvelope : Set₁ where
  constructor nsZeroModeGreatCircleGeometryFailClosedEnvelope
  field
    receipt :
      NSZeroModeGreatCircleGeometryTheoremReceipt
    receiptIsCanonical :
      receipt ≡ canonicalNSZeroModeGreatCircleGeometryTheoremReceipt

    scalarLawRecorded :
      DefectLaplacianScalarLaw
    scalarLawRecordedIsCanonical :
      scalarLawRecorded ≡ canonicalDefectLaplacianScalarLaw

    naiveFrameRejected :
      AngleFrameGovernance
    naiveFrameRejectedIsCanonical :
      naiveFrameRejected ≡ canonicalNaiveFrameRejection

    intrinsicFrameSelected :
      AngleFrameGovernance
    intrinsicFrameSelectedIsCanonical :
      intrinsicFrameSelected ≡ canonicalIntrinsicFrameSelection

    intrinsicAlpha :
      IntrinsicAngleSlot
    intrinsicAlphaIsCanonical :
      intrinsicAlpha ≡ canonicalIntrinsicAlpha

    zeroModeLevelSet :
      ZeroModeLevelSetEquation
    zeroModeLevelSetIsCanonical :
      zeroModeLevelSet ≡ canonicalZeroModeLevelSetEquation

    finiteClosedCurveTarget :
      LevelSetRegularityStatus
    finiteClosedCurveTargetIsCanonical :
      finiteClosedCurveTarget ≡ canonicalFiniteClosedCurveTarget

    levelSetRegularityOpen :
      LevelSetRegularityStatus
    levelSetRegularityOpenIsCanonical :
      levelSetRegularityOpen ≡ canonicalLevelSetRegularityOpen

    greatCircleClassificationTarget :
      GreatCircleClassification
    greatCircleClassificationTargetIsCanonical :
      greatCircleClassificationTarget
      ≡
      canonicalGreatCircleHittingClassificationTarget

    lrtTrapTransferTarget :
      LeiRenTianTransferTarget
    lrtTrapTransferTargetIsCanonical :
      lrtTrapTransferTarget ≡ canonicalLeiRenTianZeroModeTrapTarget

    defectMeasureTransferTarget :
      LeiRenTianTransferTarget
    defectMeasureTransferTargetIsCanonical :
      defectMeasureTransferTarget
      ≡
      canonicalDefectMeasureSupportTransferTarget

    geometryRows :
      List NSZeroModeGreatCircleGeometryRow
    geometryRowsAreCanonical :
      geometryRows ≡ canonicalNSZeroModeGreatCircleGeometryRows
    geometryRowCountProof :
      listLength geometryRows ≡ 14

    blockers :
      List NSZeroModeGreatCircleGeometryBlocker
    blockersAreCanonical :
      blockers ≡ canonicalNSZeroModeGreatCircleGeometryBlockers
    blockerCountProof :
      listLength blockers ≡ 14

    statuses :
      List NSZeroModeGreatCircleGeometryStatus
    statusesAreCanonical :
      statuses ≡ canonicalNSZeroModeGreatCircleGeometryStatuses
    statusCountProof :
      listLength statuses ≡ 10

    obligations :
      List String
    obligationsAreCanonical :
      obligations ≡ canonicalNSZeroModeGreatCircleGeometryObligations
    obligationCountProof :
      listLength obligations ≡ 10

    promotionFlags :
      List NSZeroModeGreatCircleGeometryPromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []
    noPromotionPossibleHere :
      NSZeroModeGreatCircleGeometryPromotion →
      ⊥

    intrinsicTensorChannelStillFalse :
      IntrinsicTensorChannelFormalized ≡ false
    levelSetRegularityStillFalse :
      LevelSetRegularityProved ≡ false
    finiteCurvesStillFalse :
      FiniteUnionClosedCurvesProved ≡ false
    greatCircleComponentExclusionStillFalse :
      GreatCircleHittingComponentsExcluded ≡ false
    zeroModeTrapMissesGreatCircleStillFalse :
      ZeroModeTrapMissesGreatCircleProved ≡ false
    defectMeasureTransferStillFalse :
      VorticityDirectionSetToDefectMeasureTransferProved ≡ false
    quantitativeMassStillFalse :
      QuantitativeMassOutsideZeroModeSetProved ≡ false
    microlocalMassStillFalse :
      MicrolocalDefectMassConstructed ≡ false
    criticalResidualStillFalse :
      NSCriticalResidualNonPositive ≡ false
    fullLocalMonotonicityStillFalse :
      FullLocalDefectMonotonicity ≡ false
    claySolvedStillFalse :
      full_clay_ns_solved ≡ false
    clayPromotionStillFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionStillFalse :
      terminalPromotion ≡ false

open NSZeroModeGreatCircleGeometryFailClosedEnvelope public

canonicalNSZeroModeGreatCircleGeometryFailClosedEnvelope :
  NSZeroModeGreatCircleGeometryFailClosedEnvelope
canonicalNSZeroModeGreatCircleGeometryFailClosedEnvelope =
  nsZeroModeGreatCircleGeometryFailClosedEnvelope
    canonicalNSZeroModeGreatCircleGeometryTheoremReceipt
    refl
    canonicalDefectLaplacianScalarLaw
    refl
    canonicalNaiveFrameRejection
    refl
    canonicalIntrinsicFrameSelection
    refl
    canonicalIntrinsicAlpha
    refl
    canonicalZeroModeLevelSetEquation
    refl
    canonicalFiniteClosedCurveTarget
    refl
    canonicalLevelSetRegularityOpen
    refl
    canonicalGreatCircleHittingClassificationTarget
    refl
    canonicalLeiRenTianZeroModeTrapTarget
    refl
    canonicalDefectMeasureSupportTransferTarget
    refl
    canonicalNSZeroModeGreatCircleGeometryRows
    refl
    zeroModeGreatCircleGeometryRowCountIs14
    canonicalNSZeroModeGreatCircleGeometryBlockers
    refl
    zeroModeGreatCircleGeometryBlockerCountIs14
    canonicalNSZeroModeGreatCircleGeometryStatuses
    refl
    zeroModeGreatCircleGeometryStatusCountIs10
    canonicalNSZeroModeGreatCircleGeometryObligations
    refl
    zeroModeGreatCircleGeometryObligationCountIs10
    []
    refl
    nsZeroModeGreatCircleGeometryPromotionImpossibleHere
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

canonicalNSZeroModeGreatCircleGeometryFailClosedSummary :
  String
canonicalNSZeroModeGreatCircleGeometryFailClosedSummary =
  "Fail-closed: the corrected intrinsic zero-mode great-circle geometry target is recorded, while regularity, classification, quantitative transfer, microlocal mass, residual monotonicity, Clay NS, and terminal promotion remain blocked."
