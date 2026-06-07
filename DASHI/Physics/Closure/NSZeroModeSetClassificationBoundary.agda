module DASHI.Physics.Closure.NSZeroModeSetClassificationBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSMicrolocalDefectMassConstructionBoundary as Micro
import DASHI.Physics.Closure.NSNonRadialityQuantificationAverage as NonRadial
import DASHI.Physics.Closure.NSRankOneProjectionCommutatorFormula as RankOne
import DASHI.Physics.Closure.NSSigmaNonRadialCommutatorLowerBoundTarget as Sigma
import DASHI.Physics.Closure.NSTransverseSigmaNeighborhoodGeometry as Transverse

------------------------------------------------------------------------
-- NS zero-mode set classification boundary.
--
-- This worker-lane module records the corrected P0 zero-mode formulation
-- for the Navier-Stokes pressure / maximal-strain projection defect:
--
--   lambda_Delta(theta) = 1/4 sin^2(2 alpha(theta))
--   Z_NS = Z_rad union Z_tan
--
-- It consumes the checked rank-one projection commutator formula, the finite
-- non-radiality averaging support, the transverse Sigma neighborhood target,
-- the Sigma non-radial lower-bound target, and the microlocal defect-mass
-- construction boundary.  It deliberately does not prove leakage away from
-- zero modes, radial/tangential rigidity, wedge exclusion, microlocal mass,
-- residual depletion, Clay NS, or terminal unification.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

data DefectLaplacianEigenvalueExpression : Set where
  oneQuarterSinSquaredTwoAlpha :
    DefectLaplacianEigenvalueExpression

data NSZeroModeBranch : Set where
  radialZeroModeBranch :
    NSZeroModeBranch

  tangentialZeroModeBranch :
    NSZeroModeBranch

canonicalNSZeroModeBranches : List NSZeroModeBranch
canonicalNSZeroModeBranches =
  radialZeroModeBranch
  ∷ tangentialZeroModeBranch
  ∷ []

nsZeroModeBranchCount : Nat
nsZeroModeBranchCount =
  listLength canonicalNSZeroModeBranches

nsZeroModeBranchCountIsTwo :
  nsZeroModeBranchCount ≡ 2
nsZeroModeBranchCountIsTwo =
  refl

data ZeroModeCondition : Set where
  ePlusParallelTheta :
    ZeroModeCondition

  ePlusPerpendicularTheta :
    ZeroModeCondition

zeroModeCondition :
  NSZeroModeBranch →
  ZeroModeCondition
zeroModeCondition radialZeroModeBranch =
  ePlusParallelTheta
zeroModeCondition tangentialZeroModeBranch =
  ePlusPerpendicularTheta

radialZeroModeConditionIsParallel :
  zeroModeCondition radialZeroModeBranch ≡ ePlusParallelTheta
radialZeroModeConditionIsParallel =
  refl

tangentialZeroModeConditionIsPerpendicular :
  zeroModeCondition tangentialZeroModeBranch ≡ ePlusPerpendicularTheta
tangentialZeroModeConditionIsPerpendicular =
  refl

data NSZeroModeSet : Set where
  zeroModeSetUnionRadialTangential :
    NSZeroModeBranch →
    NSZeroModeSet

canonicalRadialZeroModeSet : NSZeroModeSet
canonicalRadialZeroModeSet =
  zeroModeSetUnionRadialTangential radialZeroModeBranch

canonicalTangentialZeroModeSet : NSZeroModeSet
canonicalTangentialZeroModeSet =
  zeroModeSetUnionRadialTangential tangentialZeroModeBranch

canonicalNSZeroModeSetComponents : List NSZeroModeSet
canonicalNSZeroModeSetComponents =
  canonicalRadialZeroModeSet
  ∷ canonicalTangentialZeroModeSet
  ∷ []

nsZeroModeSetComponentCount : Nat
nsZeroModeSetComponentCount =
  listLength canonicalNSZeroModeSetComponents

nsZeroModeSetComponentCountIsTwo :
  nsZeroModeSetComponentCount ≡ 2
nsZeroModeSetComponentCountIsTwo =
  refl

data DefectMeasureSupportRegion : Set where
  awayFromZeroModeNeighborhood :
    DefectMeasureSupportRegion

  supportedOnRadialZeroMode :
    DefectMeasureSupportRegion

  supportedOnTangentialZeroMode :
    DefectMeasureSupportRegion

  supportedInShrinkingSigmaWedge :
    DefectMeasureSupportRegion

  supportUnclassified :
    DefectMeasureSupportRegion

canonicalSupportClassificationCases :
  List DefectMeasureSupportRegion
canonicalSupportClassificationCases =
  awayFromZeroModeNeighborhood
  ∷ supportedOnRadialZeroMode
  ∷ supportedOnTangentialZeroMode
  ∷ supportedInShrinkingSigmaWedge
  ∷ supportUnclassified
  ∷ []

supportClassificationCaseCount : Nat
supportClassificationCaseCount =
  listLength canonicalSupportClassificationCases

supportClassificationCaseCountIsFive :
  supportClassificationCaseCount ≡ 5
supportClassificationCaseCountIsFive =
  refl

data ZeroModeCaseTarget : Set where
  leakageAwayFromZeroModes :
    DefectMeasureSupportRegion →
    ZeroModeCaseTarget

  radialZeroModeRigidityObstruction :
    DefectMeasureSupportRegion →
    ZeroModeCaseTarget

  tangentialZeroModePressureStarvation :
    DefectMeasureSupportRegion →
    ZeroModeCaseTarget

  sigmaWedgeCollapseExclusion :
    DefectMeasureSupportRegion →
    ZeroModeCaseTarget

  supportClassificationExhaustion :
    List DefectMeasureSupportRegion →
    ZeroModeCaseTarget

canonicalLeakageAwayFromZeroModesTarget : ZeroModeCaseTarget
canonicalLeakageAwayFromZeroModesTarget =
  leakageAwayFromZeroModes awayFromZeroModeNeighborhood

canonicalRadialZeroModeRigidityTarget : ZeroModeCaseTarget
canonicalRadialZeroModeRigidityTarget =
  radialZeroModeRigidityObstruction supportedOnRadialZeroMode

canonicalTangentialZeroModeStarvationTarget : ZeroModeCaseTarget
canonicalTangentialZeroModeStarvationTarget =
  tangentialZeroModePressureStarvation supportedOnTangentialZeroMode

canonicalSigmaWedgeCollapseTarget : ZeroModeCaseTarget
canonicalSigmaWedgeCollapseTarget =
  sigmaWedgeCollapseExclusion supportedInShrinkingSigmaWedge

canonicalSupportClassificationExhaustionTarget : ZeroModeCaseTarget
canonicalSupportClassificationExhaustionTarget =
  supportClassificationExhaustion canonicalSupportClassificationCases

data NSZeroModeSetClassificationRow : Set where
  rankOneDefectLaplacianFormulaAnchorRow :
    NSZeroModeSetClassificationRow

  lambdaDeltaOneQuarterSinSquaredTwoAlphaRow :
    NSZeroModeSetClassificationRow

  zeroModeSetUnionRadialTangentialRow :
    NSZeroModeSetClassificationRow

  radialZeroModeParallelConditionRow :
    NSZeroModeSetClassificationRow

  tangentialZeroModePerpendicularConditionRow :
    NSZeroModeSetClassificationRow

  nonRadialAverageSupportAnchorRow :
    NSZeroModeSetClassificationRow

  transverseSigmaGeometryAnchorRow :
    NSZeroModeSetClassificationRow

  sigmaLowerBoundTargetAnchorRow :
    NSZeroModeSetClassificationRow

  microlocalDefectMassBoundaryAnchorRow :
    NSZeroModeSetClassificationRow

  leakageAwayFromZeroModesTargetRow :
    NSZeroModeSetClassificationRow

  radialZeroModeRigidityTargetRow :
    NSZeroModeSetClassificationRow

  tangentialZeroModePressureStarvationTargetRow :
    NSZeroModeSetClassificationRow

  sigmaWedgeCollapseTargetRow :
    NSZeroModeSetClassificationRow

  exactSupportClassificationGapRow :
    NSZeroModeSetClassificationRow

  noClayOrTerminalPromotionRow :
    NSZeroModeSetClassificationRow

canonicalNSZeroModeSetClassificationRows :
  List NSZeroModeSetClassificationRow
canonicalNSZeroModeSetClassificationRows =
  rankOneDefectLaplacianFormulaAnchorRow
  ∷ lambdaDeltaOneQuarterSinSquaredTwoAlphaRow
  ∷ zeroModeSetUnionRadialTangentialRow
  ∷ radialZeroModeParallelConditionRow
  ∷ tangentialZeroModePerpendicularConditionRow
  ∷ nonRadialAverageSupportAnchorRow
  ∷ transverseSigmaGeometryAnchorRow
  ∷ sigmaLowerBoundTargetAnchorRow
  ∷ microlocalDefectMassBoundaryAnchorRow
  ∷ leakageAwayFromZeroModesTargetRow
  ∷ radialZeroModeRigidityTargetRow
  ∷ tangentialZeroModePressureStarvationTargetRow
  ∷ sigmaWedgeCollapseTargetRow
  ∷ exactSupportClassificationGapRow
  ∷ noClayOrTerminalPromotionRow
  ∷ []

zeroModeSetClassificationRowCount : Nat
zeroModeSetClassificationRowCount =
  listLength canonicalNSZeroModeSetClassificationRows

zeroModeSetClassificationRowCountIs15 :
  zeroModeSetClassificationRowCount ≡ 15
zeroModeSetClassificationRowCountIs15 =
  refl

data NSZeroModeSetClassificationBlocker : Set where
  missingLeiRenTianAuthorityTokenAndFormalImport :
    NSZeroModeSetClassificationBlocker

  missingRadialZeroModeIncompressibilityObstructionProof :
    NSZeroModeSetClassificationBlocker

  missingTangentialZeroModePressureStarvationProof :
    NSZeroModeSetClassificationBlocker

  missingLeakageAwayFromZeroModesEstimate :
    NSZeroModeSetClassificationBlocker

  missingSigmaWedgeCollapseExclusionProof :
    NSZeroModeSetClassificationBlocker

  missingSupportClassificationExhaustion :
    NSZeroModeSetClassificationBlocker

  missingMicrolocalDefectMassConstruction :
    NSZeroModeSetClassificationBlocker

  missingNoZeroModeDegeneracyRidingCascade :
    NSZeroModeSetClassificationBlocker

  missingNSCriticalResidualNonPositive :
    NSZeroModeSetClassificationBlocker

  missingFullLocalDefectMonotonicity :
    NSZeroModeSetClassificationBlocker

  missingMechanismExhaustionForFullClayNS :
    NSZeroModeSetClassificationBlocker

  clayNavierStokesPromotionClosed :
    NSZeroModeSetClassificationBlocker

canonicalNSZeroModeSetClassificationBlockers :
  List NSZeroModeSetClassificationBlocker
canonicalNSZeroModeSetClassificationBlockers =
  missingLeiRenTianAuthorityTokenAndFormalImport
  ∷ missingRadialZeroModeIncompressibilityObstructionProof
  ∷ missingTangentialZeroModePressureStarvationProof
  ∷ missingLeakageAwayFromZeroModesEstimate
  ∷ missingSigmaWedgeCollapseExclusionProof
  ∷ missingSupportClassificationExhaustion
  ∷ missingMicrolocalDefectMassConstruction
  ∷ missingNoZeroModeDegeneracyRidingCascade
  ∷ missingNSCriticalResidualNonPositive
  ∷ missingFullLocalDefectMonotonicity
  ∷ missingMechanismExhaustionForFullClayNS
  ∷ clayNavierStokesPromotionClosed
  ∷ []

zeroModeSetClassificationBlockerCount : Nat
zeroModeSetClassificationBlockerCount =
  listLength canonicalNSZeroModeSetClassificationBlockers

zeroModeSetClassificationBlockerCountIs12 :
  zeroModeSetClassificationBlockerCount ≡ 12
zeroModeSetClassificationBlockerCountIs12 =
  refl

data NSZeroModeSetClassificationStatus : Set where
  rankOneFormulaImportedStatus :
    NSZeroModeSetClassificationStatus

  zeroModeBranchesTypedStatus :
    NSZeroModeSetClassificationStatus

  supportCasesTypedStatus :
    NSZeroModeSetClassificationStatus

  leakageTargetTypedStatus :
    NSZeroModeSetClassificationStatus

  radialRigidityTargetTypedStatus :
    NSZeroModeSetClassificationStatus

  tangentialStarvationTargetTypedStatus :
    NSZeroModeSetClassificationStatus

  sigmaWedgeTargetTypedStatus :
    NSZeroModeSetClassificationStatus

  microlocalMassStillFalseStatus :
    NSZeroModeSetClassificationStatus

  residualDepletionStillFalseStatus :
    NSZeroModeSetClassificationStatus

  clayPromotionFalseStatus :
    NSZeroModeSetClassificationStatus

canonicalNSZeroModeSetClassificationStatuses :
  List NSZeroModeSetClassificationStatus
canonicalNSZeroModeSetClassificationStatuses =
  rankOneFormulaImportedStatus
  ∷ zeroModeBranchesTypedStatus
  ∷ supportCasesTypedStatus
  ∷ leakageTargetTypedStatus
  ∷ radialRigidityTargetTypedStatus
  ∷ tangentialStarvationTargetTypedStatus
  ∷ sigmaWedgeTargetTypedStatus
  ∷ microlocalMassStillFalseStatus
  ∷ residualDepletionStillFalseStatus
  ∷ clayPromotionFalseStatus
  ∷ []

zeroModeSetClassificationStatusCount : Nat
zeroModeSetClassificationStatusCount =
  listLength canonicalNSZeroModeSetClassificationStatuses

zeroModeSetClassificationStatusCountIs10 :
  zeroModeSetClassificationStatusCount ≡ 10
zeroModeSetClassificationStatusCountIs10 =
  refl

data NSZeroModeSetClassificationPromotion : Set where

nsZeroModeSetClassificationPromotionImpossibleHere :
  NSZeroModeSetClassificationPromotion →
  ⊥
nsZeroModeSetClassificationPromotionImpossibleHere ()

zeroModeClassificationName : String
zeroModeClassificationName =
  "NSZeroModeSetClassificationBoundary"

lambdaDeltaText : String
lambdaDeltaText =
  "lambda_Delta(theta) = one-quarter times sin^2(2 alpha(theta))"

zeroModeUnionText : String
zeroModeUnionText =
  "Z_NS is the union of Z_rad, where e_+ is parallel to theta, and Z_tan, where e_+ is perpendicular to theta"

supportGapText : String
supportGapText =
  "exact remaining support-classification gap: classify defect-measure support across away-from-zero, radial zero-mode, tangential zero-mode, shrinking Sigma wedge, and unclassified residual cases"

nonPromotionBoundaryText : String
nonPromotionBoundaryText =
  "This module records the NS zero-mode classification target only; leakage, zero-mode rigidity, microlocal mass, critical-residual depletion, Clay NS, and terminal promotion remain false."

NSZeroModeSetClassificationBoundaryRecorded : Bool
NSZeroModeSetClassificationBoundaryRecorded =
  true

RankOneDefectLaplacianFormulaImported : Bool
RankOneDefectLaplacianFormulaImported =
  true

ZeroModeSetDefined : Bool
ZeroModeSetDefined =
  true

LeakageAwayFromZeroModesTargetRecorded : Bool
LeakageAwayFromZeroModesTargetRecorded =
  true

RadialZeroModeRigidityTargetRecorded : Bool
RadialZeroModeRigidityTargetRecorded =
  true

TangentialZeroModePressureStarvationTargetRecorded : Bool
TangentialZeroModePressureStarvationTargetRecorded =
  true

SigmaWedgeCollapseTargetRecorded : Bool
SigmaWedgeCollapseTargetRecorded =
  true

SupportClassificationGapRecorded : Bool
SupportClassificationGapRecorded =
  true

LeiRenTianAuthorityAccepted : Bool
LeiRenTianAuthorityAccepted =
  false

RadialZeroModeRigidityProved : Bool
RadialZeroModeRigidityProved =
  false

TangentialZeroModePressureStarvationProved : Bool
TangentialZeroModePressureStarvationProved =
  false

LeakageAwayFromZeroModesProved : Bool
LeakageAwayFromZeroModesProved =
  false

SigmaWedgeCollapseExclusionProved : Bool
SigmaWedgeCollapseExclusionProved =
  false

SupportClassificationExhausted : Bool
SupportClassificationExhausted =
  false

MicrolocalDefectMassConstructed : Bool
MicrolocalDefectMassConstructed =
  false

NoZeroModeDegeneracyRidingCascade : Bool
NoZeroModeDegeneracyRidingCascade =
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

organizationString : String
organizationString =
  "O: Worker lane 2 owns the NS zero-mode classification boundary module only."

requirementString : String
requirementString =
  "R: Define the NS defect-Laplacian zero-mode set from the rank-one formula, record Z_rad union Z_tan, and type the leakage/wedge/support-classification targets without promotion."

codeArtifactString : String
codeArtifactString =
  "C: DASHI.Physics.Closure.NSZeroModeSetClassificationBoundary exports zero-mode carriers, support cases, target rows, blocker rows, status rows, ORCSLPGF, and a canonical non-promoting receipt."

stateString : String
stateString =
  "S: rank-one algebra, finite non-radial averaging, transverse Sigma geometry, Sigma lower-bound target, and microlocal defect-mass boundary are imported; zero-mode rigidity and support exhaustion remain unproved."

latticeString : String
latticeString =
  "L: rank-one defect eigenvalue -> Z_rad/Z_tan classification -> leakage away from zero modes or rigidity/starvation/wedge targets -> microlocal mass -> residual depletion -> Clay blockers."

proposalString : String
proposalString =
  "P: Promote only the zero-mode classification boundary as an executable Agda surface; leave all PDE, authority, and Clay claims false."

governanceString : String
governanceString =
  "G: Internal algebra anchors are true; Lei-Ren-Tian authority, radial/tangential rigidity, leakage estimates, microlocal mass, mechanism exhaustion, Clay NS, and terminal promotion remain false."

gapString : String
gapString =
  "F: Remaining gap is support classification for blowup defect measures: prove away-from-zero leakage, radial zero-mode obstruction, tangential pressure starvation, Sigma wedge exclusion, microlocal mass, and no positive critical residual cascade."

record NSZeroModeSetClassificationORCSLPGF : Set where
  constructor nsZeroModeSetClassificationORCSLPGF
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

open NSZeroModeSetClassificationORCSLPGF public

canonicalNSZeroModeSetClassificationORCSLPGF :
  NSZeroModeSetClassificationORCSLPGF
canonicalNSZeroModeSetClassificationORCSLPGF =
  nsZeroModeSetClassificationORCSLPGF
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

record NSZeroModeSetClassificationBoundaryReceipt : Setω where
  constructor nsZeroModeSetClassificationBoundaryReceipt
  field
    theoremName :
      String
    theoremNameIsCanonical :
      theoremName ≡ zeroModeClassificationName

    rankOneFormulaAnchor :
      RankOne.NSRankOneProjectionCommutatorFormula
    rankOneFormulaRecorded :
      RankOne.correctedFormulaRecorded rankOneFormulaAnchor ≡ true
    rankOneClayStillFalse :
      RankOne.navierStokesClayPromoted rankOneFormulaAnchor ≡ false
    rankOneTerminalStillFalse :
      RankOne.terminalPromotion rankOneFormulaAnchor ≡ false

    nonRadialAverageAnchor :
      NonRadial.NSNonRadialityQuantificationAverageReceipt
    nonRadialAverageRecorded :
      NonRadial.FiniteFourSampleAverageRecorded ≡ true
    nonRadialAverageTheoremStillFalse :
      NonRadial.SigmaNonRadialCommutatorLowerBoundProved ≡ false

    transverseSigmaAnchor :
      Transverse.NSTransverseSigmaNeighborhoodGeometryReceipt
    transverseTargetRecorded :
      Transverse.TransverseSigmaNeighborhoodGeometryTargetRecorded ≡ true
    transverseGeometryStillFalse :
      Transverse.InternalTransverseChartProofAccepted ≡ false

    sigmaLowerBoundTargetAnchor :
      Sigma.NSSigmaNonRadialCommutatorLowerBoundTargetReceipt
    sigmaTargetRecorded :
      Sigma.SigmaNonRadialCommutatorLowerBoundTargetRecorded ≡ true
    sigmaLowerBoundStillFalse :
      Sigma.SigmaNonRadialCommutatorLowerBound ≡ false

    microlocalDefectMassAnchor :
      Micro.NSMicrolocalDefectMassConstructionBoundaryReceipt
    microlocalBoundaryRecorded :
      Micro.NSMicrolocalDefectMassConstructionBoundaryRecorded ≡ true
    microlocalMassStillFalse :
      Micro.MicrolocalDefectMassConstructed ≡ false

    eigenvalueExpression :
      DefectLaplacianEigenvalueExpression
    eigenvalueExpressionIsCanonical :
      eigenvalueExpression ≡ oneQuarterSinSquaredTwoAlpha
    eigenvalueExpressionText :
      String
    eigenvalueExpressionTextIsCanonical :
      eigenvalueExpressionText ≡ lambdaDeltaText

    zeroModeBranches :
      List NSZeroModeBranch
    zeroModeBranchesAreCanonical :
      zeroModeBranches ≡ canonicalNSZeroModeBranches
    zeroModeBranchCount :
      Nat
    zeroModeBranchCountIsTwo :
      zeroModeBranchCount ≡ 2

    radialCondition :
      zeroModeCondition radialZeroModeBranch ≡ ePlusParallelTheta
    tangentialCondition :
      zeroModeCondition tangentialZeroModeBranch ≡ ePlusPerpendicularTheta

    zeroModeSetComponents :
      List NSZeroModeSet
    zeroModeSetComponentsAreCanonical :
      zeroModeSetComponents ≡ canonicalNSZeroModeSetComponents
    zeroModeSetComponentCount :
      Nat
    zeroModeSetComponentCountIsTwo :
      zeroModeSetComponentCount ≡ 2
    zeroModeUnionDescription :
      String
    zeroModeUnionDescriptionIsCanonical :
      zeroModeUnionDescription ≡ zeroModeUnionText

    supportCases :
      List DefectMeasureSupportRegion
    supportCasesAreCanonical :
      supportCases ≡ canonicalSupportClassificationCases
    supportCaseCount :
      Nat
    supportCaseCountIsFive :
      supportCaseCount ≡ 5

    leakageAwayTarget :
      ZeroModeCaseTarget
    leakageAwayTargetIsCanonical :
      leakageAwayTarget ≡ canonicalLeakageAwayFromZeroModesTarget
    radialRigidityTarget :
      ZeroModeCaseTarget
    radialRigidityTargetIsCanonical :
      radialRigidityTarget ≡ canonicalRadialZeroModeRigidityTarget
    tangentialStarvationTarget :
      ZeroModeCaseTarget
    tangentialStarvationTargetIsCanonical :
      tangentialStarvationTarget
      ≡
      canonicalTangentialZeroModeStarvationTarget
    sigmaWedgeTarget :
      ZeroModeCaseTarget
    sigmaWedgeTargetIsCanonical :
      sigmaWedgeTarget ≡ canonicalSigmaWedgeCollapseTarget
    supportExhaustionTarget :
      ZeroModeCaseTarget
    supportExhaustionTargetIsCanonical :
      supportExhaustionTarget
      ≡
      canonicalSupportClassificationExhaustionTarget

    rows :
      List NSZeroModeSetClassificationRow
    rowsAreCanonical :
      rows ≡ canonicalNSZeroModeSetClassificationRows
    rowCount :
      Nat
    rowCountIs15 :
      rowCount ≡ 15
    blockers :
      List NSZeroModeSetClassificationBlocker
    blockersAreCanonical :
      blockers ≡ canonicalNSZeroModeSetClassificationBlockers
    blockerCount :
      Nat
    blockerCountIs12 :
      blockerCount ≡ 12
    statuses :
      List NSZeroModeSetClassificationStatus
    statusesAreCanonical :
      statuses ≡ canonicalNSZeroModeSetClassificationStatuses
    statusCount :
      Nat
    statusCountIs10 :
      statusCount ≡ 10

    boundaryRecorded :
      NSZeroModeSetClassificationBoundaryRecorded ≡ true
    rankOneDefectLaplacianFormulaImported :
      RankOneDefectLaplacianFormulaImported ≡ true
    zeroModeSetDefined :
      ZeroModeSetDefined ≡ true
    leakageAwayFromZeroModesTargetRecorded :
      LeakageAwayFromZeroModesTargetRecorded ≡ true
    radialZeroModeRigidityTargetRecorded :
      RadialZeroModeRigidityTargetRecorded ≡ true
    tangentialZeroModePressureStarvationTargetRecorded :
      TangentialZeroModePressureStarvationTargetRecorded ≡ true
    sigmaWedgeCollapseTargetRecorded :
      SigmaWedgeCollapseTargetRecorded ≡ true
    supportClassificationGapRecorded :
      SupportClassificationGapRecorded ≡ true

    leiRenTianAuthorityAccepted :
      LeiRenTianAuthorityAccepted ≡ false
    radialZeroModeRigidityProved :
      RadialZeroModeRigidityProved ≡ false
    tangentialZeroModePressureStarvationProved :
      TangentialZeroModePressureStarvationProved ≡ false
    leakageAwayFromZeroModesProved :
      LeakageAwayFromZeroModesProved ≡ false
    sigmaWedgeCollapseExclusionProved :
      SigmaWedgeCollapseExclusionProved ≡ false
    supportClassificationExhausted :
      SupportClassificationExhausted ≡ false
    microlocalDefectMassConstructed :
      MicrolocalDefectMassConstructed ≡ false
    noZeroModeDegeneracyRidingCascade :
      NoZeroModeDegeneracyRidingCascade ≡ false
    nsCriticalResidualNonPositive :
      NSCriticalResidualNonPositive ≡ false
    fullLocalDefectMonotonicity :
      FullLocalDefectMonotonicity ≡ false
    mechanismExhaustionForFullClayNS :
      MechanismExhaustionForFullClayNS ≡ false
    fullClayNSSolvedFalse :
      fullClayNSSolved ≡ false
    fullClayNSSolvedSnakeFalse :
      full_clay_ns_solved ≡ false
    clayNavierStokesPromotedFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionFalse :
      terminalPromotion ≡ false

    promotionFlags :
      List NSZeroModeSetClassificationPromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []
    supportClassificationGap :
      String
    supportClassificationGapIsCanonical :
      supportClassificationGap ≡ supportGapText
    nonPromotionBoundary :
      String
    nonPromotionBoundaryIsCanonical :
      nonPromotionBoundary ≡ nonPromotionBoundaryText
    orcslpgf :
      NSZeroModeSetClassificationORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSZeroModeSetClassificationORCSLPGF
    remainingObligations :
      List String

open NSZeroModeSetClassificationBoundaryReceipt public

canonicalNSZeroModeSetClassificationBoundaryReceipt :
  NSZeroModeSetClassificationBoundaryReceipt
canonicalNSZeroModeSetClassificationBoundaryReceipt =
  record
    { theoremName =
        zeroModeClassificationName
    ; theoremNameIsCanonical =
        refl
    ; rankOneFormulaAnchor =
        RankOne.canonicalNSRankOneProjectionCommutatorFormula
    ; rankOneFormulaRecorded =
        refl
    ; rankOneClayStillFalse =
        refl
    ; rankOneTerminalStillFalse =
        refl
    ; nonRadialAverageAnchor =
        NonRadial.canonicalNSNonRadialityQuantificationAverageReceipt
    ; nonRadialAverageRecorded =
        refl
    ; nonRadialAverageTheoremStillFalse =
        refl
    ; transverseSigmaAnchor =
        Transverse.canonicalNSTransverseSigmaNeighborhoodGeometryReceipt
    ; transverseTargetRecorded =
        refl
    ; transverseGeometryStillFalse =
        refl
    ; sigmaLowerBoundTargetAnchor =
        Sigma.canonicalNSSigmaNonRadialCommutatorLowerBoundTargetReceipt
    ; sigmaTargetRecorded =
        refl
    ; sigmaLowerBoundStillFalse =
        refl
    ; microlocalDefectMassAnchor =
        Micro.canonicalNSMicrolocalDefectMassConstructionBoundaryReceipt
    ; microlocalBoundaryRecorded =
        refl
    ; microlocalMassStillFalse =
        refl
    ; eigenvalueExpression =
        oneQuarterSinSquaredTwoAlpha
    ; eigenvalueExpressionIsCanonical =
        refl
    ; eigenvalueExpressionText =
        lambdaDeltaText
    ; eigenvalueExpressionTextIsCanonical =
        refl
    ; zeroModeBranches =
        canonicalNSZeroModeBranches
    ; zeroModeBranchesAreCanonical =
        refl
    ; zeroModeBranchCount =
        nsZeroModeBranchCount
    ; zeroModeBranchCountIsTwo =
        refl
    ; radialCondition =
        refl
    ; tangentialCondition =
        refl
    ; zeroModeSetComponents =
        canonicalNSZeroModeSetComponents
    ; zeroModeSetComponentsAreCanonical =
        refl
    ; zeroModeSetComponentCount =
        nsZeroModeSetComponentCount
    ; zeroModeSetComponentCountIsTwo =
        refl
    ; zeroModeUnionDescription =
        zeroModeUnionText
    ; zeroModeUnionDescriptionIsCanonical =
        refl
    ; supportCases =
        canonicalSupportClassificationCases
    ; supportCasesAreCanonical =
        refl
    ; supportCaseCount =
        supportClassificationCaseCount
    ; supportCaseCountIsFive =
        refl
    ; leakageAwayTarget =
        canonicalLeakageAwayFromZeroModesTarget
    ; leakageAwayTargetIsCanonical =
        refl
    ; radialRigidityTarget =
        canonicalRadialZeroModeRigidityTarget
    ; radialRigidityTargetIsCanonical =
        refl
    ; tangentialStarvationTarget =
        canonicalTangentialZeroModeStarvationTarget
    ; tangentialStarvationTargetIsCanonical =
        refl
    ; sigmaWedgeTarget =
        canonicalSigmaWedgeCollapseTarget
    ; sigmaWedgeTargetIsCanonical =
        refl
    ; supportExhaustionTarget =
        canonicalSupportClassificationExhaustionTarget
    ; supportExhaustionTargetIsCanonical =
        refl
    ; rows =
        canonicalNSZeroModeSetClassificationRows
    ; rowsAreCanonical =
        refl
    ; rowCount =
        zeroModeSetClassificationRowCount
    ; rowCountIs15 =
        refl
    ; blockers =
        canonicalNSZeroModeSetClassificationBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCount =
        zeroModeSetClassificationBlockerCount
    ; blockerCountIs12 =
        refl
    ; statuses =
        canonicalNSZeroModeSetClassificationStatuses
    ; statusesAreCanonical =
        refl
    ; statusCount =
        zeroModeSetClassificationStatusCount
    ; statusCountIs10 =
        refl
    ; boundaryRecorded =
        refl
    ; rankOneDefectLaplacianFormulaImported =
        refl
    ; zeroModeSetDefined =
        refl
    ; leakageAwayFromZeroModesTargetRecorded =
        refl
    ; radialZeroModeRigidityTargetRecorded =
        refl
    ; tangentialZeroModePressureStarvationTargetRecorded =
        refl
    ; sigmaWedgeCollapseTargetRecorded =
        refl
    ; supportClassificationGapRecorded =
        refl
    ; leiRenTianAuthorityAccepted =
        refl
    ; radialZeroModeRigidityProved =
        refl
    ; tangentialZeroModePressureStarvationProved =
        refl
    ; leakageAwayFromZeroModesProved =
        refl
    ; sigmaWedgeCollapseExclusionProved =
        refl
    ; supportClassificationExhausted =
        refl
    ; microlocalDefectMassConstructed =
        refl
    ; noZeroModeDegeneracyRidingCascade =
        refl
    ; nsCriticalResidualNonPositive =
        refl
    ; fullLocalDefectMonotonicity =
        refl
    ; mechanismExhaustionForFullClayNS =
        refl
    ; fullClayNSSolvedFalse =
        refl
    ; fullClayNSSolvedSnakeFalse =
        refl
    ; clayNavierStokesPromotedFalse =
        refl
    ; terminalPromotionFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; supportClassificationGap =
        supportGapText
    ; supportClassificationGapIsCanonical =
        refl
    ; nonPromotionBoundary =
        nonPromotionBoundaryText
    ; nonPromotionBoundaryIsCanonical =
        refl
    ; orcslpgf =
        canonicalNSZeroModeSetClassificationORCSLPGF
    ; orcslpgfIsCanonical =
        refl
    ; remainingObligations =
        "import and pin Lei-Ren-Tian great-circle theorem as an external authority token"
        ∷ "prove radial zero-mode incompressibility obstruction for blowup defect measures"
        ∷ "prove tangential zero-mode pressure starvation as a deterministic ancient-profile estimate"
        ∷ "prove leakage away from zero modes using the Sigma commutator lower-bound target"
        ∷ "prove shrinking Sigma wedge exclusion or compactness failure"
        ∷ "construct nontrivial microlocal defect mass from arbitrary blowup sequences"
        ∷ "combine support cases into NoZeroModeDegeneracyRidingCascade"
        ∷ "derive NSCriticalResidualNonPositive and FullLocalDefectMonotonicity"
        ∷ "complete MechanismExhaustionForFullClayNS before any Clay promotion"
        ∷ []
    }
