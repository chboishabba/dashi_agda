module DASHI.Physics.Closure.ProjectionNonlocalityDefectLaplacianZeroModeSheaf where

-- Shared P0 zero-mode frontier:
--
--   Delta_{Pi,N} = Pi N^dagger (1 - Pi) N Pi
--
-- A critical obstruction either carries positive defect-Laplacian energy and
-- pays leakage/coercivity, or lies in the zero-mode sheaf and must be
-- classified by a rigidity theorem.  This module records that object and the
-- current NS/YM/Core instance rows only.  It does not prove the defect
-- Laplacian theorem, zero-mode rigidity, continuum transfer, Clay, or terminal
-- promotion.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.CompatibilityLeakageCoercivityTrichotomy as CLC
import DASHI.Physics.Closure.ProjectionNonlocalityLeakagePrincipleBoundary as Base
import DASHI.Physics.Closure.Sprint166ProjectionNonlocalityLeakagePrincipleReceipt as S166
import DASHI.Physics.Closure.UniformProjectionNonlocalityGapFinite as FiniteGap

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

data DefectLaplacianSymbolPart : Set where
  leftProjectionPi :
    DefectLaplacianSymbolPart

  nonlocalAdjointNDagger :
    DefectLaplacianSymbolPart

  offProjectionOneMinusPi :
    DefectLaplacianSymbolPart

  nonlocalOperatorN :
    DefectLaplacianSymbolPart

  rightProjectionPi :
    DefectLaplacianSymbolPart

canonicalDefectLaplacianSymbol :
  List DefectLaplacianSymbolPart
canonicalDefectLaplacianSymbol =
  leftProjectionPi
  ∷ nonlocalAdjointNDagger
  ∷ offProjectionOneMinusPi
  ∷ nonlocalOperatorN
  ∷ rightProjectionPi
  ∷ []

defectLaplacianSymbolText : String
defectLaplacianSymbolText =
  "Delta_{Pi,N} = Pi N^dagger (1-Pi) N Pi"

defectLaplacianEnergyIdentityText : String
defectLaplacianEnergyIdentityText =
  "<f, Delta_{Pi,N} f> = ||(1-Pi) N Pi f||^2 for f in im Pi"

data ZeroModeSheafObject : Set where
  imageProjectionSector :
    ZeroModeSheafObject

  defectLaplacianKernel :
    ZeroModeSheafObject

  leakagePositiveComplement :
    ZeroModeSheafObject

  zeroModeRigidityClassifier :
    ZeroModeSheafObject

canonicalZeroModeSheafObjects :
  List ZeroModeSheafObject
canonicalZeroModeSheafObjects =
  imageProjectionSector
  ∷ defectLaplacianKernel
  ∷ leakagePositiveComplement
  ∷ zeroModeRigidityClassifier
  ∷ []

data ZeroModeAlternativeBranch : Set where
  leakagePositiveBranch :
    ZeroModeAlternativeBranch

  zeroModeRigidBranch :
    ZeroModeAlternativeBranch

branchLabel : ZeroModeAlternativeBranch → String
branchLabel leakagePositiveBranch =
  "positive defect-Laplacian energy pays leakage or coercivity"
branchLabel zeroModeRigidBranch =
  "zero-mode sector is classified by a rigidity theorem"

data ZeroModeInstanceLane : Set where
  navierStokesZeroModeLane :
    ZeroModeInstanceLane

  yangMillsZeroModeLane :
    ZeroModeInstanceLane

  coreUnificationZeroModeLane :
    ZeroModeInstanceLane

laneLabel : ZeroModeInstanceLane → String
laneLabel navierStokesZeroModeLane =
  "Navier-Stokes pressure/strain zero-mode sheaf"
laneLabel yangMillsZeroModeLane =
  "Yang-Mills finite Hodge/gauge zero-mode sheaf"
laneLabel coreUnificationZeroModeLane =
  "Core defect/admissibility quotient zero-mode seam"

laneProjectionObject : ZeroModeInstanceLane → String
laneProjectionObject navierStokesZeroModeLane =
  "Pi = maximal strain eigenprojection P_+(theta)"
laneProjectionObject yangMillsZeroModeLane =
  "Pi = gauge-compatible finite Hodge quotient projection"
laneProjectionObject coreUnificationZeroModeLane =
  "Pi = admissibility quotient representative projection"

laneNonlocalObject : ZeroModeInstanceLane → String
laneNonlocalObject navierStokesZeroModeLane =
  "N = pressure Riesz tensor channel R_i R_j"
laneNonlocalObject yangMillsZeroModeLane =
  "N = finite covariant codifferential / transfer closure"
laneNonlocalObject coreUnificationZeroModeLane =
  "N = hierarchy lift-project defect propagation"

laneZeroModeDescription : ZeroModeInstanceLane → String
laneZeroModeDescription navierStokesZeroModeLane =
  "Z_NS = Z_rad union Z_tan, with Sigma wedge escape tracked separately"
laneZeroModeDescription yangMillsZeroModeLane =
  "Z_YM,d = finite fields where weighted Hodge star realizes the gauge adjoint"
laneZeroModeDescription coreUnificationZeroModeLane =
  "Z_core = admissible low-defect quotient representatives with vanishing four-point defect"

laneNextRigidityTheorem : ZeroModeInstanceLane → String
laneNextRigidityTheorem navierStokesZeroModeLane =
  "exclude radial/tangential/wedge support for ancient blowup defect measures"
laneNextRigidityTheorem yangMillsZeroModeLane =
  "show non-vacuum gauge-compatible zero modes have Hamiltonian energy at least m_d"
laneNextRigidityTheorem coreUnificationZeroModeLane =
  "prove hierarchy consistency kills the four-point parallelogram defect"

data ZeroModeHardBlocker : Set where
  missingNSMicrolocalDefectMassAndZeroModeRigidity :
    ZeroModeHardBlocker

  missingYMHamiltonianDominationAndGaugeQuotientRigidity :
    ZeroModeHardBlocker

  missingCoreFourPointDefectElimination :
    ZeroModeHardBlocker

laneBlocker : ZeroModeInstanceLane → ZeroModeHardBlocker
laneBlocker navierStokesZeroModeLane =
  missingNSMicrolocalDefectMassAndZeroModeRigidity
laneBlocker yangMillsZeroModeLane =
  missingYMHamiltonianDominationAndGaugeQuotientRigidity
laneBlocker coreUnificationZeroModeLane =
  missingCoreFourPointDefectElimination

data ZeroModeInstanceRowKind : Set where
  nsRadialTangentialZeroModeRow :
    ZeroModeInstanceRowKind

  ymGaugeHodgeCompatibleZeroModeRow :
    ZeroModeInstanceRowKind

  coreAdmissibilityFourPointZeroModeRow :
    ZeroModeInstanceRowKind

canonicalZeroModeInstanceRowKinds :
  List ZeroModeInstanceRowKind
canonicalZeroModeInstanceRowKinds =
  nsRadialTangentialZeroModeRow
  ∷ ymGaugeHodgeCompatibleZeroModeRow
  ∷ coreAdmissibilityFourPointZeroModeRow
  ∷ []

record ZeroModeInstanceRow : Set where
  constructor zeroModeInstanceRow
  field
    rowKind :
      ZeroModeInstanceRowKind

    lane :
      ZeroModeInstanceLane

    laneText :
      String

    laneTextIsCanonical :
      laneText ≡ laneLabel lane

    projectionObject :
      String

    projectionObjectIsCanonical :
      projectionObject ≡ laneProjectionObject lane

    nonlocalObject :
      String

    nonlocalObjectIsCanonical :
      nonlocalObject ≡ laneNonlocalObject lane

    zeroModeDescription :
      String

    zeroModeDescriptionIsCanonical :
      zeroModeDescription ≡ laneZeroModeDescription lane

    leakageBranch :
      ZeroModeAlternativeBranch

    leakageBranchIsCanonical :
      leakageBranch ≡ leakagePositiveBranch

    zeroModeBranch :
      ZeroModeAlternativeBranch

    zeroModeBranchIsCanonical :
      zeroModeBranch ≡ zeroModeRigidBranch

    nextRigidityTheorem :
      String

    nextRigidityTheoremIsCanonical :
      nextRigidityTheorem ≡ laneNextRigidityTheorem lane

    hardBlocker :
      ZeroModeHardBlocker

    hardBlockerMatchesLane :
      hardBlocker ≡ laneBlocker lane

    finiteSupportRecorded :
      Bool

    finiteSupportRecordedIsTrue :
      finiteSupportRecorded ≡ true

    rigidityTheoremProved :
      Bool

    rigidityTheoremProvedIsFalse :
      rigidityTheoremProved ≡ false

    continuumTransferProved :
      Bool

    continuumTransferProvedIsFalse :
      continuumTransferProved ≡ false

    promotesLane :
      Bool

    promotesLaneIsFalse :
      promotesLane ≡ false

open ZeroModeInstanceRow public

mkZeroModeInstanceRow :
  ZeroModeInstanceRowKind →
  ZeroModeInstanceLane →
  ZeroModeInstanceRow
mkZeroModeInstanceRow kind lane =
  zeroModeInstanceRow
    kind
    lane
    (laneLabel lane)
    refl
    (laneProjectionObject lane)
    refl
    (laneNonlocalObject lane)
    refl
    (laneZeroModeDescription lane)
    refl
    leakagePositiveBranch
    refl
    zeroModeRigidBranch
    refl
    (laneNextRigidityTheorem lane)
    refl
    (laneBlocker lane)
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl

nsZeroModeInstanceRow : ZeroModeInstanceRow
nsZeroModeInstanceRow =
  mkZeroModeInstanceRow
    nsRadialTangentialZeroModeRow
    navierStokesZeroModeLane

ymZeroModeInstanceRow : ZeroModeInstanceRow
ymZeroModeInstanceRow =
  mkZeroModeInstanceRow
    ymGaugeHodgeCompatibleZeroModeRow
    yangMillsZeroModeLane

coreZeroModeInstanceRow : ZeroModeInstanceRow
coreZeroModeInstanceRow =
  mkZeroModeInstanceRow
    coreAdmissibilityFourPointZeroModeRow
    coreUnificationZeroModeLane

canonicalZeroModeInstanceRows :
  List ZeroModeInstanceRow
canonicalZeroModeInstanceRows =
  nsZeroModeInstanceRow
  ∷ ymZeroModeInstanceRow
  ∷ coreZeroModeInstanceRow
  ∷ []

data ZeroModeSheafBlockerRow : Set where
  noDefectLaplacianTheorem :
    ZeroModeSheafBlockerRow

  noZeroModeSheafClassification :
    ZeroModeSheafBlockerRow

  noNSZeroModeCascadeExclusion :
    ZeroModeSheafBlockerRow

  noYMGaugeZeroModeSpectralRigidity :
    ZeroModeSheafBlockerRow

  noCoreFourPointDefectTheorem :
    ZeroModeSheafBlockerRow

  noContinuumOrClayPromotion :
    ZeroModeSheafBlockerRow

canonicalZeroModeSheafBlockers :
  List ZeroModeSheafBlockerRow
canonicalZeroModeSheafBlockers =
  noDefectLaplacianTheorem
  ∷ noZeroModeSheafClassification
  ∷ noNSZeroModeCascadeExclusion
  ∷ noYMGaugeZeroModeSpectralRigidity
  ∷ noCoreFourPointDefectTheorem
  ∷ noContinuumOrClayPromotion
  ∷ []

defectLaplacianObjectRecorded : Bool
defectLaplacianObjectRecorded =
  true

zeroModeSheafRecorded : Bool
zeroModeSheafRecorded =
  true

leakageZeroModeAlternativeRecorded : Bool
leakageZeroModeAlternativeRecorded =
  true

finiteGapSupportImported : Bool
finiteGapSupportImported =
  FiniteGap.finiteUniformProjectionNonlocalityGap

sprint166BoundaryImported : Bool
sprint166BoundaryImported =
  S166.Sprint166ProjectionNonlocalityReceiptRecorded

basePrincipleBoundaryImported : Bool
basePrincipleBoundaryImported =
  Base.ProjectionNonlocalityLeakagePrincipleTargetRecorded

trichotomyBranchImported : Bool
trichotomyBranchImported =
  true

defectLaplacianTheoremProved : Bool
defectLaplacianTheoremProved =
  false

zeroModeCascadeExclusionProved : Bool
zeroModeCascadeExclusionProved =
  false

nsZeroModeRigidityProved : Bool
nsZeroModeRigidityProved =
  false

ymGaugeZeroModeSpectralRigidityProved : Bool
ymGaugeZeroModeSpectralRigidityProved =
  false

coreFourPointZeroModeRigidityProved : Bool
coreFourPointZeroModeRigidityProved =
  false

continuumZeroModeTransferProved : Bool
continuumZeroModeTransferProved =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

clayYangMillsPromoted : Bool
clayYangMillsPromoted =
  false

semanticUnificationPromoted : Bool
semanticUnificationPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

defectLaplacianObjectRecordedIsTrue :
  defectLaplacianObjectRecorded ≡ true
defectLaplacianObjectRecordedIsTrue =
  refl

zeroModeSheafRecordedIsTrue :
  zeroModeSheafRecorded ≡ true
zeroModeSheafRecordedIsTrue =
  refl

leakageZeroModeAlternativeRecordedIsTrue :
  leakageZeroModeAlternativeRecorded ≡ true
leakageZeroModeAlternativeRecordedIsTrue =
  refl

finiteGapSupportImportedIsTrue :
  finiteGapSupportImported ≡ true
finiteGapSupportImportedIsTrue =
  FiniteGap.finiteUniformProjectionNonlocalityGapIsTrue

sprint166BoundaryImportedIsTrue :
  sprint166BoundaryImported ≡ true
sprint166BoundaryImportedIsTrue =
  refl

basePrincipleBoundaryImportedIsTrue :
  basePrincipleBoundaryImported ≡ true
basePrincipleBoundaryImportedIsTrue =
  Base.projectionNonlocalityRecordsPrincipleTarget

trichotomyBranchImportedIsTrue :
  trichotomyBranchImported ≡ true
trichotomyBranchImportedIsTrue =
  refl

defectLaplacianTheoremProvedIsFalse :
  defectLaplacianTheoremProved ≡ false
defectLaplacianTheoremProvedIsFalse =
  refl

zeroModeCascadeExclusionProvedIsFalse :
  zeroModeCascadeExclusionProved ≡ false
zeroModeCascadeExclusionProvedIsFalse =
  refl

nsZeroModeRigidityProvedIsFalse :
  nsZeroModeRigidityProved ≡ false
nsZeroModeRigidityProvedIsFalse =
  refl

ymGaugeZeroModeSpectralRigidityProvedIsFalse :
  ymGaugeZeroModeSpectralRigidityProved ≡ false
ymGaugeZeroModeSpectralRigidityProvedIsFalse =
  refl

coreFourPointZeroModeRigidityProvedIsFalse :
  coreFourPointZeroModeRigidityProved ≡ false
coreFourPointZeroModeRigidityProvedIsFalse =
  refl

continuumZeroModeTransferProvedIsFalse :
  continuumZeroModeTransferProved ≡ false
continuumZeroModeTransferProvedIsFalse =
  refl

clayNavierStokesPromotedIsFalse :
  clayNavierStokesPromoted ≡ false
clayNavierStokesPromotedIsFalse =
  refl

clayYangMillsPromotedIsFalse :
  clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse =
  refl

semanticUnificationPromotedIsFalse :
  semanticUnificationPromoted ≡ false
semanticUnificationPromotedIsFalse =
  refl

terminalPromotionIsFalse :
  terminalPromotion ≡ false
terminalPromotionIsFalse =
  refl

organizationString : String
organizationString =
  "O: ProjectionNonlocalityDefectLaplacianZeroModeSheaf records the shared P0 zero-mode object over NS, YM, and core unification lanes."

requirementString : String
requirementString =
  "R: Normalize Delta_{Pi,N}=Pi N^dagger (1-Pi) N Pi, its kernel sheaf, and the leakage-positive versus zero-mode-rigid alternative."

codeArtifactString : String
codeArtifactString =
  "C: This Agda module imports the trichotomy, base projection-nonlocality boundary, Sprint166 receipt, and finite gap receipt, then exports canonical zero-mode rows, blockers, flags, and equality guards."

stateString : String
stateString =
  "S: The object and alternatives are recorded; the defect-Laplacian theorem, zero-mode classification, rigidity, continuum transfer, Clay, and terminal promotion are unproved."

latticeString : String
latticeString =
  "L: compatibility/leakage/coercivity trichotomy -> defect Laplacian -> kernel sheaf -> leakage-positive complement or zero-mode rigidity -> open continuum and authority gates."

proposalString : String
proposalString =
  "P: Treat zero-mode classification as the next P0 frontier while preserving fail-closed promotion guards."

governanceString : String
governanceString =
  "G: True fields are source anchors, finite support, and target-recorded guards only; theorem, rigidity, continuum, Clay, semantic, and terminal fields are false."

gapString : String
gapString =
  "F: Missing proofs are Delta theorem, zero-mode sheaf classification, NS zero-mode cascade exclusion, YM gauge zero-mode spectral rigidity, core four-point defect elimination, and continuum transfer."

record ProjectionNonlocalityDefectLaplacianZeroModeSheafReceipt : Setω where
  constructor projectionNonlocalityDefectLaplacianZeroModeSheafReceipt
  field
    compatibilityLeakageCoercivityTrichotomy :
      CLC.CompatibilityLeakageCoercivityTrichotomy

    compatibilityLeakageCoercivityTrichotomyImported :
      Bool

    compatibilityLeakageCoercivityTrichotomyImportedIsTrue :
      compatibilityLeakageCoercivityTrichotomyImported ≡ true

    baseProjectionNonlocalityBoundary :
      Base.ProjectionNonlocalityLeakagePrincipleBoundaryReceipt

    baseProjectionNonlocalityBoundaryIsCanonical :
      baseProjectionNonlocalityBoundary
      ≡
      Base.canonicalProjectionNonlocalityLeakagePrincipleBoundaryReceipt

    sprint166ProjectionNonlocalityReceipt :
      S166.Sprint166ProjectionNonlocalityLeakagePrincipleReceipt

    sprint166ProjectionNonlocalityReceiptIsCanonical :
      sprint166ProjectionNonlocalityReceipt
      ≡
      S166.canonicalSprint166ProjectionNonlocalityLeakagePrincipleReceipt

    finiteProjectionNonlocalityGapReceipt :
      FiniteGap.UniformProjectionNonlocalityGapReceipt

    finiteProjectionNonlocalityGapReceiptIsCanonical :
      finiteProjectionNonlocalityGapReceipt
      ≡
      FiniteGap.canonicalUniformProjectionNonlocalityGapReceipt

    defectLaplacianSymbol :
      List DefectLaplacianSymbolPart

    defectLaplacianSymbolIsCanonical :
      defectLaplacianSymbol ≡ canonicalDefectLaplacianSymbol

    defectLaplacianFormula :
      String

    defectLaplacianFormulaIsCanonical :
      defectLaplacianFormula ≡ defectLaplacianSymbolText

    defectLaplacianEnergyIdentity :
      String

    defectLaplacianEnergyIdentityIsCanonical :
      defectLaplacianEnergyIdentity ≡ defectLaplacianEnergyIdentityText

    zeroModeSheafObjects :
      List ZeroModeSheafObject

    zeroModeSheafObjectsAreCanonical :
      zeroModeSheafObjects ≡ canonicalZeroModeSheafObjects

    instanceRowKinds :
      List ZeroModeInstanceRowKind

    instanceRowKindsAreCanonical :
      instanceRowKinds ≡ canonicalZeroModeInstanceRowKinds

    instanceRows :
      List ZeroModeInstanceRow

    instanceRowsAreCanonical :
      instanceRows ≡ canonicalZeroModeInstanceRows

    blockers :
      List ZeroModeSheafBlockerRow

    blockersAreCanonical :
      blockers ≡ canonicalZeroModeSheafBlockers

    symbolPartCount :
      Nat

    symbolPartCountIs5 :
      symbolPartCount ≡ 5

    zeroModeObjectCount :
      Nat

    zeroModeObjectCountIs4 :
      zeroModeObjectCount ≡ 4

    instanceRowCount :
      Nat

    instanceRowCountIs3 :
      instanceRowCount ≡ 3

    blockerCount :
      Nat

    blockerCountIs6 :
      blockerCount ≡ 6

    O :
      String

    OIsCanonical :
      O ≡ organizationString

    R :
      String

    RIsCanonical :
      R ≡ requirementString

    C :
      String

    CIsCanonical :
      C ≡ codeArtifactString

    S :
      String

    SIsCanonical :
      S ≡ stateString

    L :
      String

    LIsCanonical :
      L ≡ latticeString

    P :
      String

    PIsCanonical :
      P ≡ proposalString

    G :
      String

    GIsCanonical :
      G ≡ governanceString

    F :
      String

    FIsCanonical :
      F ≡ gapString

    defectLaplacianObjectRecordedField :
      defectLaplacianObjectRecorded ≡ true

    zeroModeSheafRecordedField :
      zeroModeSheafRecorded ≡ true

    leakageZeroModeAlternativeRecordedField :
      leakageZeroModeAlternativeRecorded ≡ true

    finiteGapSupportImportedField :
      finiteGapSupportImported ≡ true

    sprint166BoundaryImportedField :
      sprint166BoundaryImported ≡ true

    basePrincipleBoundaryImportedField :
      basePrincipleBoundaryImported ≡ true

    trichotomyBranchImportedField :
      trichotomyBranchImported ≡ true

    defectLaplacianTheoremFalseField :
      defectLaplacianTheoremProved ≡ false

    zeroModeCascadeExclusionFalseField :
      zeroModeCascadeExclusionProved ≡ false

    nsZeroModeRigidityFalseField :
      nsZeroModeRigidityProved ≡ false

    ymGaugeZeroModeSpectralRigidityFalseField :
      ymGaugeZeroModeSpectralRigidityProved ≡ false

    coreFourPointZeroModeRigidityFalseField :
      coreFourPointZeroModeRigidityProved ≡ false

    continuumZeroModeTransferFalseField :
      continuumZeroModeTransferProved ≡ false

    clayNavierStokesPromotedFalseField :
      clayNavierStokesPromoted ≡ false

    clayYangMillsPromotedFalseField :
      clayYangMillsPromoted ≡ false

    semanticUnificationPromotedFalseField :
      semanticUnificationPromoted ≡ false

    terminalPromotionFalseField :
      terminalPromotion ≡ false

open ProjectionNonlocalityDefectLaplacianZeroModeSheafReceipt public

canonicalProjectionNonlocalityDefectLaplacianZeroModeSheafReceipt :
  ProjectionNonlocalityDefectLaplacianZeroModeSheafReceipt
canonicalProjectionNonlocalityDefectLaplacianZeroModeSheafReceipt =
  projectionNonlocalityDefectLaplacianZeroModeSheafReceipt
    CLC.canonicalCompatibilityLeakageCoercivityTrichotomy
    true
    refl
    Base.canonicalProjectionNonlocalityLeakagePrincipleBoundaryReceipt
    refl
    S166.canonicalSprint166ProjectionNonlocalityLeakagePrincipleReceipt
    refl
    FiniteGap.canonicalUniformProjectionNonlocalityGapReceipt
    refl
    canonicalDefectLaplacianSymbol
    refl
    defectLaplacianSymbolText
    refl
    defectLaplacianEnergyIdentityText
    refl
    canonicalZeroModeSheafObjects
    refl
    canonicalZeroModeInstanceRowKinds
    refl
    canonicalZeroModeInstanceRows
    refl
    canonicalZeroModeSheafBlockers
    refl
    (listCount canonicalDefectLaplacianSymbol)
    refl
    (listCount canonicalZeroModeSheafObjects)
    refl
    (listCount canonicalZeroModeInstanceRows)
    refl
    (listCount canonicalZeroModeSheafBlockers)
    refl
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
    refl
    refl
    refl
    finiteGapSupportImportedIsTrue
    refl
    basePrincipleBoundaryImportedIsTrue
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

zeroModeSheafReceiptKeepsNSClayFalse :
  clayNavierStokesPromoted
  ≡
  false
zeroModeSheafReceiptKeepsNSClayFalse =
  refl

zeroModeSheafReceiptKeepsYMClayFalse :
  clayYangMillsPromoted
  ≡
  false
zeroModeSheafReceiptKeepsYMClayFalse =
  refl

zeroModeSheafReceiptKeepsTerminalFalse :
  terminalPromotion
  ≡
  false
zeroModeSheafReceiptKeepsTerminalFalse =
  refl

zeroModeSheafInstanceRowCountIsThree :
  listCount canonicalZeroModeInstanceRows
  ≡
  3
zeroModeSheafInstanceRowCountIsThree =
  refl
