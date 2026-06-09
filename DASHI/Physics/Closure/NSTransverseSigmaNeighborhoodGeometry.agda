module DASHI.Physics.Closure.NSTransverseSigmaNeighborhoodGeometry where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSRankOneProjectionCommutatorFormula as RankOne
import DASHI.Physics.Closure.NSSigmaNonRadialCommutatorLowerBoundTarget as SigmaTarget
import DASHI.Physics.Closure.NSSprint163TopologicalAlignmentObstructionBoundaryReceipt as S163

------------------------------------------------------------------------
-- Transverse Sigma neighborhood geometry for the NS pressure/strain
-- commutator route.
--
-- This file records the next local geometric proof boundary:
--
--   TransverseSigmaNeighborhoodGeometry
--
-- It packages a symbol-level local chart around the angular strain-symbol
-- degeneracy locus Sigma, two tangential directions, a first-order splitting
-- witness, and the linear lower-bound target needed by
-- SigmaNonRadialCommutatorLowerBound.  It consumes the Sprint 163
-- source-bound Sanni vocabulary, the corrected Sigma non-radial lower-bound
-- target, and the checked finite rank-one projection commutator formula.
--
-- It deliberately does not accept Sanni as an internal PDE theorem, does not
-- prove microlocal defect mass, does not prove pressure control, and does not
-- promote Clay NS.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

data SigmaLocalChart : Set where
  transverseAngularStrainSigmaChart :
    SigmaLocalChart

data SigmaChartCenter : Set where
  transverseDegeneracyPointTheta0 :
    SigmaChartCenter

data SigmaTangentDirection : Set where
  etaOneTangentialDirection :
    SigmaTangentDirection

  etaTwoTangentialDirection :
    SigmaTangentDirection

canonicalSigmaTangentialDirections :
  List SigmaTangentDirection
canonicalSigmaTangentialDirections =
  etaOneTangentialDirection
  ∷ etaTwoTangentialDirection
  ∷ []

sigmaTangentialDirectionCount : Nat
sigmaTangentialDirectionCount =
  2

sigmaTangentialDirectionCountIsTwo :
  sigmaTangentialDirectionCount ≡ 2
sigmaTangentialDirectionCountIsTwo =
  refl

data TangentialDerivativeWitness : Set where
  derivativeAOne :
    SigmaTangentDirection →
    TangentialDerivativeWitness

  derivativeATwo :
    SigmaTangentDirection →
    TangentialDerivativeWitness

canonicalTangentialDerivativeWitnesses :
  List TangentialDerivativeWitness
canonicalTangentialDerivativeWitnesses =
  derivativeAOne etaOneTangentialDirection
  ∷ derivativeATwo etaTwoTangentialDirection
  ∷ []

tangentialDerivativeWitnessCount : Nat
tangentialDerivativeWitnessCount =
  2

tangentialDerivativeWitnessCountIsTwo :
  tangentialDerivativeWitnessCount ≡ 2
tangentialDerivativeWitnessCountIsTwo =
  refl

data FirstOrderSplitWitness : Set where
  firstOrderLinearSymbolSplit :
    SigmaLocalChart →
    SigmaChartCenter →
    TangentialDerivativeWitness →
    TangentialDerivativeWitness →
    FirstOrderSplitWitness

canonicalFirstOrderSplitWitness :
  FirstOrderSplitWitness
canonicalFirstOrderSplitWitness =
  firstOrderLinearSymbolSplit
    transverseAngularStrainSigmaChart
    transverseDegeneracyPointTheta0
    (derivativeAOne etaOneTangentialDirection)
    (derivativeATwo etaTwoTangentialDirection)

data SigmaTransversalityWitness : Set where
  twoIndependentTangentialDerivatives :
    FirstOrderSplitWitness →
    SigmaTransversalityWitness

canonicalSigmaTransversalityWitness :
  SigmaTransversalityWitness
canonicalSigmaTransversalityWitness =
  twoIndependentTangentialDerivatives canonicalFirstOrderSplitWitness

data EigenvalueSplitLowerBoundTarget : Set where
  linearEigenvalueSplitLowerBound :
    SigmaTransversalityWitness →
    EigenvalueSplitLowerBoundTarget

canonicalEigenvalueSplitLowerBoundTarget :
  EigenvalueSplitLowerBoundTarget
canonicalEigenvalueSplitLowerBoundTarget =
  linearEigenvalueSplitLowerBound canonicalSigmaTransversalityWitness

data AnnularNeighborhoodTarget : Set where
  sigmaAnnulusDeltaOverTwoToDelta :
    SigmaLocalChart →
    AnnularNeighborhoodTarget

canonicalAnnularNeighborhoodTarget :
  AnnularNeighborhoodTarget
canonicalAnnularNeighborhoodTarget =
  sigmaAnnulusDeltaOverTwoToDelta transverseAngularStrainSigmaChart

data TransverseSigmaNeighborhoodGeometryRow : Set where
  sprint163AngularSigmaVocabularyAnchorRow :
    TransverseSigmaNeighborhoodGeometryRow

  sigmaNonRadialTargetAnchorRow :
    TransverseSigmaNeighborhoodGeometryRow

  rankOneProjectionFormulaAnchorRow :
    TransverseSigmaNeighborhoodGeometryRow

  transverseLocalChartRecordedRow :
    TransverseSigmaNeighborhoodGeometryRow

  sigmaCenterThetaZeroRecordedRow :
    TransverseSigmaNeighborhoodGeometryRow

  twoTangentialDirectionsRecordedRow :
    TransverseSigmaNeighborhoodGeometryRow

  firstOrderSplitWitnessRecordedRow :
    TransverseSigmaNeighborhoodGeometryRow

  independentDerivativeWitnessRecordedRow :
    TransverseSigmaNeighborhoodGeometryRow

  linearEigenvalueSplitLowerBoundTargetRow :
    TransverseSigmaNeighborhoodGeometryRow

  annularNeighborhoodTargetRecordedRow :
    TransverseSigmaNeighborhoodGeometryRow

  noPDEPromotionGuardRow :
    TransverseSigmaNeighborhoodGeometryRow

canonicalTransverseSigmaNeighborhoodGeometryRows :
  List TransverseSigmaNeighborhoodGeometryRow
canonicalTransverseSigmaNeighborhoodGeometryRows =
  sprint163AngularSigmaVocabularyAnchorRow
  ∷ sigmaNonRadialTargetAnchorRow
  ∷ rankOneProjectionFormulaAnchorRow
  ∷ transverseLocalChartRecordedRow
  ∷ sigmaCenterThetaZeroRecordedRow
  ∷ twoTangentialDirectionsRecordedRow
  ∷ firstOrderSplitWitnessRecordedRow
  ∷ independentDerivativeWitnessRecordedRow
  ∷ linearEigenvalueSplitLowerBoundTargetRow
  ∷ annularNeighborhoodTargetRecordedRow
  ∷ noPDEPromotionGuardRow
  ∷ []

transverseSigmaNeighborhoodGeometryRowCount : Nat
transverseSigmaNeighborhoodGeometryRowCount =
  listLength canonicalTransverseSigmaNeighborhoodGeometryRows

transverseSigmaNeighborhoodGeometryRowCountIsEleven :
  transverseSigmaNeighborhoodGeometryRowCount ≡ 11
transverseSigmaNeighborhoodGeometryRowCountIsEleven =
  refl

data TransverseSigmaNeighborhoodGeometryBlocker : Set where
  missingSanniExternalAuthorityToken :
    TransverseSigmaNeighborhoodGeometryBlocker

  missingInternalProofOfTransverseChartFromSymbol :
    TransverseSigmaNeighborhoodGeometryBlocker

  missingQuantitativeDerivativeNormLowerBound :
    TransverseSigmaNeighborhoodGeometryBlocker

  missingNonRadialityQuantification :
    TransverseSigmaNeighborhoodGeometryBlocker

  missingAveragedCommutatorMassLowerBoundProof :
    TransverseSigmaNeighborhoodGeometryBlocker

  missingMicrolocalDefectMassConstruction :
    TransverseSigmaNeighborhoodGeometryBlocker

  missingPressureCommutatorGainProof :
    TransverseSigmaNeighborhoodGeometryBlocker

  missingMechanismExhaustionForFullClayNS :
    TransverseSigmaNeighborhoodGeometryBlocker

  clayNavierStokesPromotionClosed :
    TransverseSigmaNeighborhoodGeometryBlocker

canonicalTransverseSigmaNeighborhoodGeometryBlockers :
  List TransverseSigmaNeighborhoodGeometryBlocker
canonicalTransverseSigmaNeighborhoodGeometryBlockers =
  missingSanniExternalAuthorityToken
  ∷ missingInternalProofOfTransverseChartFromSymbol
  ∷ missingQuantitativeDerivativeNormLowerBound
  ∷ missingNonRadialityQuantification
  ∷ missingAveragedCommutatorMassLowerBoundProof
  ∷ missingMicrolocalDefectMassConstruction
  ∷ missingPressureCommutatorGainProof
  ∷ missingMechanismExhaustionForFullClayNS
  ∷ clayNavierStokesPromotionClosed
  ∷ []

transverseSigmaNeighborhoodGeometryBlockerCount : Nat
transverseSigmaNeighborhoodGeometryBlockerCount =
  listLength canonicalTransverseSigmaNeighborhoodGeometryBlockers

transverseSigmaNeighborhoodGeometryBlockerCountIsNine :
  transverseSigmaNeighborhoodGeometryBlockerCount ≡ 9
transverseSigmaNeighborhoodGeometryBlockerCountIsNine =
  refl

data TransverseSigmaNeighborhoodGeometryStatus : Set where
  sprint163SigmaDegeneracyRecordedStatus :
    TransverseSigmaNeighborhoodGeometryStatus

  sprint163NoPDEClaimRecordedStatus :
    TransverseSigmaNeighborhoodGeometryStatus

  sigmaNonRadialTargetRecordedStatus :
    TransverseSigmaNeighborhoodGeometryStatus

  rankOneFormulaImportedStatus :
    TransverseSigmaNeighborhoodGeometryStatus

  localChartRecordedStatus :
    TransverseSigmaNeighborhoodGeometryStatus

  twoTangentialDirectionsRecordedStatus :
    TransverseSigmaNeighborhoodGeometryStatus

  firstOrderSplitWitnessRecordedStatus :
    TransverseSigmaNeighborhoodGeometryStatus

  linearLowerBoundTargetRecordedStatus :
    TransverseSigmaNeighborhoodGeometryStatus

  analyticProofStillFalseStatus :
    TransverseSigmaNeighborhoodGeometryStatus

  clayPromotionStillFalseStatus :
    TransverseSigmaNeighborhoodGeometryStatus

canonicalTransverseSigmaNeighborhoodGeometryStatuses :
  List TransverseSigmaNeighborhoodGeometryStatus
canonicalTransverseSigmaNeighborhoodGeometryStatuses =
  sprint163SigmaDegeneracyRecordedStatus
  ∷ sprint163NoPDEClaimRecordedStatus
  ∷ sigmaNonRadialTargetRecordedStatus
  ∷ rankOneFormulaImportedStatus
  ∷ localChartRecordedStatus
  ∷ twoTangentialDirectionsRecordedStatus
  ∷ firstOrderSplitWitnessRecordedStatus
  ∷ linearLowerBoundTargetRecordedStatus
  ∷ analyticProofStillFalseStatus
  ∷ clayPromotionStillFalseStatus
  ∷ []

transverseSigmaNeighborhoodGeometryStatusCount : Nat
transverseSigmaNeighborhoodGeometryStatusCount =
  listLength canonicalTransverseSigmaNeighborhoodGeometryStatuses

transverseSigmaNeighborhoodGeometryStatusCountIsTen :
  transverseSigmaNeighborhoodGeometryStatusCount ≡ 10
transverseSigmaNeighborhoodGeometryStatusCountIsTen =
  refl

TransverseSigmaNeighborhoodGeometryTargetRecorded : Bool
TransverseSigmaNeighborhoodGeometryTargetRecorded =
  true

TwoTangentialDirectionsRecorded : Bool
TwoTangentialDirectionsRecorded =
  true

FirstOrderSplitWitnessRecorded : Bool
FirstOrderSplitWitnessRecorded =
  true

LinearEigenvalueSplitLowerBoundTargetRecorded : Bool
LinearEigenvalueSplitLowerBoundTargetRecorded =
  true

SanniExternalAuthorityAccepted : Bool
SanniExternalAuthorityAccepted =
  false

InternalTransverseChartProofAccepted : Bool
InternalTransverseChartProofAccepted =
  false

QuantitativeDerivativeNormLowerBoundProved : Bool
QuantitativeDerivativeNormLowerBoundProved =
  false

NonRadialityQuantificationProved : Bool
NonRadialityQuantificationProved =
  false

AveragedCommutatorMassLowerBoundProved : Bool
AveragedCommutatorMassLowerBoundProved =
  false

MicrolocalDefectMassConstructed : Bool
MicrolocalDefectMassConstructed =
  false

PressureCommutatorGainProved : Bool
PressureCommutatorGainProved =
  false

MechanismExhaustionForFullClayNS : Bool
MechanismExhaustionForFullClayNS =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

fullClayNSSolved : Bool
fullClayNSSolved =
  false

terminalPromotion : Bool
terminalPromotion =
  false

organizationString : String
organizationString =
  "O: TransverseSigmaNeighborhoodGeometry is a worker-lane NS proof-boundary module over the Sigma angular strain-symbol locus."

requirementString : String
requirementString =
  "R: Record the transverse local chart, two tangent directions, first-order split witness, and linear eigenvalue lower-bound target while consuming Sprint163, Sigma target, and rank-one formula anchors."

codeArtifactString : String
codeArtifactString =
  "C: The Agda artifact exports canonical rows, blockers, status rows, booleans, equality receipts, ORCSLPGF, and a canonical non-promoting record."

stateString : String
stateString =
  "S: Sprint163 records angular strain-symbol degeneracy and no PDE theorem; SigmaNonRadialCommutatorLowerBound remains false; the rank-one formula is checked but analytic lower bounds remain open."

latticeString : String
latticeString =
  "L: Sprint163 symbol vocabulary -> transverse Sigma chart -> tangential derivative pair -> first-order splitting -> linear lower-bound target -> non-radial commutator theorem target -> microlocal/PDE/Clay blockers."

proposalString : String
proposalString =
  "P: Treat this as the exact local-geometry boundary feeding NonRadialityQuantification, not as the averaged commutator theorem or Clay NS closure."

governanceString : String
governanceString =
  "G: Source anchors and local target rows are true; Sanni authority acceptance, internal PDE proof, microlocal defect mass, pressure gain, mechanism exhaustion, Clay NS, and terminal promotion remain false."

gapString : String
gapString =
  "F: Remaining deficits are external authority token, internal symbol-to-chart proof, derivative norm lower bound, non-radiality quantification, averaged commutator mass, microlocal defect mass, pressure gain, and full Clay mechanism exhaustion."

record TransverseSigmaNeighborhoodGeometryORCSLPGF : Set where
  constructor transverseSigmaNeighborhoodGeometryORCSLPGF
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

open TransverseSigmaNeighborhoodGeometryORCSLPGF public

canonicalTransverseSigmaNeighborhoodGeometryORCSLPGF :
  TransverseSigmaNeighborhoodGeometryORCSLPGF
canonicalTransverseSigmaNeighborhoodGeometryORCSLPGF =
  transverseSigmaNeighborhoodGeometryORCSLPGF
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

record NSTransverseSigmaNeighborhoodGeometryReceipt : Setω where
  constructor nsTransverseSigmaNeighborhoodGeometryReceipt
  field
    theoremName :
      String
    theoremNameIsCanonical :
      theoremName ≡ "TransverseSigmaNeighborhoodGeometry"

    sprint163Anchor :
      S163.NSSprint163TopologicalAlignmentObstructionBoundaryReceipt
    sprint163AnchorIsCanonical :
      sprint163Anchor
      ≡
      S163.canonicalNSSprint163TopologicalAlignmentObstructionBoundaryReceipt

    sigmaNonRadialAnchor :
      SigmaTarget.NSSigmaNonRadialCommutatorLowerBoundTargetReceipt
    sigmaNonRadialAnchorCanonical :
      Bool
    sigmaNonRadialAnchorCanonicalIsTrue :
      sigmaNonRadialAnchorCanonical ≡ true

    rankOneFormulaAnchor :
      RankOne.NSRankOneProjectionCommutatorFormula
    rankOneFormulaAnchorCanonical :
      Bool
    rankOneFormulaAnchorCanonicalIsTrue :
      rankOneFormulaAnchorCanonical ≡ true

    localChart :
      SigmaLocalChart
    localChartIsCanonical :
      localChart ≡ transverseAngularStrainSigmaChart
    chartCenter :
      SigmaChartCenter
    chartCenterIsTheta0 :
      chartCenter ≡ transverseDegeneracyPointTheta0
    tangentDirections :
      List SigmaTangentDirection
    tangentDirectionsAreCanonical :
      tangentDirections ≡ canonicalSigmaTangentialDirections
    tangentDirectionCount :
      Nat
    tangentDirectionCountIsTwo :
      tangentDirectionCount ≡ 2
    derivativeWitnesses :
      List TangentialDerivativeWitness
    derivativeWitnessesAreCanonical :
      derivativeWitnesses ≡ canonicalTangentialDerivativeWitnesses
    derivativeWitnessCount :
      Nat
    derivativeWitnessCountIsTwo :
      derivativeWitnessCount ≡ 2
    firstOrderSplit :
      FirstOrderSplitWitness
    firstOrderSplitIsCanonical :
      firstOrderSplit ≡ canonicalFirstOrderSplitWitness
    transversalityWitness :
      SigmaTransversalityWitness
    transversalityWitnessIsCanonical :
      transversalityWitness ≡ canonicalSigmaTransversalityWitness
    linearLowerBoundTarget :
      EigenvalueSplitLowerBoundTarget
    linearLowerBoundTargetIsCanonical :
      linearLowerBoundTarget ≡ canonicalEigenvalueSplitLowerBoundTarget
    annularNeighborhoodTarget :
      AnnularNeighborhoodTarget
    annularNeighborhoodTargetIsCanonical :
      annularNeighborhoodTarget ≡ canonicalAnnularNeighborhoodTarget

    rows :
      List TransverseSigmaNeighborhoodGeometryRow
    rowsAreCanonical :
      rows ≡ canonicalTransverseSigmaNeighborhoodGeometryRows
    rowCount :
      Nat
    rowCountIsEleven :
      rowCount ≡ 11
    blockers :
      List TransverseSigmaNeighborhoodGeometryBlocker
    blockersAreCanonical :
      blockers ≡ canonicalTransverseSigmaNeighborhoodGeometryBlockers
    blockerCount :
      Nat
    blockerCountIsNine :
      blockerCount ≡ 9
    statuses :
      List TransverseSigmaNeighborhoodGeometryStatus
    statusesAreCanonical :
      statuses ≡ canonicalTransverseSigmaNeighborhoodGeometryStatuses
    statusCount :
      Nat
    statusCountIsTen :
      statusCount ≡ 10

    orcslpgf :
      TransverseSigmaNeighborhoodGeometryORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalTransverseSigmaNeighborhoodGeometryORCSLPGF

    sprint163AngularStrainSymbolDegeneracyRecorded :
      S163.AngularStrainSymbolDegeneracyRecorded ≡ true
    sprint163MaximalEigenbundleNonOrientabilityRecorded :
      S163.MaximalEigenbundleNonOrientabilityRecorded ≡ true
    sprint163SanniSymbolOnlyNoPDE :
      S163.SanniSymbolLevelNoPDEClaimRecorded ≡ true
    sprint163KeepsMechanismExhaustionFalse :
      S163.MechanismExhaustionForFullClayNS ≡ false
    sprint163KeepsClayPromotionFalse :
      S163.clayNavierStokesPromoted ≡ false

    sigmaTargetRecordsTransverseNeighborhood :
      SigmaTarget.TransverseSigmaNeighborhoodTargetRecorded ≡ true
    sigmaTargetRecordsRankOneFormula :
      SigmaTarget.RankOneCommutatorFormulaProvedOrImported ≡ true
    sigmaTargetLowerBoundStillFalse :
      SigmaTarget.SigmaNonRadialCommutatorLowerBound ≡ false
    sigmaTargetMicrolocalMassStillFalse :
      SigmaTarget.MicrolocalDefectMassConstructed ≡ false
    sigmaTargetClayPromotionStillFalse :
      SigmaTarget.clayNavierStokesPromoted ≡ false

    rankOneCorrectedFormulaRecorded :
      RankOne.correctedFormulaRecorded
        RankOne.canonicalNSRankOneProjectionCommutatorFormula
      ≡
      true
    rankOnePressureControlStillFalse :
      RankOne.analyticPressureControlProved
        RankOne.canonicalNSRankOneProjectionCommutatorFormula
      ≡
      false
    rankOneClayPromotionStillFalse :
      RankOne.navierStokesClayPromoted
        RankOne.canonicalNSRankOneProjectionCommutatorFormula
      ≡
      false

    targetRecorded :
      TransverseSigmaNeighborhoodGeometryTargetRecorded ≡ true
    twoTangentialDirectionsRecorded :
      TwoTangentialDirectionsRecorded ≡ true
    firstOrderSplitWitnessRecorded :
      FirstOrderSplitWitnessRecorded ≡ true
    linearEigenvalueSplitLowerBoundTargetRecorded :
      LinearEigenvalueSplitLowerBoundTargetRecorded ≡ true
    sanniExternalAuthorityAcceptedFalse :
      SanniExternalAuthorityAccepted ≡ false
    internalTransverseChartProofAcceptedFalse :
      InternalTransverseChartProofAccepted ≡ false
    quantitativeDerivativeNormLowerBoundProvedFalse :
      QuantitativeDerivativeNormLowerBoundProved ≡ false
    nonRadialityQuantificationProvedFalse :
      NonRadialityQuantificationProved ≡ false
    averagedCommutatorMassLowerBoundProvedFalse :
      AveragedCommutatorMassLowerBoundProved ≡ false
    microlocalDefectMassConstructedFalse :
      MicrolocalDefectMassConstructed ≡ false
    pressureCommutatorGainProvedFalse :
      PressureCommutatorGainProved ≡ false
    mechanismExhaustionForFullClayNSFalse :
      MechanismExhaustionForFullClayNS ≡ false
    clayNavierStokesPromotedFalse :
      clayNavierStokesPromoted ≡ false
    fullClayNSSolvedFalse :
      fullClayNSSolved ≡ false
    terminalPromotionFalse :
      terminalPromotion ≡ false

open NSTransverseSigmaNeighborhoodGeometryReceipt public

canonicalNSTransverseSigmaNeighborhoodGeometryReceipt :
  NSTransverseSigmaNeighborhoodGeometryReceipt
canonicalNSTransverseSigmaNeighborhoodGeometryReceipt =
  record
    { theoremName =
        "TransverseSigmaNeighborhoodGeometry"
    ; theoremNameIsCanonical =
        refl
    ; sprint163Anchor =
        S163.canonicalNSSprint163TopologicalAlignmentObstructionBoundaryReceipt
    ; sprint163AnchorIsCanonical =
        refl
    ; sigmaNonRadialAnchor =
        SigmaTarget.canonicalNSSigmaNonRadialCommutatorLowerBoundTargetReceipt
    ; sigmaNonRadialAnchorCanonical =
        true
    ; sigmaNonRadialAnchorCanonicalIsTrue =
        refl
    ; rankOneFormulaAnchor =
        RankOne.canonicalNSRankOneProjectionCommutatorFormula
    ; rankOneFormulaAnchorCanonical =
        true
    ; rankOneFormulaAnchorCanonicalIsTrue =
        refl
    ; localChart =
        transverseAngularStrainSigmaChart
    ; localChartIsCanonical =
        refl
    ; chartCenter =
        transverseDegeneracyPointTheta0
    ; chartCenterIsTheta0 =
        refl
    ; tangentDirections =
        canonicalSigmaTangentialDirections
    ; tangentDirectionsAreCanonical =
        refl
    ; tangentDirectionCount =
        sigmaTangentialDirectionCount
    ; tangentDirectionCountIsTwo =
        refl
    ; derivativeWitnesses =
        canonicalTangentialDerivativeWitnesses
    ; derivativeWitnessesAreCanonical =
        refl
    ; derivativeWitnessCount =
        tangentialDerivativeWitnessCount
    ; derivativeWitnessCountIsTwo =
        refl
    ; firstOrderSplit =
        canonicalFirstOrderSplitWitness
    ; firstOrderSplitIsCanonical =
        refl
    ; transversalityWitness =
        canonicalSigmaTransversalityWitness
    ; transversalityWitnessIsCanonical =
        refl
    ; linearLowerBoundTarget =
        canonicalEigenvalueSplitLowerBoundTarget
    ; linearLowerBoundTargetIsCanonical =
        refl
    ; annularNeighborhoodTarget =
        canonicalAnnularNeighborhoodTarget
    ; annularNeighborhoodTargetIsCanonical =
        refl
    ; rows =
        canonicalTransverseSigmaNeighborhoodGeometryRows
    ; rowsAreCanonical =
        refl
    ; rowCount =
        transverseSigmaNeighborhoodGeometryRowCount
    ; rowCountIsEleven =
        refl
    ; blockers =
        canonicalTransverseSigmaNeighborhoodGeometryBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCount =
        transverseSigmaNeighborhoodGeometryBlockerCount
    ; blockerCountIsNine =
        refl
    ; statuses =
        canonicalTransverseSigmaNeighborhoodGeometryStatuses
    ; statusesAreCanonical =
        refl
    ; statusCount =
        transverseSigmaNeighborhoodGeometryStatusCount
    ; statusCountIsTen =
        refl
    ; orcslpgf =
        canonicalTransverseSigmaNeighborhoodGeometryORCSLPGF
    ; orcslpgfIsCanonical =
        refl
    ; sprint163AngularStrainSymbolDegeneracyRecorded =
        refl
    ; sprint163MaximalEigenbundleNonOrientabilityRecorded =
        refl
    ; sprint163SanniSymbolOnlyNoPDE =
        refl
    ; sprint163KeepsMechanismExhaustionFalse =
        refl
    ; sprint163KeepsClayPromotionFalse =
        refl
    ; sigmaTargetRecordsTransverseNeighborhood =
        refl
    ; sigmaTargetRecordsRankOneFormula =
        refl
    ; sigmaTargetLowerBoundStillFalse =
        refl
    ; sigmaTargetMicrolocalMassStillFalse =
        refl
    ; sigmaTargetClayPromotionStillFalse =
        refl
    ; rankOneCorrectedFormulaRecorded =
        refl
    ; rankOnePressureControlStillFalse =
        refl
    ; rankOneClayPromotionStillFalse =
        refl
    ; targetRecorded =
        refl
    ; twoTangentialDirectionsRecorded =
        refl
    ; firstOrderSplitWitnessRecorded =
        refl
    ; linearEigenvalueSplitLowerBoundTargetRecorded =
        refl
    ; sanniExternalAuthorityAcceptedFalse =
        refl
    ; internalTransverseChartProofAcceptedFalse =
        refl
    ; quantitativeDerivativeNormLowerBoundProvedFalse =
        refl
    ; nonRadialityQuantificationProvedFalse =
        refl
    ; averagedCommutatorMassLowerBoundProvedFalse =
        refl
    ; microlocalDefectMassConstructedFalse =
        refl
    ; pressureCommutatorGainProvedFalse =
        refl
    ; mechanismExhaustionForFullClayNSFalse =
        refl
    ; clayNavierStokesPromotedFalse =
        refl
    ; fullClayNSSolvedFalse =
        refl
    ; terminalPromotionFalse =
        refl
    }
