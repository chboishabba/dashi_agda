module DASHI.Physics.Closure.NSTrueLerayTriadicZeroModeClassificationBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSTrueLerayTriadicDefectSymbol as TrueSymbol

------------------------------------------------------------------------
-- True Leray triadic zero-mode classification boundary.
--
-- This module records the next finite symbolic Navier-Stokes obligation:
--
--   TrueLerayTriadicZeroModeClassification
--
-- The single-depth kernel of the true non-averaged Leray triadic defect
-- should be exhausted by two rank-one families on the output tangent plane:
--
--   Family I:
--     output vorticity direction parallel to P_c b
--
--   Family II:
--     output vorticity direction orthogonal to P_c a
--
-- where P_c is tangential projection to T_c S^2 and the restricted matrix is
-- the Leray/tangential rank-one operator P_c (b tensor a) P_c.  This is only
-- a fail-closed receipt.  It does not prove the classification, cascade
-- output width, PDE leakage transfer, local monotonicity, or Clay NS.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Typed anchor to the exact symbol module.

trueSymbolReceipt :
  TrueSymbol.TrueLerayTriadicDefectSymbolBoundary
trueSymbolReceipt =
  TrueSymbol.canonicalTrueLerayTriadicDefectSymbolBoundary

exactTriadicSymbolImported : Bool
exactTriadicSymbolImported =
  true

exactTriadicSymbolReference : String
exactTriadicSymbolReference =
  "DASHI.Physics.Closure.NSTrueLerayTriadicDefectSymbol"

stringOnlySymbolReferenceUsed : Bool
stringOnlySymbolReferenceUsed =
  false

------------------------------------------------------------------------
-- Rank-one restricted Leray matrix target.

data OutputTangentPlane : Set where
  tangentPlaneAtOutputC :
    TrueSymbol.Direction3 →
    OutputTangentPlane

data TangentialInputProjection : Set where
  projectInputAToOutputTangent :
    TrueSymbol.TangentialProjectionAtOutput →
    TangentialInputProjection
  projectInputBToOutputTangent :
    TrueSymbol.TangentialProjectionAtOutput →
    TangentialInputProjection

data RestrictedRankOneLerayMatrix : Set where
  pcBTensorAPcOnOutputTangent :
    OutputTangentPlane →
    TangentialInputProjection →
    TangentialInputProjection →
    TrueSymbol.LerayProjector →
    RestrictedRankOneLerayMatrix

canonicalOutputTangentPlane : OutputTangentPlane
canonicalOutputTangentPlane =
  tangentPlaneAtOutputC TrueSymbol.canonicalOutputC

canonicalProjectedInputA : TangentialInputProjection
canonicalProjectedInputA =
  projectInputAToOutputTangent
    TrueSymbol.canonicalTangentialProjectionOfA

canonicalProjectedInputB : TangentialInputProjection
canonicalProjectedInputB =
  projectInputBToOutputTangent
    TrueSymbol.canonicalTangentialProjectionOfB

canonicalRestrictedRankOneLerayMatrix : RestrictedRankOneLerayMatrix
canonicalRestrictedRankOneLerayMatrix =
  pcBTensorAPcOnOutputTangent
    canonicalOutputTangentPlane
    canonicalProjectedInputB
    canonicalProjectedInputA
    TrueSymbol.canonicalLerayProjector

------------------------------------------------------------------------
-- The two zero-mode families and their exhaustion target.

data TriadicZeroModeFamilyName : Set where
  familyI :
    TriadicZeroModeFamilyName
  familyII :
    TriadicZeroModeFamilyName

data FamilyIZeroModeCondition : Set where
  outputVorticityParallelToProjectedB :
    TrueSymbol.Direction3 →
    TangentialInputProjection →
    FamilyIZeroModeCondition

data FamilyIIZeroModeCondition : Set where
  outputVorticityOrthogonalToProjectedA :
    TrueSymbol.Direction3 →
    TangentialInputProjection →
    FamilyIIZeroModeCondition

canonicalFamilyICondition : FamilyIZeroModeCondition
canonicalFamilyICondition =
  outputVorticityParallelToProjectedB
    TrueSymbol.outputVorticityDirection
    canonicalProjectedInputB

canonicalFamilyIICondition : FamilyIIZeroModeCondition
canonicalFamilyIICondition =
  outputVorticityOrthogonalToProjectedA
    TrueSymbol.outputVorticityDirection
    canonicalProjectedInputA

data ZeroModeFamilyClassifier : Set where
  familyIClassifier :
    FamilyIZeroModeCondition →
    ZeroModeFamilyClassifier
  familyIIClassifier :
    FamilyIIZeroModeCondition →
    ZeroModeFamilyClassifier

canonicalZeroModeFamilyClassifiers :
  List ZeroModeFamilyClassifier
canonicalZeroModeFamilyClassifiers =
  familyIClassifier canonicalFamilyICondition
  ∷ familyIIClassifier canonicalFamilyIICondition
  ∷ []

zeroModeFamilyClassifierCount : Nat
zeroModeFamilyClassifierCount =
  listLength canonicalZeroModeFamilyClassifiers

zeroModeFamilyClassifierCountIs2 :
  zeroModeFamilyClassifierCount ≡ 2
zeroModeFamilyClassifierCountIs2 =
  refl

data RankOneExhaustionTarget : Set where
  rankOneTwoFamilyExhaustionOfKernelTarget :
    RestrictedRankOneLerayMatrix →
    TrueSymbol.TriadicZeroModeEquation →
    List ZeroModeFamilyClassifier →
    RankOneExhaustionTarget

canonicalRankOneExhaustionTarget : RankOneExhaustionTarget
canonicalRankOneExhaustionTarget =
  rankOneTwoFamilyExhaustionOfKernelTarget
    canonicalRestrictedRankOneLerayMatrix
    TrueSymbol.canonicalTriadicZeroModeEquationTarget
    canonicalZeroModeFamilyClassifiers

------------------------------------------------------------------------
-- Algebra proof obligations.

data ClassificationProofObligation : Set where
  restrictTrueLeraySymbolToOutputTangentPlane :
    ClassificationProofObligation
  identifyRestrictedSymbolAsRankOnePcBTensorAPc :
    ClassificationProofObligation
  computeRankOneImageEigenline :
    ClassificationProofObligation
  computeRankOneKernelEigenline :
    ClassificationProofObligation
  proveNoThirdEigenlineInTwoDimensionalTangentPlane :
    ClassificationProofObligation
  connectImageEigenlineToFamilyI :
    ClassificationProofObligation
  connectKernelEigenlineToFamilyII :
    ClassificationProofObligation
  propagateClassificationToCascadeWidthDependency :
    ClassificationProofObligation
  keepTaoAveragedOperatorGuard :
    ClassificationProofObligation
  keepClayNavierStokesPromotionClosed :
    ClassificationProofObligation

canonicalClassificationProofObligations :
  List ClassificationProofObligation
canonicalClassificationProofObligations =
  restrictTrueLeraySymbolToOutputTangentPlane
  ∷ identifyRestrictedSymbolAsRankOnePcBTensorAPc
  ∷ computeRankOneImageEigenline
  ∷ computeRankOneKernelEigenline
  ∷ proveNoThirdEigenlineInTwoDimensionalTangentPlane
  ∷ connectImageEigenlineToFamilyI
  ∷ connectKernelEigenlineToFamilyII
  ∷ propagateClassificationToCascadeWidthDependency
  ∷ keepTaoAveragedOperatorGuard
  ∷ keepClayNavierStokesPromotionClosed
  ∷ []

classificationProofObligationCount : Nat
classificationProofObligationCount =
  listLength canonicalClassificationProofObligations

classificationProofObligationCountIs10 :
  classificationProofObligationCount ≡ 10
classificationProofObligationCountIs10 =
  refl

data ClassificationObligationStatus : Set where
  targetRecorded :
    ClassificationObligationStatus
  importedFromExactSymbolModule :
    ClassificationObligationStatus
  proofOpen :
    ClassificationObligationStatus
  downstreamCascadeDependency :
    ClassificationObligationStatus
  promotionBlocked :
    ClassificationObligationStatus

statusForClassificationObligation :
  ClassificationProofObligation →
  ClassificationObligationStatus
statusForClassificationObligation restrictTrueLeraySymbolToOutputTangentPlane =
  importedFromExactSymbolModule
statusForClassificationObligation identifyRestrictedSymbolAsRankOnePcBTensorAPc =
  proofOpen
statusForClassificationObligation computeRankOneImageEigenline =
  proofOpen
statusForClassificationObligation computeRankOneKernelEigenline =
  proofOpen
statusForClassificationObligation proveNoThirdEigenlineInTwoDimensionalTangentPlane =
  proofOpen
statusForClassificationObligation connectImageEigenlineToFamilyI =
  targetRecorded
statusForClassificationObligation connectKernelEigenlineToFamilyII =
  targetRecorded
statusForClassificationObligation propagateClassificationToCascadeWidthDependency =
  downstreamCascadeDependency
statusForClassificationObligation keepTaoAveragedOperatorGuard =
  targetRecorded
statusForClassificationObligation keepClayNavierStokesPromotionClosed =
  promotionBlocked

data ClassificationBlocker : Set where
  noBlockerForSymbolImport :
    ClassificationBlocker
  missingExactRankOneRestrictionProof :
    ClassificationBlocker
  missingRankOneImageEigenlineProof :
    ClassificationBlocker
  missingRankOneKernelEigenlineProof :
    ClassificationBlocker
  missingNoThirdEigenlineProof :
    ClassificationBlocker
  noBlockerForFamilyIName :
    ClassificationBlocker
  noBlockerForFamilyIIName :
    ClassificationBlocker
  missingCascadeClosedIterationLemma :
    ClassificationBlocker
  taoAveragedOperatorMustNotInheritClassification :
    ClassificationBlocker
  clayNavierStokesPromotionClosed :
    ClassificationBlocker

blockerForClassificationObligation :
  ClassificationProofObligation →
  ClassificationBlocker
blockerForClassificationObligation restrictTrueLeraySymbolToOutputTangentPlane =
  noBlockerForSymbolImport
blockerForClassificationObligation identifyRestrictedSymbolAsRankOnePcBTensorAPc =
  missingExactRankOneRestrictionProof
blockerForClassificationObligation computeRankOneImageEigenline =
  missingRankOneImageEigenlineProof
blockerForClassificationObligation computeRankOneKernelEigenline =
  missingRankOneKernelEigenlineProof
blockerForClassificationObligation proveNoThirdEigenlineInTwoDimensionalTangentPlane =
  missingNoThirdEigenlineProof
blockerForClassificationObligation connectImageEigenlineToFamilyI =
  noBlockerForFamilyIName
blockerForClassificationObligation connectKernelEigenlineToFamilyII =
  noBlockerForFamilyIIName
blockerForClassificationObligation propagateClassificationToCascadeWidthDependency =
  missingCascadeClosedIterationLemma
blockerForClassificationObligation keepTaoAveragedOperatorGuard =
  taoAveragedOperatorMustNotInheritClassification
blockerForClassificationObligation keepClayNavierStokesPromotionClosed =
  clayNavierStokesPromotionClosed

record ClassificationObligationRow : Set where
  constructor classificationObligationRow
  field
    obligation :
      ClassificationProofObligation
    status :
      ClassificationObligationStatus
    statusIsCanonical :
      status ≡ statusForClassificationObligation obligation
    blocker :
      ClassificationBlocker
    blockerIsCanonical :
      blocker ≡ blockerForClassificationObligation obligation
    recordedTarget :
      String
    requiredProof :
      String
    familyClassificationProvedInRow :
      Bool
    familyClassificationProvedInRowIsFalse :
      familyClassificationProvedInRow ≡ false
    outputWidthProvedInRow :
      Bool
    outputWidthProvedInRowIsFalse :
      outputWidthProvedInRow ≡ false
    clayPromotionInRow :
      Bool
    clayPromotionInRowIsFalse :
      clayPromotionInRow ≡ false

open ClassificationObligationRow public

mkClassificationObligationRow :
  ClassificationProofObligation →
  String →
  String →
  ClassificationObligationRow
mkClassificationObligationRow obligation recordedTarget requiredProof =
  classificationObligationRow
    obligation
    (statusForClassificationObligation obligation)
    refl
    (blockerForClassificationObligation obligation)
    refl
    recordedTarget
    requiredProof
    false
    refl
    false
    refl
    false
    refl

canonicalClassificationObligationRows :
  List ClassificationObligationRow
canonicalClassificationObligationRows =
  mkClassificationObligationRow
    restrictTrueLeraySymbolToOutputTangentPlane
    "use the exact non-averaged P(xi+eta) symbol from NSTrueLerayTriadicDefectSymbol"
    "write the component restriction to the output divergence-free tangent plane"
  ∷ mkClassificationObligationRow
    identifyRestrictedSymbolAsRankOnePcBTensorAPc
    "restricted operator target is P_c (b tensor a) P_c on T_c S^2"
    "derive the rank-one matrix from the Leray-projected bilinear symbol"
  ∷ mkClassificationObligationRow
    computeRankOneImageEigenline
    "rank-one image line is generated by the tangential projection P_c b"
    "prove the nonzero image eigenline statement, including degenerate cases"
  ∷ mkClassificationObligationRow
    computeRankOneKernelEigenline
    "rank-one kernel line is orthogonal to the tangential projection P_c a"
    "prove the kernel eigenline statement on the two-dimensional output tangent plane"
  ∷ mkClassificationObligationRow
    proveNoThirdEigenlineInTwoDimensionalTangentPlane
    "Family I and Family II are the only possible zero-mode channels at one depth"
    "exclude extra zero-mode families for the restricted rank-one matrix"
  ∷ mkClassificationObligationRow
    connectImageEigenlineToFamilyI
    "Family I is output vorticity parallel to P_c b"
    "connect the image eigenline computation to the named family"
  ∷ mkClassificationObligationRow
    connectKernelEigenlineToFamilyII
    "Family II is output vorticity orthogonal to P_c a"
    "connect the kernel eigenline computation to the named family"
  ∷ mkClassificationObligationRow
    propagateClassificationToCascadeWidthDependency
    "cascade width proof depends on feeding output c as a next-generation input"
    "prove CascadeClosedIterationLemma after the one-depth classification"
  ∷ mkClassificationObligationRow
    keepTaoAveragedOperatorGuard
    "the theorem must use true P(xi+eta), not an averaged operator family"
    "verify averaged NS does not inherit this classification-to-width route"
  ∷ mkClassificationObligationRow
    keepClayNavierStokesPromotionClosed
    "classification alone does not prove output width or PDE transfer"
    "keep all Clay NS promotion gates false"
  ∷ []

classificationObligationRowCount : Nat
classificationObligationRowCount =
  listLength canonicalClassificationObligationRows

classificationObligationRowCountIs10 :
  classificationObligationRowCount ≡ 10
classificationObligationRowCountIs10 =
  refl

------------------------------------------------------------------------
-- Cascade dependency ledger.

data CascadeDependency : Set where
  oneDepthClassificationFeedsZNsTriad :
    CascadeDependency
  zNsTriadFeedsCascadeClosedIteration :
    CascadeDependency
  cascadeClosedIterationFeedsDepthTwoDegreeComputation :
    CascadeDependency
  depthTwoDegreeComputationFeedsPositiveOutputWidth :
    CascadeDependency
  positiveOutputWidthFeedsTriadicSheafLeakage :
    CascadeDependency

canonicalCascadeDependencies : List CascadeDependency
canonicalCascadeDependencies =
  oneDepthClassificationFeedsZNsTriad
  ∷ zNsTriadFeedsCascadeClosedIteration
  ∷ cascadeClosedIterationFeedsDepthTwoDegreeComputation
  ∷ depthTwoDegreeComputationFeedsPositiveOutputWidth
  ∷ positiveOutputWidthFeedsTriadicSheafLeakage
  ∷ []

cascadeDependencyCount : Nat
cascadeDependencyCount =
  listLength canonicalCascadeDependencies

cascadeDependencyCountIs5 :
  cascadeDependencyCount ≡ 5
cascadeDependencyCountIs5 =
  refl

data ClassificationFalseGate : Set where
  familyClassificationTheoremFalseGate :
    ClassificationFalseGate
  cascadeClosedIterationLemmaFalseGate :
    ClassificationFalseGate
  cascadeDepthTwoDegreeComputationFalseGate :
    ClassificationFalseGate
  outputWidthTheoremFalseGate :
    ClassificationFalseGate
  triadicLeakageTransferFalseGate :
    ClassificationFalseGate
  clayNavierStokesPromotionFalseGate :
    ClassificationFalseGate

canonicalClassificationFalseGates : List ClassificationFalseGate
canonicalClassificationFalseGates =
  familyClassificationTheoremFalseGate
  ∷ cascadeClosedIterationLemmaFalseGate
  ∷ cascadeDepthTwoDegreeComputationFalseGate
  ∷ outputWidthTheoremFalseGate
  ∷ triadicLeakageTransferFalseGate
  ∷ clayNavierStokesPromotionFalseGate
  ∷ []

classificationFalseGateCount : Nat
classificationFalseGateCount =
  listLength canonicalClassificationFalseGates

classificationFalseGateCountIs6 :
  classificationFalseGateCount ≡ 6
classificationFalseGateCountIs6 =
  refl

record NSTrueLerayTriadicZeroModeClassificationBoundary : Set where
  constructor nsTrueLerayTriadicZeroModeClassificationBoundary
  field
    sourceSymbolReceipt :
      TrueSymbol.TrueLerayTriadicDefectSymbolBoundary
    sourceSymbolReceiptIsCanonical :
      sourceSymbolReceipt ≡ TrueSymbol.canonicalTrueLerayTriadicDefectSymbolBoundary
    sourceExactSymbolRecorded :
      TrueSymbol.exactSymbolRecorded sourceSymbolReceipt ≡ true
    sourceTaoGuardRecorded :
      TrueSymbol.taoGuardRecorded sourceSymbolReceipt ≡ true
    exactSymbolImported :
      Bool
    exactSymbolImportedIsTrue :
      exactSymbolImported ≡ true
    stringReferenceUsed :
      Bool
    stringReferenceUsedIsFalse :
      stringReferenceUsed ≡ false
    restrictedRankOneMatrix :
      RestrictedRankOneLerayMatrix
    restrictedRankOneMatrixIsCanonical :
      restrictedRankOneMatrix ≡ canonicalRestrictedRankOneLerayMatrix
    familyICondition :
      FamilyIZeroModeCondition
    familyIConditionIsCanonical :
      familyICondition ≡ canonicalFamilyICondition
    familyIICondition :
      FamilyIIZeroModeCondition
    familyIIConditionIsCanonical :
      familyIICondition ≡ canonicalFamilyIICondition
    familyClassifiers :
      List ZeroModeFamilyClassifier
    familyClassifiersAreCanonical :
      familyClassifiers ≡ canonicalZeroModeFamilyClassifiers
    familyClassifierCount :
      Nat
    familyClassifierCountIs2 :
      familyClassifierCount ≡ 2
    rankOneExhaustionTarget :
      RankOneExhaustionTarget
    rankOneExhaustionTargetIsCanonical :
      rankOneExhaustionTarget ≡ canonicalRankOneExhaustionTarget
    proofObligations :
      List ClassificationProofObligation
    proofObligationsAreCanonical :
      proofObligations ≡ canonicalClassificationProofObligations
    proofObligationCount :
      Nat
    proofObligationCountIs10 :
      proofObligationCount ≡ 10
    obligationRows :
      List ClassificationObligationRow
    obligationRowsAreCanonical :
      obligationRows ≡ canonicalClassificationObligationRows
    obligationRowCount :
      Nat
    obligationRowCountIs10 :
      obligationRowCount ≡ 10
    cascadeDependencies :
      List CascadeDependency
    cascadeDependenciesAreCanonical :
      cascadeDependencies ≡ canonicalCascadeDependencies
    cascadeDependencyCountField :
      Nat
    cascadeDependencyCountIs5Field :
      cascadeDependencyCountField ≡ 5
    falseGates :
      List ClassificationFalseGate
    falseGatesAreCanonical :
      falseGates ≡ canonicalClassificationFalseGates
    falseGateCount :
      Nat
    falseGateCountIs6 :
      falseGateCount ≡ 6
    familyClassificationTargetRecorded :
      Bool
    familyClassificationTargetRecordedIsTrue :
      familyClassificationTargetRecorded ≡ true
    rankOneExhaustionProved :
      Bool
    rankOneExhaustionProvedIsFalse :
      rankOneExhaustionProved ≡ false
    familyClassificationProved :
      Bool
    familyClassificationProvedIsFalse :
      familyClassificationProved ≡ false
    cascadeClosedIterationProved :
      Bool
    cascadeClosedIterationProvedIsFalse :
      cascadeClosedIterationProved ≡ false
    outputWidthProved :
      Bool
    outputWidthProvedIsFalse :
      outputWidthProved ≡ false
    leakageTransferProved :
      Bool
    leakageTransferProvedIsFalse :
      leakageTransferProved ≡ false
    clayNavierStokesPromoted :
      Bool
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

open NSTrueLerayTriadicZeroModeClassificationBoundary public

canonicalNSTrueLerayTriadicZeroModeClassificationBoundary :
  NSTrueLerayTriadicZeroModeClassificationBoundary
canonicalNSTrueLerayTriadicZeroModeClassificationBoundary =
  nsTrueLerayTriadicZeroModeClassificationBoundary
    trueSymbolReceipt
    refl
    TrueSymbol.exactSymbolRecordedFlagIsTrue
    TrueSymbol.taoGuardRecordedFlagIsTrue
    exactTriadicSymbolImported
    refl
    stringOnlySymbolReferenceUsed
    refl
    canonicalRestrictedRankOneLerayMatrix
    refl
    canonicalFamilyICondition
    refl
    canonicalFamilyIICondition
    refl
    canonicalZeroModeFamilyClassifiers
    refl
    zeroModeFamilyClassifierCount
    refl
    canonicalRankOneExhaustionTarget
    refl
    canonicalClassificationProofObligations
    refl
    classificationProofObligationCount
    refl
    canonicalClassificationObligationRows
    refl
    classificationObligationRowCount
    refl
    canonicalCascadeDependencies
    refl
    cascadeDependencyCount
    refl
    canonicalClassificationFalseGates
    refl
    classificationFalseGateCount
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl

familyClassificationTargetRecordedFlag : Bool
familyClassificationTargetRecordedFlag =
  familyClassificationTargetRecorded
    canonicalNSTrueLerayTriadicZeroModeClassificationBoundary

rankOneExhaustionProvedFlag : Bool
rankOneExhaustionProvedFlag =
  rankOneExhaustionProved
    canonicalNSTrueLerayTriadicZeroModeClassificationBoundary

familyClassificationProvedFlag : Bool
familyClassificationProvedFlag =
  familyClassificationProved
    canonicalNSTrueLerayTriadicZeroModeClassificationBoundary

cascadeClosedIterationProvedFlag : Bool
cascadeClosedIterationProvedFlag =
  cascadeClosedIterationProved
    canonicalNSTrueLerayTriadicZeroModeClassificationBoundary

outputWidthProvedFlag : Bool
outputWidthProvedFlag =
  outputWidthProved
    canonicalNSTrueLerayTriadicZeroModeClassificationBoundary

leakageTransferProvedFlag : Bool
leakageTransferProvedFlag =
  leakageTransferProved
    canonicalNSTrueLerayTriadicZeroModeClassificationBoundary

clayNavierStokesPromotedFlag : Bool
clayNavierStokesPromotedFlag =
  clayNavierStokesPromoted
    canonicalNSTrueLerayTriadicZeroModeClassificationBoundary

familyClassificationTargetRecordedFlagIsTrue :
  familyClassificationTargetRecordedFlag ≡ true
familyClassificationTargetRecordedFlagIsTrue =
  refl

rankOneExhaustionProvedFlagIsFalse :
  rankOneExhaustionProvedFlag ≡ false
rankOneExhaustionProvedFlagIsFalse =
  refl

familyClassificationProvedFlagIsFalse :
  familyClassificationProvedFlag ≡ false
familyClassificationProvedFlagIsFalse =
  refl

cascadeClosedIterationProvedFlagIsFalse :
  cascadeClosedIterationProvedFlag ≡ false
cascadeClosedIterationProvedFlagIsFalse =
  refl

outputWidthProvedFlagIsFalse :
  outputWidthProvedFlag ≡ false
outputWidthProvedFlagIsFalse =
  refl

leakageTransferProvedFlagIsFalse :
  leakageTransferProvedFlag ≡ false
leakageTransferProvedFlagIsFalse =
  refl

clayNavierStokesPromotedFlagIsFalse :
  clayNavierStokesPromotedFlag ≡ false
clayNavierStokesPromotedFlagIsFalse =
  refl

clayNavierStokesPromotionContradictionBoundary :
  clayNavierStokesPromotedFlag ≡ true →
  ⊥
clayNavierStokesPromotionContradictionBoundary ()

controlCard : List String
controlCard =
  "O: NS finite symbolic lane; owner is lane 2; decision surface is this fail-closed boundary module."
  ∷ "R: Record TrueLerayTriadicZeroModeClassification with Family I, Family II, rank-one restricted Leray exhaustion, and cascade dependency."
  ∷ "C: Imports NSTrueLerayTriadicDefectSymbol, anchors P_c(b tensor a)P_c, records two family classifiers, obligations, dependencies, and false gates."
  ∷ "S: Exact symbol is imported; family classification, rank-one exhaustion, cascade iteration, output width, leakage transfer, and Clay NS are unproved."
  ∷ "L: target-recorded < rank-one-exhaustion-proved < classification-proved < cascade-width-proved < PDE-transfer-proved < Clay-promoted."
  ∷ "P: Promote only the boundary receipt; do not promote finite theorem, output width, leakage transfer, or Clay NS."
  ∷ "G: Tao averaged-operator guard remains active; classification must use true non-averaged P(xi+eta)."
  ∷ "F: Remaining gap is exact algebraic proof that the restricted rank-one matrix has only the Family I image line and Family II kernel line, then cascade closure."
  ∷ []

summary : String
summary =
  "True Leray triadic zero-mode classification boundary recorded; Family I/II named; rank-one exhaustion and all downstream theorem flags remain false."
