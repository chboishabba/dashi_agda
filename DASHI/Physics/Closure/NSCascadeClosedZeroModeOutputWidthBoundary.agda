module DASHI.Physics.Closure.NSCascadeClosedZeroModeOutputWidthBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSTrueLerayTriadicDefectSymbol as TrueSymbol

------------------------------------------------------------------------
-- NS cascade-closed triadic zero-mode output-width boundary.
--
-- This module records the corrected finite-dimensional Navier-Stokes
-- target:
--
--   CascadeClosedZeroModeOutputWidth
--
-- The old single-angle zero-mode set is too small.  The exact obstruction
-- must live over the true Leray bilinear interaction phase space:
--
--   input direction a, input direction b, output direction c,
--   divergence-free polarization data, and the true P(xi + eta) symbol.
--
-- The desired theorem is not recorded as proved here.  This file records:
--
--   * Z_NS^triad as the kernel target of the true triadic defect symbol;
--   * Z_NS^infty as the iterated cascade-closed zero-mode target;
--   * pi_out from cascade-closed triads to output directions;
--   * positive great-circle avoidance width as the theorem target;
--   * double-Hairy-Ball / Whitney-transversality proof obligations;
--   * Tao averaged-operator falsifiability guard.
--
-- There is intentionally no Clay promotion in this boundary.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Symbol-source reference.
--
-- The true non-averaged Leray triadic symbol is now a typed local anchor.
-- The string name is retained only as a reader-facing module reference.

trueLerayTriadicDefectSymbolReference : String
trueLerayTriadicDefectSymbolReference =
  "DASHI.Physics.Closure.NSTrueLerayTriadicDefectSymbol"

trueLerayTriadicDefectSymbolImported : Bool
trueLerayTriadicDefectSymbolImported =
  true

trueLerayTriadicDefectSymbolStringReferenceUsed : Bool
trueLerayTriadicDefectSymbolStringReferenceUsed =
  false

trueLerayTriadicDefectSymbolReceipt :
  TrueSymbol.TrueLerayTriadicDefectSymbolBoundary
trueLerayTriadicDefectSymbolReceipt =
  TrueSymbol.canonicalTrueLerayTriadicDefectSymbolBoundary

------------------------------------------------------------------------
-- Interaction phase space and zero-mode carriers.

data TriadicDirectionCarrier : Set where
  inputFrequencyDirectionA :
    TriadicDirectionCarrier
  inputFrequencyDirectionB :
    TriadicDirectionCarrier
  outputFrequencyDirectionC :
    TriadicDirectionCarrier

data DivergenceFreePolarizationCarrier : Set where
  divergenceFreeTriadicPolarization :
    DivergenceFreePolarizationCarrier

data ResonantTriadicInteraction : Set where
  resonantTriadWithOutputDirection :
    TriadicDirectionCarrier →
    TriadicDirectionCarrier →
    TriadicDirectionCarrier →
    DivergenceFreePolarizationCarrier →
    ResonantTriadicInteraction

data TrueLerayBilinearSymbolTarget : Set where
  exactOutputProjectedLerayBilinearSymbol :
    String →
    TrueLerayBilinearSymbolTarget

data TriadicDefectLaplacianTarget : Set where
  stretchLeakageDefectLaplacianOnTriads :
    TrueLerayBilinearSymbolTarget →
    ResonantTriadicInteraction →
    TriadicDefectLaplacianTarget

data TriadicZeroModeSetTarget : Set where
  zNSTriadKernelOfDefectLaplacian :
    TriadicDefectLaplacianTarget →
    TriadicZeroModeSetTarget

canonicalPolarization : DivergenceFreePolarizationCarrier
canonicalPolarization =
  divergenceFreeTriadicPolarization

canonicalResonantTriad : ResonantTriadicInteraction
canonicalResonantTriad =
  resonantTriadWithOutputDirection
    inputFrequencyDirectionA
    inputFrequencyDirectionB
    outputFrequencyDirectionC
    canonicalPolarization

canonicalTrueLerayBilinearSymbolTarget : TrueLerayBilinearSymbolTarget
canonicalTrueLerayBilinearSymbolTarget =
  exactOutputProjectedLerayBilinearSymbol
    trueLerayTriadicDefectSymbolReference

canonicalTriadicDefectLaplacianTarget : TriadicDefectLaplacianTarget
canonicalTriadicDefectLaplacianTarget =
  stretchLeakageDefectLaplacianOnTriads
    canonicalTrueLerayBilinearSymbolTarget
    canonicalResonantTriad

canonicalTriadicZeroModeSetTarget : TriadicZeroModeSetTarget
canonicalTriadicZeroModeSetTarget =
  zNSTriadKernelOfDefectLaplacian
    canonicalTriadicDefectLaplacianTarget

------------------------------------------------------------------------
-- Cascade closure Z_NS^infty.

data CascadeDepth : Set where
  depthZeroTriadicZeroMode :
    CascadeDepth
  depthOneTriadFeedsNextInteraction :
    CascadeDepth
  depthTwoMutualFrameConstraint :
    CascadeDepth
  arbitraryFiniteCascadeDepth :
    CascadeDepth
  omegaCascadeClosedLimit :
    CascadeDepth

data CascadeClosureStage : Set where
  baseTriadicZeroModeStage :
    CascadeClosureStage
  firstGenerationOutputReusedAsInputStage :
    CascadeClosureStage
  secondGenerationCompatibilityStage :
    CascadeClosureStage
  finiteDepthIteratedZeroLeakageStage :
    CascadeClosureStage
  infiniteCascadeClosedIntersectionStage :
    CascadeClosureStage

data CascadeClosedZeroModeSetTarget : Set where
  zNSInfinityIteratedZeroLeakageIntersection :
    TriadicZeroModeSetTarget →
    List CascadeClosureStage →
    CascadeClosedZeroModeSetTarget

canonicalCascadeClosureStages : List CascadeClosureStage
canonicalCascadeClosureStages =
  baseTriadicZeroModeStage
  ∷ firstGenerationOutputReusedAsInputStage
  ∷ secondGenerationCompatibilityStage
  ∷ finiteDepthIteratedZeroLeakageStage
  ∷ infiniteCascadeClosedIntersectionStage
  ∷ []

cascadeClosureStageCount : Nat
cascadeClosureStageCount =
  listLength canonicalCascadeClosureStages

cascadeClosureStageCountIs5 :
  cascadeClosureStageCount ≡ 5
cascadeClosureStageCountIs5 =
  refl

canonicalCascadeClosedZeroModeSetTarget :
  CascadeClosedZeroModeSetTarget
canonicalCascadeClosedZeroModeSetTarget =
  zNSInfinityIteratedZeroLeakageIntersection
    canonicalTriadicZeroModeSetTarget
    canonicalCascadeClosureStages

------------------------------------------------------------------------
-- Output projection and positive great-circle avoidance width.

data OutputProjectionPiOutTarget : Set where
  piOutFromCascadeClosedTriadsToOutputSphere :
    CascadeClosedZeroModeSetTarget →
    TriadicDirectionCarrier →
    OutputProjectionPiOutTarget

data GreatCircleAvoidanceWidthTarget : Set where
  positiveGreatCircleAvoidanceWidthForPiOutZInfinity :
    OutputProjectionPiOutTarget →
    GreatCircleAvoidanceWidthTarget

canonicalOutputProjectionPiOutTarget : OutputProjectionPiOutTarget
canonicalOutputProjectionPiOutTarget =
  piOutFromCascadeClosedTriadsToOutputSphere
    canonicalCascadeClosedZeroModeSetTarget
    outputFrequencyDirectionC

canonicalGreatCircleAvoidanceWidthTarget :
  GreatCircleAvoidanceWidthTarget
canonicalGreatCircleAvoidanceWidthTarget =
  positiveGreatCircleAvoidanceWidthForPiOutZInfinity
    canonicalOutputProjectionPiOutTarget

------------------------------------------------------------------------
-- Proof-obligation rows.

data CascadeClosedWidthObligationStep : Set where
  trueLerayTriadicSymbolObligation :
    CascadeClosedWidthObligationStep
  triadicZeroModeFamilyClassificationObligation :
    CascadeClosedWidthObligationStep
  cascadeClosureDefinitionObligation :
    CascadeClosedWidthObligationStep
  outputProjectionDefinitionObligation :
    CascadeClosedWidthObligationStep
  doubleHairyBallFrameMismatchObligation :
    CascadeClosedWidthObligationStep
  whitneyTransversalityCodimensionObligation :
    CascadeClosedWidthObligationStep
  positiveGreatCircleAvoidanceWidthObligation :
    CascadeClosedWidthObligationStep
  taoAveragedOperatorFalsifiabilityGuardObligation :
    CascadeClosedWidthObligationStep
  clayNavierStokesPromotionGuardObligation :
    CascadeClosedWidthObligationStep

data CascadeClosedWidthStatus : Set where
  targetRecorded :
    CascadeClosedWidthStatus
  typedAnchorImported :
    CascadeClosedWidthStatus
  stringReferenceOnly :
    CascadeClosedWidthStatus
  proofObligationOpen :
    CascadeClosedWidthStatus
  falsifiabilityGuardRecorded :
    CascadeClosedWidthStatus
  promotionBlocked :
    CascadeClosedWidthStatus

data CascadeClosedWidthBlocker : Set where
  noBlockerForTypedTrueLerayTriadicSymbolAnchor :
    CascadeClosedWidthBlocker
  missingNSTrueLerayTriadicDefectSymbolModule :
    CascadeClosedWidthBlocker
  missingExactTriadicZeroModeFamilyProof :
    CascadeClosedWidthBlocker
  missingIteratedCascadeClosureTheorem :
    CascadeClosedWidthBlocker
  noBlockerForOutputProjectionRecord :
    CascadeClosedWidthBlocker
  missingDoubleHairyBallFrameMismatchProof :
    CascadeClosedWidthBlocker
  missingWhitneyTransversalityCodimensionProof :
    CascadeClosedWidthBlocker
  missingPositiveGreatCircleAvoidanceWidthProof :
    CascadeClosedWidthBlocker
  taoAveragedOperatorMustNotInheritWidthTheorem :
    CascadeClosedWidthBlocker
  clayNavierStokesPromotionClosed :
    CascadeClosedWidthBlocker

statusForObligation :
  CascadeClosedWidthObligationStep →
  CascadeClosedWidthStatus
statusForObligation trueLerayTriadicSymbolObligation =
  typedAnchorImported
statusForObligation triadicZeroModeFamilyClassificationObligation =
  proofObligationOpen
statusForObligation cascadeClosureDefinitionObligation =
  targetRecorded
statusForObligation outputProjectionDefinitionObligation =
  targetRecorded
statusForObligation doubleHairyBallFrameMismatchObligation =
  proofObligationOpen
statusForObligation whitneyTransversalityCodimensionObligation =
  proofObligationOpen
statusForObligation positiveGreatCircleAvoidanceWidthObligation =
  proofObligationOpen
statusForObligation taoAveragedOperatorFalsifiabilityGuardObligation =
  falsifiabilityGuardRecorded
statusForObligation clayNavierStokesPromotionGuardObligation =
  promotionBlocked

blockerForObligation :
  CascadeClosedWidthObligationStep →
  CascadeClosedWidthBlocker
blockerForObligation trueLerayTriadicSymbolObligation =
  noBlockerForTypedTrueLerayTriadicSymbolAnchor
blockerForObligation triadicZeroModeFamilyClassificationObligation =
  missingExactTriadicZeroModeFamilyProof
blockerForObligation cascadeClosureDefinitionObligation =
  missingIteratedCascadeClosureTheorem
blockerForObligation outputProjectionDefinitionObligation =
  noBlockerForOutputProjectionRecord
blockerForObligation doubleHairyBallFrameMismatchObligation =
  missingDoubleHairyBallFrameMismatchProof
blockerForObligation whitneyTransversalityCodimensionObligation =
  missingWhitneyTransversalityCodimensionProof
blockerForObligation positiveGreatCircleAvoidanceWidthObligation =
  missingPositiveGreatCircleAvoidanceWidthProof
blockerForObligation taoAveragedOperatorFalsifiabilityGuardObligation =
  taoAveragedOperatorMustNotInheritWidthTheorem
blockerForObligation clayNavierStokesPromotionGuardObligation =
  clayNavierStokesPromotionClosed

record CascadeClosedWidthObligationRow : Set where
  constructor cascadeClosedWidthObligationRow
  field
    obligation :
      CascadeClosedWidthObligationStep
    status :
      CascadeClosedWidthStatus
    statusIsCanonical :
      status ≡ statusForObligation obligation
    blocker :
      CascadeClosedWidthBlocker
    blockerIsCanonical :
      blocker ≡ blockerForObligation obligation
    recordedInput :
      String
    requiredProof :
      String
    cascadeClosureRecordedInRow :
      Bool
    cascadeClosureRecordedInRowIsTrue :
      cascadeClosureRecordedInRow ≡ true
    outputWidthProvedInRow :
      Bool
    outputWidthProvedInRowIsFalse :
      outputWidthProvedInRow ≡ false
    clayPromotionInRow :
      Bool
    clayPromotionInRowIsFalse :
      clayPromotionInRow ≡ false

open CascadeClosedWidthObligationRow public

mkCascadeClosedWidthObligationRow :
  CascadeClosedWidthObligationStep →
  String →
  String →
  CascadeClosedWidthObligationRow
mkCascadeClosedWidthObligationRow obligation recordedInput requiredProof =
  cascadeClosedWidthObligationRow
    obligation
    (statusForObligation obligation)
    refl
    (blockerForObligation obligation)
    refl
    recordedInput
    requiredProof
    true
    refl
    false
    refl
    false
    refl

canonicalCascadeClosedWidthObligationRows :
  List CascadeClosedWidthObligationRow
canonicalCascadeClosedWidthObligationRows =
  mkCascadeClosedWidthObligationRow
    trueLerayTriadicSymbolObligation
    "exact Leray bilinear symbol P(xi+eta) is imported from NSTrueLerayTriadicDefectSymbol"
    "consume the typed true-symbol boundary while keeping width and cascade-closure proofs separate"
  ∷ mkCascadeClosedWidthObligationRow
    triadicZeroModeFamilyClassificationObligation
    "Z_NS^triad is the kernel of the triadic stretch-leakage defect Laplacian over resonant interactions and polarizations"
    "prove the exact algebraic zero-mode family classification for the true non-averaged Leray bilinear symbol"
  ∷ mkCascadeClosedWidthObligationRow
    cascadeClosureDefinitionObligation
    "Z_NS^infty is recorded as iterated zero-leakage closure under output-as-next-input triadic interactions"
    "turn the finite-stage ledger into a theorem about the intersection over all cascade depths"
  ∷ mkCascadeClosedWidthObligationRow
    outputProjectionDefinitionObligation
    "pi_out maps cascade-closed triads to the output direction c in S2"
    "connect this projection to the output-vorticity support condition used by Lei-Ren-Tian"
  ∷ mkCascadeClosedWidthObligationRow
    doubleHairyBallFrameMismatchObligation
    "near degeneracy, output eigenframe half-winding must be compared across two cascade generations"
    "prove the double-Hairy-Ball frame mismatch rather than reusing the old single-angle zero-mode argument"
  ∷ mkCascadeClosedWidthObligationRow
    whitneyTransversalityCodimensionObligation
    "the cascade-compatibility equations are recorded as a codimension target on the output sphere"
    "supply the Whitney-transversality/codimension proof excluding great-circle-covering output support"
  ∷ mkCascadeClosedWidthObligationRow
    positiveGreatCircleAvoidanceWidthObligation
    "the theorem target is w(pi_out(Z_NS^infty)) > 0"
    "prove a positive great-circle avoidance width for the cascade-closed output projection"
  ∷ mkCascadeClosedWidthObligationRow
    taoAveragedOperatorFalsifiabilityGuardObligation
    "Tao-style averaged operators may preserve energy cancellation while thickening zero modes"
    "show the theorem uses the true P(xi+eta) symbol and is not inherited by ordinary averaged NS models"
  ∷ mkCascadeClosedWidthObligationRow
    clayNavierStokesPromotionGuardObligation
    "CascadeClosedZeroModeOutputWidth alone is a finite-dimensional target, not a PDE regularity proof"
    "combine with Abel triadic defect measure, leakage square-function coercivity, and local defect monotonicity before any NS Clay promotion"
  ∷ []

cascadeClosedWidthObligationRowCount : Nat
cascadeClosedWidthObligationRowCount =
  listLength canonicalCascadeClosedWidthObligationRows

cascadeClosedWidthObligationRowCountIs9 :
  cascadeClosedWidthObligationRowCount ≡ 9
cascadeClosedWidthObligationRowCountIs9 =
  refl

------------------------------------------------------------------------
-- Fail-closed flags requested by the lane.

NSCascadeClosedZeroModeOutputWidthBoundaryRecorded : Bool
NSCascadeClosedZeroModeOutputWidthBoundaryRecorded =
  true

cascadeClosureRecorded : Bool
cascadeClosureRecorded =
  true

outputProjectionPiOutRecorded : Bool
outputProjectionPiOutRecorded =
  true

outputWidthTargetRecorded : Bool
outputWidthTargetRecorded =
  true

doubleHairyBallProofObligationRecorded : Bool
doubleHairyBallProofObligationRecorded =
  true

whitneyTransversalityProofObligationRecorded : Bool
whitneyTransversalityProofObligationRecorded =
  true

taoAveragedOperatorGuardRecorded : Bool
taoAveragedOperatorGuardRecorded =
  true

taoAveragedOperatorInheritsWidthTheorem : Bool
taoAveragedOperatorInheritsWidthTheorem =
  false

triadicZeroModeFamilyClassificationProved : Bool
triadicZeroModeFamilyClassificationProved =
  false

cascadeClosureProved : Bool
cascadeClosureProved =
  false

outputWidthProved : Bool
outputWidthProved =
  false

abelTriadicDefectMeasureConstructed : Bool
abelTriadicDefectMeasureConstructed =
  false

triadicLeakageSquareFunctionCoercivityProved : Bool
triadicLeakageSquareFunctionCoercivityProved =
  false

fullLocalDefectMonotonicity : Bool
fullLocalDefectMonotonicity =
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

cascadeClosureRecordedIsTrue :
  cascadeClosureRecorded ≡ true
cascadeClosureRecordedIsTrue =
  refl

outputWidthTargetRecordedIsTrue :
  outputWidthTargetRecorded ≡ true
outputWidthTargetRecordedIsTrue =
  refl

outputWidthProvedIsFalse :
  outputWidthProved ≡ false
outputWidthProvedIsFalse =
  refl

clayNavierStokesPromotedIsFalse :
  clayNavierStokesPromoted ≡ false
clayNavierStokesPromotedIsFalse =
  refl

taoAveragedOperatorInheritsWidthTheoremIsFalse :
  taoAveragedOperatorInheritsWidthTheorem ≡ false
taoAveragedOperatorInheritsWidthTheoremIsFalse =
  refl

------------------------------------------------------------------------
-- ORCSLPGF surface.

organizationString : String
organizationString =
  "O: Lane B records NSCascadeClosedZeroModeOutputWidth as a self-contained fail-closed Agda boundary."

requirementString : String
requirementString =
  "R: Replace the obsolete single-sphere zero-mode target with a cascade-closed triadic interaction zero-mode output-width theorem target."

codeArtifactString : String
codeArtifactString =
  "C: The module exports triadic carriers, Z_NS^triad, Z_NS^infty, pi_out, positive width target, proof-obligation rows, Tao averaged-operator guard, and false promotion flags."

stateString : String
stateString =
  "S: The true Leray triadic symbol module is imported as a typed anchor; cascade closure and output width are recorded targets only."

latticeString : String
latticeString =
  "L: true Leray symbol -> triadic zero modes -> iterated cascade closure -> output projection -> double-Hairy-Ball/Whitney obligations -> positive width target -> PDE transfer blockers."

proposalString : String
proposalString =
  "P: Promote only the corrected finite-dimensional target ledger; keep outputWidthProved, PDE transfer, local monotonicity, Clay NS, and terminal promotion false."

governanceString : String
governanceString =
  "G: Tao averaged-operator falsifiability is a guard: ordinary averaged NS models must not inherit this theorem."

gapString : String
gapString =
  "F: Missing evidence is the exact triadic symbol theorem, zero-mode classification, iterated cascade closure, double-Hairy-Ball/Whitney positive-width proof, Abel measure transfer, and square-function coercivity."

record NSCascadeClosedZeroModeOutputWidthORCSLPGF : Set where
  constructor nsCascadeClosedZeroModeOutputWidthORCSLPGF
  field
    organization :
      String
    requirement :
      String
    codeArtifact :
      String
    state :
      String
    lattice :
      String
    proposal :
      String
    governance :
      String
    gap :
      String

open NSCascadeClosedZeroModeOutputWidthORCSLPGF public

canonicalNSCascadeClosedZeroModeOutputWidthORCSLPGF :
  NSCascadeClosedZeroModeOutputWidthORCSLPGF
canonicalNSCascadeClosedZeroModeOutputWidthORCSLPGF =
  nsCascadeClosedZeroModeOutputWidthORCSLPGF
    organizationString
    requirementString
    codeArtifactString
    stateString
    latticeString
    proposalString
    governanceString
    gapString

record NSCascadeClosedZeroModeOutputWidthBoundary : Setω where
  constructor nsCascadeClosedZeroModeOutputWidthBoundary
  field
    symbolReference :
      String
    symbolReferenceIsCanonical :
      symbolReference ≡ trueLerayTriadicDefectSymbolReference
    symbolImported :
      Bool
    symbolImportedIsTrue :
      symbolImported ≡ true
    stringReferenceUsed :
      Bool
    stringReferenceUsedIsFalse :
      stringReferenceUsed ≡ false
    typedTrueSymbolReceipt :
      TrueSymbol.TrueLerayTriadicDefectSymbolBoundary
    typedTrueSymbolExactSymbolRecorded :
      TrueSymbol.exactSymbolRecorded
        typedTrueSymbolReceipt
      ≡ true
    typedTrueSymbolTaoGuardRecorded :
      TrueSymbol.taoGuardRecorded
        typedTrueSymbolReceipt
      ≡ true
    typedTrueSymbolWidthStillFalse :
      TrueSymbol.widthProved
        typedTrueSymbolReceipt
      ≡ false
    resonantTriad :
      ResonantTriadicInteraction
    resonantTriadIsCanonical :
      resonantTriad ≡ canonicalResonantTriad
    triadicZeroModeTarget :
      TriadicZeroModeSetTarget
    triadicZeroModeTargetIsCanonical :
      triadicZeroModeTarget ≡ canonicalTriadicZeroModeSetTarget
    cascadeClosedZeroModeTarget :
      CascadeClosedZeroModeSetTarget
    cascadeClosedZeroModeTargetIsCanonical :
      cascadeClosedZeroModeTarget
        ≡ canonicalCascadeClosedZeroModeSetTarget
    outputProjectionTarget :
      OutputProjectionPiOutTarget
    outputProjectionTargetIsCanonical :
      outputProjectionTarget ≡ canonicalOutputProjectionPiOutTarget
    widthTarget :
      GreatCircleAvoidanceWidthTarget
    widthTargetIsCanonical :
      widthTarget ≡ canonicalGreatCircleAvoidanceWidthTarget
    cascadeStages :
      List CascadeClosureStage
    cascadeStagesAreCanonical :
      cascadeStages ≡ canonicalCascadeClosureStages
    cascadeStageCount :
      Nat
    cascadeStageCountIs5 :
      cascadeStageCount ≡ 5
    obligationRows :
      List CascadeClosedWidthObligationRow
    obligationRowsAreCanonical :
      obligationRows ≡ canonicalCascadeClosedWidthObligationRows
    obligationRowCount :
      Nat
    obligationRowCountIs9 :
      obligationRowCount ≡ 9
    orcslpgf :
      NSCascadeClosedZeroModeOutputWidthORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSCascadeClosedZeroModeOutputWidthORCSLPGF
    cascadeClosureRecordedField :
      Bool
    cascadeClosureRecordedFieldIsTrue :
      cascadeClosureRecordedField ≡ true
    outputWidthTargetRecordedField :
      Bool
    outputWidthTargetRecordedFieldIsTrue :
      outputWidthTargetRecordedField ≡ true
    outputWidthProvedField :
      Bool
    outputWidthProvedFieldIsFalse :
      outputWidthProvedField ≡ false
    taoAveragedOperatorGuardRecordedField :
      Bool
    taoAveragedOperatorGuardRecordedFieldIsTrue :
      taoAveragedOperatorGuardRecordedField ≡ true
    taoAveragedOperatorInheritsWidthTheoremField :
      Bool
    taoAveragedOperatorInheritsWidthTheoremFieldIsFalse :
      taoAveragedOperatorInheritsWidthTheoremField ≡ false
    clayNavierStokesPromotedField :
      Bool
    clayNavierStokesPromotedFieldIsFalse :
      clayNavierStokesPromotedField ≡ false

open NSCascadeClosedZeroModeOutputWidthBoundary public

canonicalNSCascadeClosedZeroModeOutputWidthBoundary :
  NSCascadeClosedZeroModeOutputWidthBoundary
canonicalNSCascadeClosedZeroModeOutputWidthBoundary =
  nsCascadeClosedZeroModeOutputWidthBoundary
    trueLerayTriadicDefectSymbolReference
    refl
    trueLerayTriadicDefectSymbolImported
    refl
    trueLerayTriadicDefectSymbolStringReferenceUsed
    refl
    trueLerayTriadicDefectSymbolReceipt
    TrueSymbol.exactSymbolRecordedFlagIsTrue
    TrueSymbol.taoGuardRecordedFlagIsTrue
    TrueSymbol.widthProvedFlagIsFalse
    canonicalResonantTriad
    refl
    canonicalTriadicZeroModeSetTarget
    refl
    canonicalCascadeClosedZeroModeSetTarget
    refl
    canonicalOutputProjectionPiOutTarget
    refl
    canonicalGreatCircleAvoidanceWidthTarget
    refl
    canonicalCascadeClosureStages
    refl
    cascadeClosureStageCount
    refl
    canonicalCascadeClosedWidthObligationRows
    refl
    cascadeClosedWidthObligationRowCount
    refl
    canonicalNSCascadeClosedZeroModeOutputWidthORCSLPGF
    refl
    cascadeClosureRecorded
    refl
    outputWidthTargetRecorded
    refl
    outputWidthProved
    refl
    taoAveragedOperatorGuardRecorded
    refl
    taoAveragedOperatorInheritsWidthTheorem
    refl
    clayNavierStokesPromoted
    refl

canonicalNSCascadeClosedZeroModeOutputWidthBoundaryKeepsWidthFalse :
  outputWidthProvedField
    canonicalNSCascadeClosedZeroModeOutputWidthBoundary
  ≡ false
canonicalNSCascadeClosedZeroModeOutputWidthBoundaryKeepsWidthFalse =
  refl

canonicalNSCascadeClosedZeroModeOutputWidthBoundaryKeepsClayFalse :
  clayNavierStokesPromotedField
    canonicalNSCascadeClosedZeroModeOutputWidthBoundary
  ≡ false
canonicalNSCascadeClosedZeroModeOutputWidthBoundaryKeepsClayFalse =
  refl

canonicalNSCascadeClosedZeroModeOutputWidthBoundaryRecordsCascade :
  cascadeClosureRecordedField
    canonicalNSCascadeClosedZeroModeOutputWidthBoundary
  ≡ true
canonicalNSCascadeClosedZeroModeOutputWidthBoundaryRecordsCascade =
  refl

canonicalNSCascadeClosedZeroModeOutputWidthBoundaryRecordsWidthTarget :
  outputWidthTargetRecordedField
    canonicalNSCascadeClosedZeroModeOutputWidthBoundary
  ≡ true
canonicalNSCascadeClosedZeroModeOutputWidthBoundaryRecordsWidthTarget =
  refl

data NSCascadeClosedZeroModeOutputWidthPromotionToken : Set where

nSCascadeClosedZeroModeOutputWidthPromotionTokenImpossibleHere :
  NSCascadeClosedZeroModeOutputWidthPromotionToken →
  Set
nSCascadeClosedZeroModeOutputWidthPromotionTokenImpossibleHere ()

canonicalNSCascadeClosedZeroModeOutputWidthFailClosedFindings :
  List String
canonicalNSCascadeClosedZeroModeOutputWidthFailClosedFindings =
  "Old angular Z_NS subset S2 is superseded by cascade-closed triadic Z_NS^infty."
  ∷ "Typed anchor: NSTrueLerayTriadicDefectSymbol records the exact non-averaged P(xi+eta) Leray symbol and Tao guard."
  ∷ "Lei-Ren-Tian applies to pi_out support, not to a scalar angular cutoff."
  ∷ "Tao averaged NS is a guard: averaged operators must not inherit the positive-width theorem."
  ∷ "Double-Hairy-Ball and Whitney-transversality rows are proof obligations only."
  ∷ "NS Clay promotion remains false until PDE transfer and local monotonicity are proved."
  ∷ []

canonicalNSCascadeClosedZeroModeOutputWidthFindingCount : Nat
canonicalNSCascadeClosedZeroModeOutputWidthFindingCount =
  listLength canonicalNSCascadeClosedZeroModeOutputWidthFailClosedFindings

canonicalNSCascadeClosedZeroModeOutputWidthFindingCountIs6 :
  canonicalNSCascadeClosedZeroModeOutputWidthFindingCount ≡ 6
canonicalNSCascadeClosedZeroModeOutputWidthFindingCountIs6 =
  refl
