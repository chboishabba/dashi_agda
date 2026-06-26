module DASHI.Physics.Closure.NSGeometricConcentrationCarrierReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- Fail-closed receipt for the geometric concentration obstruction.
--
-- Remaining obstruction:
--   every possible blow-up point must lie on or approach ∂Ω_K = { lambda2 = 0 }.
-- Equivalently, the blow-up carrier must land in the Kato/biaxial carrier.
--
-- If blow-up can occur away from ∂Ω_K, the carrier-surface control does not
-- close Clay.
--
-- Required shape recorded here:
--   BlowUpPoint(u,T*) -> exists sequence (x_n,t_n) with t_n < T*,
--   t_n -> T*, lambda2(x_n,t_n) -> 0, |omega| large, and layer-thickness /
--   coarea compatibility.
--
-- The pressure-Poisson bypass, GD1 bridge, and LayerKorn/BKM bridge remain
-- conditional on this geometric concentration theorem.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSGeometricConcentrationStatus : Set where
  geometricConcentrationObstructionRecordedNoClayPromotion :
    NSGeometricConcentrationStatus

data NSGeometricConcentrationStage : Set where
  remainingObstructionOnBoundaryCarrierRecorded :
    NSGeometricConcentrationStage
  blowUpPointMustApproachBoundaryCarrierRecorded :
    NSGeometricConcentrationStage
  blowUpAwayFromBoundaryDoesNotCloseClayRecorded :
    NSGeometricConcentrationStage
  sequenceWitnessShapeRecorded :
    NSGeometricConcentrationStage
  layerThicknessCoareaCompatibilityRecorded :
    NSGeometricConcentrationStage
  pressurePoissonBypassGuardedByGeometryRecorded :
    NSGeometricConcentrationStage
  gd1BridgeGuardedByGeometryRecorded :
    NSGeometricConcentrationStage
  layerKornBkmBridgeGuardedByGeometryRecorded :
    NSGeometricConcentrationStage
  finalProofConditionalOnlyRecorded :
    NSGeometricConcentrationStage
  clayPromotionBlockedRecorded :
    NSGeometricConcentrationStage

canonicalNSGeometricConcentrationStages :
  List NSGeometricConcentrationStage
canonicalNSGeometricConcentrationStages =
  remainingObstructionOnBoundaryCarrierRecorded
  ∷ blowUpPointMustApproachBoundaryCarrierRecorded
  ∷ blowUpAwayFromBoundaryDoesNotCloseClayRecorded
  ∷ sequenceWitnessShapeRecorded
  ∷ layerThicknessCoareaCompatibilityRecorded
  ∷ pressurePoissonBypassGuardedByGeometryRecorded
  ∷ gd1BridgeGuardedByGeometryRecorded
  ∷ layerKornBkmBridgeGuardedByGeometryRecorded
  ∷ finalProofConditionalOnlyRecorded
  ∷ clayPromotionBlockedRecorded
  ∷ []

data NSGeometricConcentrationBlocker : Set where
  geometricConcentrationTheoremMissing :
    NSGeometricConcentrationBlocker
  blowUpAwayFromBoundaryLeakageOpen :
    NSGeometricConcentrationBlocker
  carrierSurfaceControlDoesNotCloseClay :
    NSGeometricConcentrationBlocker
  pressurePoissonBypassNotStandalone :
    NSGeometricConcentrationBlocker
  gd1NotStandalone :
    NSGeometricConcentrationBlocker
  layerKornBkmNotStandalone :
    NSGeometricConcentrationBlocker
  noClayPromotion :
    NSGeometricConcentrationBlocker

canonicalNSGeometricConcentrationBlockers :
  List NSGeometricConcentrationBlocker
canonicalNSGeometricConcentrationBlockers =
  geometricConcentrationTheoremMissing
  ∷ blowUpAwayFromBoundaryLeakageOpen
  ∷ carrierSurfaceControlDoesNotCloseClay
  ∷ pressurePoissonBypassNotStandalone
  ∷ gd1NotStandalone
  ∷ layerKornBkmNotStandalone
  ∷ noClayPromotion
  ∷ []

oStringValue : String
oStringValue =
  "O: obstruction overview"

rStringValue : String
rStringValue =
  "R: remaining obstruction is boundary concentration of every blow-up carrier"

cStringValue : String
cStringValue =
  "C: blow-up carrier must lie on the Kato/biaxial carrier, i.e. lambda2 = 0"

sStringValue : String
sStringValue =
  "S: BlowUpPoint(u,T*) must produce a boundary-approaching sequence (x_n,t_n)"

lStringValue : String
lStringValue =
  "L: layer thickness and coarea compatibility remain part of the required shape"

pStringValue : String
pStringValue =
  "P: pressure-Poisson bypass stays conditional on the geometric concentration theorem"

gStringValue : String
gStringValue =
  "G: GD1 bridge stays conditional on the same geometric concentration theorem"

fStringValue : String
fStringValue =
  "F: final proof remains conditional, and Clay promotion stays blocked here"

canonicalNSGeometricConcentrationORCSLPGFStrings :
  List String
canonicalNSGeometricConcentrationORCSLPGFStrings =
  oStringValue
  ∷ rStringValue
  ∷ cStringValue
  ∷ sStringValue
  ∷ lStringValue
  ∷ pStringValue
  ∷ gStringValue
  ∷ fStringValue
  ∷ []

blowUpPointShapeStatement : String
blowUpPointShapeStatement =
  "BlowUpPoint(u,T*) -> exists sequence (x_n,t_n) with t_n < T*, t_n -> T*, lambda2(x_n,t_n) -> 0, |omega| large, and layer-thickness/coarea compatibility."

boundaryCarrierObstructionStatement : String
boundaryCarrierObstructionStatement =
  "Every possible blow-up point must lie on or approach ∂Ω_K = { lambda2 = 0 }; otherwise the carrier-surface control does not close Clay."

pressurePoissonGD1LayerKornBKMConditionalStatement : String
pressurePoissonGD1LayerKornBKMConditionalStatement =
  "Pressure-Poisson bypass, GD1, LayerKorn, and BKM are recorded as final-proof inputs only conditional on the geometric concentration theorem."

carrierSurfaceFailureStatement : String
carrierSurfaceFailureStatement =
  "If blow-up can occur away from ∂Ω_K, the carrier-surface control does not close Clay."

data NSGeometricConcentrationProjectionLemma : Set where
  boundaryCarrierProjectionLemma :
    NSGeometricConcentrationProjectionLemma
  sequenceProjectionLemma :
    NSGeometricConcentrationProjectionLemma
  lambda2ProjectionLemma :
    NSGeometricConcentrationProjectionLemma
  layerThicknessCoareaProjectionLemma :
    NSGeometricConcentrationProjectionLemma
  conditionalBridgeProjectionLemma :
    NSGeometricConcentrationProjectionLemma

canonicalNSGeometricConcentrationProjectionLemmaTrail :
  List NSGeometricConcentrationProjectionLemma
canonicalNSGeometricConcentrationProjectionLemmaTrail =
  boundaryCarrierProjectionLemma
  ∷ sequenceProjectionLemma
  ∷ lambda2ProjectionLemma
  ∷ layerThicknessCoareaProjectionLemma
  ∷ conditionalBridgeProjectionLemma
  ∷ []

boundaryCarrierProjectionLemmaText : String
boundaryCarrierProjectionLemmaText =
  "Projection lemma: any blow-up carrier must project to the boundary carrier ∂Ω_K."

sequenceProjectionLemmaText : String
sequenceProjectionLemmaText =
  "Projection lemma: BlowUpPoint(u,T*) projects to a sequence (x_n,t_n) with t_n < T* and t_n -> T*."

lambda2ProjectionLemmaText : String
lambda2ProjectionLemmaText =
  "Projection lemma: along the sequence, lambda2(x_n,t_n) -> 0."

layerThicknessCoareaProjectionLemmaText : String
layerThicknessCoareaProjectionLemmaText =
  "Projection lemma: the same sequence must respect layer thickness and coarea compatibility."

conditionalBridgeProjectionLemmaText : String
conditionalBridgeProjectionLemmaText =
  "Projection lemma: the pressure-Poisson bypass, GD1, and LayerKorn/BKM bridges only feed the final proof conditionally."

record NSGeometricConcentrationProjectionLemmas : Set where
  field
    boundaryCarrierProjectionLemmaTextField :
      String
    boundaryCarrierProjectionLemmaTextFieldIsCanonical :
      boundaryCarrierProjectionLemmaTextField ≡ boundaryCarrierProjectionLemmaText

    sequenceProjectionLemmaTextField :
      String
    sequenceProjectionLemmaTextFieldIsCanonical :
      sequenceProjectionLemmaTextField ≡ sequenceProjectionLemmaText

    lambda2ProjectionLemmaTextField :
      String
    lambda2ProjectionLemmaTextFieldIsCanonical :
      lambda2ProjectionLemmaTextField ≡ lambda2ProjectionLemmaText

    layerThicknessCoareaProjectionLemmaTextField :
      String
    layerThicknessCoareaProjectionLemmaTextFieldIsCanonical :
      layerThicknessCoareaProjectionLemmaTextField
      ≡ layerThicknessCoareaProjectionLemmaText

    conditionalBridgeProjectionLemmaTextField :
      String
    conditionalBridgeProjectionLemmaTextFieldIsCanonical :
      conditionalBridgeProjectionLemmaTextField
      ≡ conditionalBridgeProjectionLemmaText

open NSGeometricConcentrationProjectionLemmas public

record NSGeometricConcentrationSequenceWitness : Set where
  field
    blowUpPoint :
      String
    blowUpPointIsCanonical :
      blowUpPoint ≡ "BlowUpPoint(u,T*)"

    sequenceXn :
      String
    sequenceXnIsCanonical :
      sequenceXn ≡ "(x_n)"

    sequenceTn :
      String
    sequenceTnIsCanonical :
      sequenceTn ≡ "(t_n)"

    t_nLessThanTStar :
      Bool
    t_nLessThanTStarIsTrue :
      t_nLessThanTStar ≡ true

    t_nConvergesToTStar :
      Bool
    t_nConvergesToTStarIsTrue :
      t_nConvergesToTStar ≡ true

    lambda2ConvergesToZero :
      Bool
    lambda2ConvergesToZeroIsTrue :
      lambda2ConvergesToZero ≡ true

    omegaLargeAlongSequence :
      Bool
    omegaLargeAlongSequenceIsTrue :
      omegaLargeAlongSequence ≡ true

    layerThicknessCoareaCompatible :
      Bool
    layerThicknessCoareaCompatibleIsTrue :
      layerThicknessCoareaCompatible ≡ true

open NSGeometricConcentrationSequenceWitness public

canonicalNSGeometricConcentrationProjectionLemmas :
  NSGeometricConcentrationProjectionLemmas
canonicalNSGeometricConcentrationProjectionLemmas =
  record
    { boundaryCarrierProjectionLemmaTextField =
        boundaryCarrierProjectionLemmaText
    ; boundaryCarrierProjectionLemmaTextFieldIsCanonical =
        refl
    ; sequenceProjectionLemmaTextField =
        sequenceProjectionLemmaText
    ; sequenceProjectionLemmaTextFieldIsCanonical =
        refl
    ; lambda2ProjectionLemmaTextField =
        lambda2ProjectionLemmaText
    ; lambda2ProjectionLemmaTextFieldIsCanonical =
        refl
    ; layerThicknessCoareaProjectionLemmaTextField =
        layerThicknessCoareaProjectionLemmaText
    ; layerThicknessCoareaProjectionLemmaTextFieldIsCanonical =
        refl
    ; conditionalBridgeProjectionLemmaTextField =
        conditionalBridgeProjectionLemmaText
    ; conditionalBridgeProjectionLemmaTextFieldIsCanonical =
        refl
    }

canonicalNSGeometricConcentrationSequenceWitness :
  NSGeometricConcentrationSequenceWitness
canonicalNSGeometricConcentrationSequenceWitness =
  record
    { blowUpPoint =
        "BlowUpPoint(u,T*)"
    ; blowUpPointIsCanonical =
        refl
    ; sequenceXn =
        "(x_n)"
    ; sequenceXnIsCanonical =
        refl
    ; sequenceTn =
        "(t_n)"
    ; sequenceTnIsCanonical =
        refl
    ; t_nLessThanTStar =
        true
    ; t_nLessThanTStarIsTrue =
        refl
    ; t_nConvergesToTStar =
        true
    ; t_nConvergesToTStarIsTrue =
        refl
    ; lambda2ConvergesToZero =
        true
    ; lambda2ConvergesToZeroIsTrue =
        refl
    ; omegaLargeAlongSequence =
        true
    ; omegaLargeAlongSequenceIsTrue =
        refl
    ; layerThicknessCoareaCompatible =
        true
    ; layerThicknessCoareaCompatibleIsTrue =
        refl
    }

data NSGeometricConcentrationPromotion : Set where

nsGeometricConcentrationPromotionImpossibleHere :
  NSGeometricConcentrationPromotion →
  ⊥
nsGeometricConcentrationPromotionImpossibleHere ()

geometricConcentrationObstructionStatement : String
geometricConcentrationObstructionStatement =
  "Geometric concentration is the remaining NS obstruction: every possible blow-up point must lie on or approach ∂Ω_K = { lambda2 = 0 }, and the final proof stays conditional on this theorem."

finalProofConditionalStatement : String
finalProofConditionalStatement =
  "The final proof is conditional on geometric concentration; pressure-Poisson bypass, GD1, LayerKorn, and BKM do not close Clay without it."

geometricConcentrationReceiptBoundary : List String
geometricConcentrationReceiptBoundary =
  boundaryCarrierObstructionStatement
  ∷ blowUpPointShapeStatement
  ∷ carrierSurfaceFailureStatement
  ∷ pressurePoissonGD1LayerKornBKMConditionalStatement
  ∷ geometricConcentrationObstructionStatement
  ∷ finalProofConditionalStatement
  ∷ []

data NSGeometricConcentrationCarrierPromotion : Set where

nsGeometricConcentrationCarrierPromotionImpossibleHere :
  NSGeometricConcentrationCarrierPromotion →
  ⊥
nsGeometricConcentrationCarrierPromotionImpossibleHere ()

record NSGeometricConcentrationCarrierReceipt : Set where
  field
    status :
      NSGeometricConcentrationStatus
    statusIsCanonical :
      status
      ≡ geometricConcentrationObstructionRecordedNoClayPromotion

    authority :
      Bool
    authorityIsFalse :
      authority ≡ false

    stages :
      List NSGeometricConcentrationStage
    stagesAreCanonical :
      stages ≡ canonicalNSGeometricConcentrationStages

    stageCount :
      Nat
    stageCountIsCanonical :
      stageCount ≡ listLength canonicalNSGeometricConcentrationStages

    blockers :
      List NSGeometricConcentrationBlocker
    blockersAreCanonical :
      blockers ≡ canonicalNSGeometricConcentrationBlockers

    blockerCount :
      Nat
    blockerCountIsCanonical :
      blockerCount ≡ listLength canonicalNSGeometricConcentrationBlockers

    orcslpfgStrings :
      List String
    orcslpfgStringsAreCanonical :
      orcslpfgStrings ≡ canonicalNSGeometricConcentrationORCSLPGFStrings

    orcslpfgStringCount :
      Nat
    orcslpfgStringCountIsCanonical :
      orcslpfgStringCount
      ≡ listLength canonicalNSGeometricConcentrationORCSLPGFStrings

    projectionLemmas :
      NSGeometricConcentrationProjectionLemmas
    projectionLemmasAreCanonical :
      projectionLemmas ≡ canonicalNSGeometricConcentrationProjectionLemmas

    sequenceWitness :
      NSGeometricConcentrationSequenceWitness
    sequenceWitnessIsCanonical :
      sequenceWitness ≡ canonicalNSGeometricConcentrationSequenceWitness

    blowUpPointShape :
      String
    blowUpPointShapeIsCanonical :
      blowUpPointShape ≡ blowUpPointShapeStatement

    boundaryCarrierObstruction :
      String
    boundaryCarrierObstructionIsCanonical :
      boundaryCarrierObstruction ≡ boundaryCarrierObstructionStatement

    carrierSurfaceFailure :
      String
    carrierSurfaceFailureIsCanonical :
      carrierSurfaceFailure ≡ carrierSurfaceFailureStatement

    pressurePoissonGD1LayerKornBKMConditional :
      String
    pressurePoissonGD1LayerKornBKMConditionalIsCanonical :
      pressurePoissonGD1LayerKornBKMConditional
      ≡ pressurePoissonGD1LayerKornBKMConditionalStatement

    geometricConcentrationObstruction :
      String
    geometricConcentrationObstructionIsCanonical :
      geometricConcentrationObstruction
      ≡ geometricConcentrationObstructionStatement

    finalProofConditional :
      String
    finalProofConditionalIsCanonical :
      finalProofConditional ≡ finalProofConditionalStatement

    pressurePoissonBypassRecorded :
      Bool
    pressurePoissonBypassRecordedIsTrue :
      pressurePoissonBypassRecorded ≡ true

    gd1BridgeRecorded :
      Bool
    gd1BridgeRecordedIsTrue :
      gd1BridgeRecorded ≡ true

    layerKornBkmBridgeRecorded :
      Bool
    layerKornBkmBridgeRecordedIsTrue :
      layerKornBkmBridgeRecorded ≡ true

    finalProofConditionalOnGeometricConcentration :
      Bool
    finalProofConditionalOnGeometricConcentrationIsTrue :
      finalProofConditionalOnGeometricConcentration ≡ true

    carrierSurfaceControlClosesClay :
      Bool
    carrierSurfaceControlClosesClayIsFalse :
      carrierSurfaceControlClosesClay ≡ false

    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

    receiptBoundary :
      List String
    receiptBoundaryIsCanonical :
      receiptBoundary ≡ geometricConcentrationReceiptBoundary

open NSGeometricConcentrationCarrierReceipt public

canonicalNSGeometricConcentrationCarrierReceipt :
  NSGeometricConcentrationCarrierReceipt
canonicalNSGeometricConcentrationCarrierReceipt =
  record
    { status =
        geometricConcentrationObstructionRecordedNoClayPromotion
    ; statusIsCanonical =
        refl
    ; authority =
        false
    ; authorityIsFalse =
        refl
    ; stages =
        canonicalNSGeometricConcentrationStages
    ; stagesAreCanonical =
        refl
    ; stageCount =
        listLength canonicalNSGeometricConcentrationStages
    ; stageCountIsCanonical =
        refl
    ; blockers =
        canonicalNSGeometricConcentrationBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCount =
        listLength canonicalNSGeometricConcentrationBlockers
    ; blockerCountIsCanonical =
        refl
    ; orcslpfgStrings =
        canonicalNSGeometricConcentrationORCSLPGFStrings
    ; orcslpfgStringsAreCanonical =
        refl
    ; orcslpfgStringCount =
        listLength canonicalNSGeometricConcentrationORCSLPGFStrings
    ; orcslpfgStringCountIsCanonical =
        refl
    ; projectionLemmas =
        canonicalNSGeometricConcentrationProjectionLemmas
    ; projectionLemmasAreCanonical =
        refl
    ; sequenceWitness =
        canonicalNSGeometricConcentrationSequenceWitness
    ; sequenceWitnessIsCanonical =
        refl
    ; blowUpPointShape =
        blowUpPointShapeStatement
    ; blowUpPointShapeIsCanonical =
        refl
    ; boundaryCarrierObstruction =
        boundaryCarrierObstructionStatement
    ; boundaryCarrierObstructionIsCanonical =
        refl
    ; carrierSurfaceFailure =
        carrierSurfaceFailureStatement
    ; carrierSurfaceFailureIsCanonical =
        refl
    ; pressurePoissonGD1LayerKornBKMConditional =
        pressurePoissonGD1LayerKornBKMConditionalStatement
    ; pressurePoissonGD1LayerKornBKMConditionalIsCanonical =
        refl
    ; geometricConcentrationObstruction =
        geometricConcentrationObstructionStatement
    ; geometricConcentrationObstructionIsCanonical =
        refl
    ; finalProofConditional =
        finalProofConditionalStatement
    ; finalProofConditionalIsCanonical =
        refl
    ; pressurePoissonBypassRecorded =
        true
    ; pressurePoissonBypassRecordedIsTrue =
        refl
    ; gd1BridgeRecorded =
        true
    ; gd1BridgeRecordedIsTrue =
        refl
    ; layerKornBkmBridgeRecorded =
        true
    ; layerKornBkmBridgeRecordedIsTrue =
        refl
    ; finalProofConditionalOnGeometricConcentration =
        true
    ; finalProofConditionalOnGeometricConcentrationIsTrue =
        refl
    ; carrierSurfaceControlClosesClay =
        false
    ; carrierSurfaceControlClosesClayIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; receiptBoundary =
        geometricConcentrationReceiptBoundary
    ; receiptBoundaryIsCanonical =
        refl
    }
