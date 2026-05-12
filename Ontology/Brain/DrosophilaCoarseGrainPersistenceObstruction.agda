module Ontology.Brain.DrosophilaCoarseGrainPersistenceObstruction where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import Ontology.Brain.DrosophilaHemibrainExternalRunReceipt using
  (HemibrainArtifactChecksum; coarseRandomBlocksChecksum;
   coarseDegreeBinnedChecksum; coarseROIChecksum; coarseRadiusR1Checksum;
   coarseRadiusR2Checksum)

------------------------------------------------------------------------
-- Negative receipt: selected coarse-grain runs collapse to the trivial
-- one-step zero-defect curve.  This blocks promotion of the Sprint 3
-- single-scale geometry into a multiscale persistence theorem.

data CoarseGrainMode : Set where
  randomBlocks degreeBinned roi radiusR1 radiusR2 : CoarseGrainMode

record CoarseGrainCurveReceipt : Set where
  constructor coarseGrainCurveReceipt
  field
    mode : CoarseGrainMode
    curveArtifact : HemibrainArtifactChecksum
    defectTrace : List Nat
    finalDefect : Nat
    trivialOneStepCurve : Bool

randomBlocksObstructionCurve : CoarseGrainCurveReceipt
randomBlocksObstructionCurve =
  coarseGrainCurveReceipt randomBlocks coarseRandomBlocksChecksum (0 ∷ []) 0 true

degreeBinnedObstructionCurve : CoarseGrainCurveReceipt
degreeBinnedObstructionCurve =
  coarseGrainCurveReceipt degreeBinned coarseDegreeBinnedChecksum (0 ∷ []) 0 true

roiObstructionCurve : CoarseGrainCurveReceipt
roiObstructionCurve =
  coarseGrainCurveReceipt roi coarseROIChecksum (0 ∷ []) 0 true

radiusR1ObstructionCurve : CoarseGrainCurveReceipt
radiusR1ObstructionCurve =
  coarseGrainCurveReceipt radiusR1 coarseRadiusR1Checksum (0 ∷ []) 0 true

radiusR2ObstructionCurve : CoarseGrainCurveReceipt
radiusR2ObstructionCurve =
  coarseGrainCurveReceipt radiusR2 coarseRadiusR2Checksum (0 ∷ []) 0 true

record DrosophilaCoarseGrainPersistenceObstruction : Set₁ where
  field
    obstructionCurves : List CoarseGrainCurveReceipt
    multiscalePersistenceEstablished : Bool
    promotesBrainLane : Bool
    obstructionBoundary : List String

drosophilaCoarseGrainPersistenceObstruction :
  DrosophilaCoarseGrainPersistenceObstruction
drosophilaCoarseGrainPersistenceObstruction =
  record
    { obstructionCurves =
        randomBlocksObstructionCurve
        ∷ degreeBinnedObstructionCurve
        ∷ roiObstructionCurve
        ∷ radiusR1ObstructionCurve
        ∷ radiusR2ObstructionCurve
        ∷ []
    ; multiscalePersistenceEstablished = false
    ; promotesBrainLane = false
    ; obstructionBoundary =
        "Selected coarse-grain curves are one-step zero-defect curves"
        ∷ "The Sprint 3 neutral/defect geometry is not promoted to multiscale persistence"
        ∷ "This is a negative receipt, not a biological impossibility theorem"
        ∷ "Future finer or locality-preserving coarse-grainings may create new receipts"
        ∷ []
    }

randomBlocksFinalDefectZero :
  CoarseGrainCurveReceipt.finalDefect randomBlocksObstructionCurve ≡ zero
randomBlocksFinalDefectZero = refl

degreeBinnedFinalDefectZero :
  CoarseGrainCurveReceipt.finalDefect degreeBinnedObstructionCurve ≡ zero
degreeBinnedFinalDefectZero = refl

multiscalePersistenceBlocked :
  DrosophilaCoarseGrainPersistenceObstruction.multiscalePersistenceEstablished
    drosophilaCoarseGrainPersistenceObstruction
  ≡
  false
multiscalePersistenceBlocked = refl

coarseObstructionDoesNotPromote :
  DrosophilaCoarseGrainPersistenceObstruction.promotesBrainLane
    drosophilaCoarseGrainPersistenceObstruction
  ≡
  false
coarseObstructionDoesNotPromote = refl
