module DASHI.Core.HemibrainRunCertificates where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Empirical receipts: data, not universal theorems
------------------------------------------------------------------------

data CoarseMethod : Set where
  randomBlocks : Nat → Nat → CoarseMethod
  degreeBinned : Nat → CoarseMethod
  roiPrimary : CoarseMethod
  hopRadius : Nat → CoarseMethod
  voxelDegenerate : Nat → CoarseMethod

record CoarseRunReceipt : Set where
  field
    method : CoarseMethod
    coarseNodes : Nat
    coarseEdges : Nat
    convergenceSteps : Nat
    finalPositive : Nat
    finalNeutral : Nat
    finalNegative : Nat
    positiveComponents : Nat
    defectAtConvergence : Nat

open CoarseRunReceipt public

randomK50Seed0 : CoarseRunReceipt
randomK50Seed0 = record
  { method = randomBlocks 50 0
  ; coarseNodes = 3599
  ; coarseEdges = 5180000
  ; convergenceSteps = 1
  ; finalPositive = 3599
  ; finalNeutral = 0
  ; finalNegative = 0
  ; positiveComponents = 1
  ; defectAtConvergence = 0
  }

randomK100Seed0 : CoarseRunReceipt
randomK100Seed0 = record
  { method = randomBlocks 100 0
  ; coarseNodes = 1800
  ; coarseEdges = 2767255
  ; convergenceSteps = 1
  ; finalPositive = 1800
  ; finalNeutral = 0
  ; finalNegative = 0
  ; positiveComponents = 1
  ; defectAtConvergence = 0
  }

randomK200Seed0 : CoarseRunReceipt
randomK200Seed0 = record
  { method = randomBlocks 200 0
  ; coarseNodes = 900
  ; coarseEdges = 810000
  ; convergenceSteps = 2
  ; finalPositive = 900
  ; finalNeutral = 0
  ; finalNegative = 0
  ; positiveComponents = 1
  ; defectAtConvergence = 0
  }

degreeBinnedK100 : CoarseRunReceipt
degreeBinnedK100 = record
  { method = degreeBinned 100
  ; coarseNodes = 1800
  ; coarseEdges = 846301
  ; convergenceSteps = 1
  ; finalPositive = 1800
  ; finalNeutral = 0
  ; finalNegative = 0
  ; positiveComponents = 1
  ; defectAtConvergence = 0
  }

roiPrimaryRun : CoarseRunReceipt
roiPrimaryRun = record
  { method = roiPrimary
  ; coarseNodes = 62
  ; coarseEdges = 1786
  ; convergenceSteps = 1
  ; finalPositive = 62
  ; finalNeutral = 0
  ; finalNegative = 0
  ; positiveComponents = 1
  ; defectAtConvergence = 0
  }

hopRadiusOneRun : CoarseRunReceipt
hopRadiusOneRun = record
  { method = hopRadius 1
  ; coarseNodes = 84748
  ; coarseEdges = 905522
  ; convergenceSteps = 1
  ; finalPositive = 54382
  ; finalNeutral = 30366
  ; finalNegative = 0
  ; positiveComponents = 46
  ; defectAtConvergence = 0
  }

hopRadiusTwoRun : CoarseRunReceipt
hopRadiusTwoRun = record
  { method = hopRadius 2
  ; coarseNodes = 69424
  ; coarseEdges = 304424
  ; convergenceSteps = 1
  ; finalPositive = 43503
  ; finalNeutral = 25921
  ; finalNegative = 0
  ; positiveComponents = 46
  ; defectAtConvergence = 0
  }

voxelMissingCoordinates : CoarseRunReceipt
voxelMissingCoordinates = record
  { method = voxelDegenerate 10000
  ; coarseNodes = 1
  ; coarseEdges = 1
  ; convergenceSteps = 0
  ; finalPositive = 0
  ; finalNeutral = 0
  ; finalNegative = 0
  ; positiveComponents = 0
  ; defectAtConvergence = 0
  }

record ReceiptInterpretationBoundary (R : CoarseRunReceipt) : Set where
  field
    particularRunOnly : ⊤
    noUniversalCollapseTheorem : ⊤
    noAutomaticBiologicalMeaning : ⊤

safeReceiptBoundary : (R : CoarseRunReceipt) → ReceiptInterpretationBoundary R
safeReceiptBoundary R = record
  { particularRunOnly = tt
  ; noUniversalCollapseTheorem = tt
  ; noAutomaticBiologicalMeaning = tt
  }
