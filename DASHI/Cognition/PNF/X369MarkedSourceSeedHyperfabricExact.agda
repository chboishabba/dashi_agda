module DASHI.Cognition.PNF.X369MarkedSourceSeedHyperfabricExact where

-- ORIGINAL SOURCE SEED GEOMETRY, NOT A NEW LEARNED CLAIM.
-- SourceGeometryOrderedLearner.signed_seed consumes (M3,D3,0,0,0).
-- The declared public task mean lives on 7 source points; D on T3^3.
-- Reuse the full native 19683-point geometry without identifying them.
-- Attribution: original Leech-LILA Anatolii Kornienko; DASHI extension.
-- Agda kernel intentionally deferred, no postulates or holes.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import DASHI.Foundations.SSPTritCarrier as T
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as H
import DASHI.Cognition.PNF.X369InputIndexedFutureConsumerExact as F

data Mean7 : Set where
  zeroMean xNeg xPos yNeg yPos zNeg zPos : Mean7

meanPoint : Mean7 → H.Ternary27Point
meanPoint zeroMean = H.origin
meanPoint xNeg = H.ternary27Point T.sspNegOne T.sspZero T.sspZero
meanPoint xPos = H.ternary27Point T.sspPosOne T.sspZero T.sspZero
meanPoint yNeg = H.ternary27Point T.sspZero T.sspNegOne T.sspZero
meanPoint yPos = H.ternary27Point T.sspZero T.sspPosOne T.sspZero
meanPoint zNeg = H.ternary27Point T.sspZero T.sspZero T.sspNegOne
meanPoint zPos = H.ternary27Point T.sspZero T.sspZero T.sspPosOne

record SourceSeed : Set where
  constructor seed
  field
    mean : Mean7
    signedResidual : H.Ternary27Point
open SourceSeed public

-- Native marked subset: first T3 is 7-point mean, second T3 is the
-- full signed 27-state residual; third T3 is the distinguished origin.
toFullFabric : SourceSeed → H.TernaryHyperformalPoint
toFullFabric s =
  H.ternaryHyperformalPoint
    (meanPoint (mean s))
    (signedResidual s)
    H.origin

-- The actual original nine-slot input packet has exactly the same chart,
-- but the learned history is a separate E x 2 x width real tensor.
toNineTrits : SourceSeed →
  H.TernaryHyperformalPoint
toNineTrits = toFullFabric

sourceInteraction : SourceSeed → H.Ternary27Point
sourceInteraction s = H.projectInteractionVoxel (toFullFabric s)

sourceSigned : SourceSeed → H.Ternary27Point
sourceSigned s = H.appraisalAVoxel (toFullFabric s)

sourcePadding : SourceSeed → H.Ternary27Point
sourcePadding s = H.appraisalBVoxel (toFullFabric s)

paddingIsOrigin : (s : SourceSeed) → sourcePadding s ≡ H.origin
paddingIsOrigin s = refl

sourceMeanIsMarked : (s : SourceSeed) →
  sourceInteraction s ≡ meanPoint (mean s)
sourceMeanIsMarked s = refl

signedReopens : (s : SourceSeed) →
  sourceSigned s ≡ signedResidual s
signedReopens s = refl

-- The source mean tag remains a proof-relevant witness. Thus two-sided
-- reconstruction does not guess a Mean7 from an arbitrary nine-trit state.
reopenTagged : Mean7 → H.Ternary27Point → SourceSeed
reopenTagged = seed

taggedBidi : (s : SourceSeed) →
  reopenTagged (mean s) (sourceSigned s) ≡ s
taggedBidi (seed m d) = refl

fabricBidiOnMarkedImage : (s : SourceSeed) →
  H.rebuildOverInteraction
    (sourceInteraction s)
    (H.projectAppraisalFibre (toFullFabric s))
    ≡ toFullFabric s
fabricBidiOnMarkedImage s = refl

-- The third native appraisal can be genuinely nonzero. No map from these
-- original restricted seeds is automatically onto the full fabric.
outside : H.TernaryHyperformalPoint
outside = H.ternaryHyperformalPoint H.origin H.origin
  (H.ternary27Point T.sspPosOne T.sspZero T.sspZero)

differentZero : T.sspZero ≡ T.sspPosOne → ⊥
differentZero ()

markedImageProper : (s : SourceSeed) → toFullFabric s ≡ outside → ⊥
markedImageProper s equal =
  differentZero
    (F.cong H.x (F.cong H.appraisalBVoxel equal))

-- The finite declared seed span is 7 x 27 = 189 marked addresses,
-- strictly within 27^3 = 19683; no claim is made that all original
-- model histories are confined to 189 byte states after recurrence.
-- Original arbitrary-width trained network/hidden vector and physical
-- 9DOF world geometry are NOT the finite seed alphabet.
