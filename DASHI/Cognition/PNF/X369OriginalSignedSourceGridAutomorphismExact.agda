module DASHI.Cognition.PNF.X369OriginalSignedSourceGridAutomorphismExact where

-- THE ORIGINAL X369 GROUP IS SIGNED COORDINATE S3 ON M3, D3;
-- residual D3 receives the mirror-odd character. This differs
-- fundamentally from S3 permutation of the TRIT PALETTE, which the
-- existing Dialectic27S3PresentationVsGridAutomorphismExact proves
-- is NOT always a nonwrapping P3 grid automorphism.
--
-- The third original input triad is zero padding. Extending the
-- coordinate action to its full 27-point block is an EXPLICIT CHOSEN
-- hyperfabric extension, not the source learned transition.
-- Original Leech-LILA: Anatolii Kornienko; DASHI formal bridge.
-- Agda kernel deferred.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as H
import DASHI.Reasoning.Dialectic27S3PresentationVsGridAutomorphismExact as Grid
import DASHI.Cognition.PNF.X369OriginalMarkedSeedHypervoxelSourceExact as Source

rotate3 : H.Ternary27Point → H.Ternary27Point
rotate3 (H.ternary27Point x y z) = H.ternary27Point y z x

mirror3 : H.Ternary27Point → H.Ternary27Point
mirror3 (H.ternary27Point x y z) = H.ternary27Point z y x

negative3 : H.Ternary27Point → H.Ternary27Point
negative3 = Grid.reflectCube

rotate3OrderThree : (p : H.Ternary27Point) →
  rotate3 (rotate3 (rotate3 p)) ≡ p
rotate3OrderThree (H.ternary27Point x y z) = refl

mirror3OrderTwo : (p : H.Ternary27Point) →
  mirror3 (mirror3 p) ≡ p
mirror3OrderTwo (H.ternary27Point x y z) = refl

negative3OrderTwo : (p : H.Ternary27Point) →
  negative3 (negative3 p) ≡ p
negative3OrderTwo = Grid.reflectCubeInvolution

-- ORIGINAL strict nonwrapping -1↔0↔+1 adjacency is genuinely
-- preserved by coordinate permutations and endpoint sign reversal.
rotate3Preserves :
  ∀ {a b} → H.HypervoxelAdjacent a b →
  H.HypervoxelAdjacent (rotate3 a) (rotate3 b)
rotate3Preserves (H.adjacentX edge) = H.adjacentZ edge
rotate3Preserves (H.adjacentY edge) = H.adjacentX edge
rotate3Preserves (H.adjacentZ edge) = H.adjacentY edge

mirror3Preserves :
  ∀ {a b} → H.HypervoxelAdjacent a b →
  H.HypervoxelAdjacent (mirror3 a) (mirror3 b)
mirror3Preserves (H.adjacentX edge) = H.adjacentZ edge
mirror3Preserves (H.adjacentY edge) = H.adjacentY edge
mirror3Preserves (H.adjacentZ edge) = H.adjacentX edge

negative3Preserves :
  ∀ {a b} → H.HypervoxelAdjacent a b →
  H.HypervoxelAdjacent (negative3 a) (negative3 b)
negative3Preserves = Grid.reflectCubePreservesGrid

-- Explicit triple-block coordinates: original source (M3,D3,0)
-- and independently CHOSEN action on arbitrary third-block trits.
rotate9 : H.TernaryHyperformalPoint → H.TernaryHyperformalPoint
rotate9 (H.ternaryHyperformalPoint m d pad) =
  H.ternaryHyperformalPoint (rotate3 m) (rotate3 d) (rotate3 pad)

mirror9 : H.TernaryHyperformalPoint → H.TernaryHyperformalPoint
mirror9 (H.ternaryHyperformalPoint m d pad) =
  H.ternaryHyperformalPoint
    (mirror3 m) (negative3 (mirror3 d)) (mirror3 pad)

negative9 : H.TernaryHyperformalPoint → H.TernaryHyperformalPoint
negative9 (H.ternaryHyperformalPoint m d pad) =
  H.ternaryHyperformalPoint
    (negative3 m) (negative3 d) (negative3 pad)

rotate9PreservesGrid :
  ∀ {a b} → H.HyperformalAdjacent a b →
  H.HyperformalAdjacent (rotate9 a) (rotate9 b)
rotate9PreservesGrid (H.interactionAdjacent step) =
  H.interactionAdjacent (rotate3Preserves step)
rotate9PreservesGrid (H.appraisalAAdjacent step) =
  H.appraisalAAdjacent (rotate3Preserves step)
rotate9PreservesGrid (H.appraisalBAdjacent step) =
  H.appraisalBAdjacent (rotate3Preserves step)

mirror9PreservesGrid :
  ∀ {a b} → H.HyperformalAdjacent a b →
  H.HyperformalAdjacent (mirror9 a) (mirror9 b)
mirror9PreservesGrid (H.interactionAdjacent step) =
  H.interactionAdjacent (mirror3Preserves step)
mirror9PreservesGrid (H.appraisalAAdjacent step) =
  H.appraisalAAdjacent
    (negative3Preserves (mirror3Preserves step))
mirror9PreservesGrid (H.appraisalBAdjacent step) =
  H.appraisalBAdjacent (mirror3Preserves step)

negative9PreservesGrid :
  ∀ {a b} → H.HyperformalAdjacent a b →
  H.HyperformalAdjacent (negative9 a) (negative9 b)
negative9PreservesGrid (H.interactionAdjacent step) =
  H.interactionAdjacent (negative3Preserves step)
negative9PreservesGrid (H.appraisalAAdjacent step) =
  H.appraisalAAdjacent (negative3Preserves step)
negative9PreservesGrid (H.appraisalBAdjacent step) =
  H.appraisalBAdjacent (negative3Preserves step)

data SourceGenerator : Set where
  sourceRotate sourceMirror sourceNegative : SourceGenerator

applyGenerator :
  SourceGenerator → H.TernaryHyperformalPoint → H.TernaryHyperformalPoint
applyGenerator sourceRotate = rotate9
applyGenerator sourceMirror = mirror9
applyGenerator sourceNegative = negative9

generatorPreservesGrid :
  (g : SourceGenerator) {a b : H.TernaryHyperformalPoint} →
  H.HyperformalAdjacent a b →
  H.HyperformalAdjacent (applyGenerator g a) (applyGenerator g b)
generatorPreservesGrid sourceRotate step = rotate9PreservesGrid step
generatorPreservesGrid sourceMirror step = mirror9PreservesGrid step
generatorPreservesGrid sourceNegative step = negative9PreservesGrid step

applyWord : List SourceGenerator →
  H.TernaryHyperformalPoint → H.TernaryHyperformalPoint
applyWord [] s = s
applyWord (g ∷ gs) s = applyWord gs (applyGenerator g s)

-- ALL finite original source generator words are actual graph maps
-- of the FULL 19683-point original nonwrapping 369 hyperfabric chart.
allWordsPreserveNativeGrid :
  (word : List SourceGenerator) {a b : H.TernaryHyperformalPoint} →
  H.HyperformalAdjacent a b →
  H.HyperformalAdjacent (applyWord word a) (applyWord word b)
allWordsPreserveNativeGrid [] step = step
allWordsPreserveNativeGrid (g ∷ gs) step =
  allWordsPreserveNativeGrid gs (generatorPreservesGrid g step)

-- The known initial source 189-state MARKED SUBCARRIER is closed under
-- the same three generators, including the mirror-odd signed residual.
rotateMean : Source.SourceMean7 → Source.SourceMean7
rotateMean Source.zeroMean = Source.zeroMean
rotateMean Source.negX = Source.negZ
rotateMean Source.posX = Source.posZ
rotateMean Source.negY = Source.negX
rotateMean Source.posY = Source.posX
rotateMean Source.negZ = Source.negY
rotateMean Source.posZ = Source.posY

mirrorMean : Source.SourceMean7 → Source.SourceMean7
mirrorMean Source.zeroMean = Source.zeroMean
mirrorMean Source.negX = Source.negZ
mirrorMean Source.posX = Source.posZ
mirrorMean Source.negY = Source.negY
mirrorMean Source.posY = Source.posY
mirrorMean Source.negZ = Source.negX
mirrorMean Source.posZ = Source.posX

negativeMean : Source.SourceMean7 → Source.SourceMean7
negativeMean Source.zeroMean = Source.zeroMean
negativeMean Source.negX = Source.posX
negativeMean Source.posX = Source.negX
negativeMean Source.negY = Source.posY
negativeMean Source.posY = Source.negY
negativeMean Source.negZ = Source.posZ
negativeMean Source.posZ = Source.negZ

rotateMeanCorrect : (m : Source.SourceMean7) →
  Source.meanVoxel (rotateMean m) ≡ rotate3 (Source.meanVoxel m)
rotateMeanCorrect Source.zeroMean = refl
rotateMeanCorrect Source.negX = refl
rotateMeanCorrect Source.posX = refl
rotateMeanCorrect Source.negY = refl
rotateMeanCorrect Source.posY = refl
rotateMeanCorrect Source.negZ = refl
rotateMeanCorrect Source.posZ = refl

mirrorMeanCorrect : (m : Source.SourceMean7) →
  Source.meanVoxel (mirrorMean m) ≡ mirror3 (Source.meanVoxel m)
mirrorMeanCorrect Source.zeroMean = refl
mirrorMeanCorrect Source.negX = refl
mirrorMeanCorrect Source.posX = refl
mirrorMeanCorrect Source.negY = refl
mirrorMeanCorrect Source.posY = refl
mirrorMeanCorrect Source.negZ = refl
mirrorMeanCorrect Source.posZ = refl

negativeMeanCorrect : (m : Source.SourceMean7) →
  Source.meanVoxel (negativeMean m) ≡ negative3 (Source.meanVoxel m)
negativeMeanCorrect Source.zeroMean = refl
negativeMeanCorrect Source.negX = refl
negativeMeanCorrect Source.posX = refl
negativeMeanCorrect Source.negY = refl
negativeMeanCorrect Source.posY = refl
negativeMeanCorrect Source.negZ = refl
negativeMeanCorrect Source.posZ = refl

rotateSeed : Source.SourceMarkedSeed → Source.SourceMarkedSeed
rotateSeed (Source.sourceMarkedSeed m d) =
  Source.sourceMarkedSeed (rotateMean m) (rotate3 d)

mirrorSeed : Source.SourceMarkedSeed → Source.SourceMarkedSeed
mirrorSeed (Source.sourceMarkedSeed m d) =
  Source.sourceMarkedSeed (mirrorMean m) (negative3 (mirror3 d))

negativeSeed : Source.SourceMarkedSeed → Source.SourceMarkedSeed
negativeSeed (Source.sourceMarkedSeed m d) =
  Source.sourceMarkedSeed (negativeMean m) (negative3 d)

rotateMarkedSourceClosed : (s : Source.SourceMarkedSeed) →
  rotate9 (Source.markedFabric s) ≡ Source.markedFabric (rotateSeed s)
rotateMarkedSourceClosed (Source.sourceMarkedSeed m d)
  rewrite rotateMeanCorrect m = refl

mirrorMarkedSourceClosed : (s : Source.SourceMarkedSeed) →
  mirror9 (Source.markedFabric s) ≡ Source.markedFabric (mirrorSeed s)
mirrorMarkedSourceClosed (Source.sourceMarkedSeed m d)
  rewrite mirrorMeanCorrect m = refl

negativeMarkedSourceClosed : (s : Source.SourceMarkedSeed) →
  negative9 (Source.markedFabric s) ≡ Source.markedFabric (negativeSeed s)
negativeMarkedSourceClosed (Source.sourceMarkedSeed m d)
  rewrite negativeMeanCorrect m = refl

-- This actual finite grid symmetry does not assert that ANY learned
-- recurrent MoE step commutes with it. Physical metrics, Leech lattice
-- action and original semantic pants boundary remain separately typed.
