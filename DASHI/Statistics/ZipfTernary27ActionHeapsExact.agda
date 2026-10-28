module DASHI.Statistics.ZipfTernary27ActionHeapsExact where

------------------------------------------------------------------------
-- 2026-10-28: 27-cell / S3-C3 / full-Heaps observation bridge.
-- Reuse exact original 27 source owners. NO second ternary or S3 carrier.
--
-- SOURCE OWNERS:
-- DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact
-- DASHI.Foundations.SSPTritCarrier
-- DASHI.Cognition.RecursiveFibreTower
-- DASHI.Foundations.TernaryEndomorphismConjugacyExact
-- DASHI.Statistics.ZipfFullHeapsCurveIdentityNoGoExact
--
-- Six value relabelings preserve every full-Heaps curve on all 27 codes.
-- Coordinate reorientation does NOT preserve full-Heaps chronology.
-- These are different actions. Code-as-word is an explicit INTERPRETATION,
-- not an equation between physical trialectic semantics and natural text.
--
-- Classical Cauchy/Frobenius/Burnside and Polya orbit counting, with
-- previously repo-owned 3^3 and seven functional-graph conjugacy shapes.
-- Johl Brown-directed, OpenAI ChatGPT-assisted source adapter.
-- SOURCE-WRITTEN; AGDA KERNEL COMPILATION NOT EXECUTED.
-- No Monster 3B, quaternion 720, RH or NS same-object identification.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import Base369 as Base
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Cognition.RecursiveFibreTower as Tower
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Perm
import DASHI.Statistics.ZipfFullHeapsCurveIdentityNoGoExact as Hist

-- The standard cube and endomorphism table are separate ORIGINAL carriers.
sspToTri : SSP.SSPTrit → Base.TriTruth
sspToTri SSP.sspNegOne = Base.tri-low
sspToTri SSP.sspZero = Base.tri-mid
sspToTri SSP.sspPosOne = Base.tri-high

triToSSP : Base.TriTruth → SSP.SSPTrit
triToSSP Base.tri-low = SSP.sspNegOne
triToSSP Base.tri-mid = SSP.sspZero
triToSSP Base.tri-high = SSP.sspPosOne

cubeToCode : Fabric.Ternary27Point → Tower.LevelTwoCode
cubeToCode (Fabric.ternary27Point x y z) =
  sspToTri x , (sspToTri y , sspToTri z)

codeToCube : Tower.LevelTwoCode → Fabric.Ternary27Point
codeToCube (x , (y , z)) =
  Fabric.ternary27Point (triToSSP x) (triToSSP y) (triToSSP z)

cubeCodeRoundTrip : (p : Fabric.Ternary27Point) →
  codeToCube (cubeToCode p) ≡ p
cubeCodeRoundTrip (Fabric.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne) = refl
cubeCodeRoundTrip (Fabric.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspZero) = refl
cubeCodeRoundTrip (Fabric.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne) = refl
cubeCodeRoundTrip (Fabric.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspNegOne) = refl
cubeCodeRoundTrip (Fabric.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspZero) = refl
cubeCodeRoundTrip (Fabric.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspPosOne) = refl
cubeCodeRoundTrip (Fabric.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne) = refl
cubeCodeRoundTrip (Fabric.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspZero) = refl
cubeCodeRoundTrip (Fabric.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne) = refl
cubeCodeRoundTrip (Fabric.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspNegOne) = refl
cubeCodeRoundTrip (Fabric.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspZero) = refl
cubeCodeRoundTrip (Fabric.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspPosOne) = refl
cubeCodeRoundTrip (Fabric.ternary27Point SSP.sspZero SSP.sspZero SSP.sspNegOne) = refl
cubeCodeRoundTrip (Fabric.ternary27Point SSP.sspZero SSP.sspZero SSP.sspZero) = refl
cubeCodeRoundTrip (Fabric.ternary27Point SSP.sspZero SSP.sspZero SSP.sspPosOne) = refl
cubeCodeRoundTrip (Fabric.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspNegOne) = refl
cubeCodeRoundTrip (Fabric.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspZero) = refl
cubeCodeRoundTrip (Fabric.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspPosOne) = refl
cubeCodeRoundTrip (Fabric.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne) = refl
cubeCodeRoundTrip (Fabric.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspZero) = refl
cubeCodeRoundTrip (Fabric.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne) = refl
cubeCodeRoundTrip (Fabric.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspNegOne) = refl
cubeCodeRoundTrip (Fabric.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero) = refl
cubeCodeRoundTrip (Fabric.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspPosOne) = refl
cubeCodeRoundTrip (Fabric.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne) = refl
cubeCodeRoundTrip (Fabric.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspZero) = refl
cubeCodeRoundTrip (Fabric.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne) = refl

codeCubeRoundTrip : (p : Tower.LevelTwoCode) →
  cubeToCode (codeToCube p) ≡ p
codeCubeRoundTrip (Base.tri-low , (Base.tri-low , Base.tri-low)) = refl
codeCubeRoundTrip (Base.tri-low , (Base.tri-low , Base.tri-mid)) = refl
codeCubeRoundTrip (Base.tri-low , (Base.tri-low , Base.tri-high)) = refl
codeCubeRoundTrip (Base.tri-low , (Base.tri-mid , Base.tri-low)) = refl
codeCubeRoundTrip (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = refl
codeCubeRoundTrip (Base.tri-low , (Base.tri-mid , Base.tri-high)) = refl
codeCubeRoundTrip (Base.tri-low , (Base.tri-high , Base.tri-low)) = refl
codeCubeRoundTrip (Base.tri-low , (Base.tri-high , Base.tri-mid)) = refl
codeCubeRoundTrip (Base.tri-low , (Base.tri-high , Base.tri-high)) = refl
codeCubeRoundTrip (Base.tri-mid , (Base.tri-low , Base.tri-low)) = refl
codeCubeRoundTrip (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = refl
codeCubeRoundTrip (Base.tri-mid , (Base.tri-low , Base.tri-high)) = refl
codeCubeRoundTrip (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = refl
codeCubeRoundTrip (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = refl
codeCubeRoundTrip (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = refl
codeCubeRoundTrip (Base.tri-mid , (Base.tri-high , Base.tri-low)) = refl
codeCubeRoundTrip (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = refl
codeCubeRoundTrip (Base.tri-mid , (Base.tri-high , Base.tri-high)) = refl
codeCubeRoundTrip (Base.tri-high , (Base.tri-low , Base.tri-low)) = refl
codeCubeRoundTrip (Base.tri-high , (Base.tri-low , Base.tri-mid)) = refl
codeCubeRoundTrip (Base.tri-high , (Base.tri-low , Base.tri-high)) = refl
codeCubeRoundTrip (Base.tri-high , (Base.tri-mid , Base.tri-low)) = refl
codeCubeRoundTrip (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = refl
codeCubeRoundTrip (Base.tri-high , (Base.tri-mid , Base.tri-high)) = refl
codeCubeRoundTrip (Base.tri-high , (Base.tri-high , Base.tri-low)) = refl
codeCubeRoundTrip (Base.tri-high , (Base.tri-high , Base.tri-mid)) = refl
codeCubeRoundTrip (Base.tri-high , (Base.tri-high , Base.tri-high)) = refl

triToLetter : Base.TriTruth → Hist.Letter
triToLetter Base.tri-low = Hist.A
triToLetter Base.tri-mid = Hist.B
triToLetter Base.tri-high = Hist.C

codeAsWord : Tower.LevelTwoCode → List Hist.Letter
codeAsWord (x , (y , z)) =
  triToLetter x ∷ triToLetter y ∷ triToLetter z ∷ []

codeHeaps : Tower.LevelTwoCode → List Nat
codeHeaps p = Hist.fullHeapsCurve (codeAsWord p)

-- IMPORTANT: source-owned Perm.applyPermutation is a permutation of
-- VALUE LABELS. Do not silently confuse with an axis position action.
valueRelabelCode : Perm.TriPermutation →
                   Tower.LevelTwoCode → Tower.LevelTwoCode
valueRelabelCode action (x , (y , z)) =
  Perm.applyPermutation action x ,
  (Perm.applyPermutation action y , Perm.applyPermutation action z)

all27CodesHeapsInvariantUnderValueRelabeling :
  (action : Perm.TriPermutation) (code : Tower.LevelTwoCode) →
  codeHeaps (valueRelabelCode action code) ≡ codeHeaps code
all27CodesHeapsInvariantUnderValueRelabeling Perm.permIdentity (Base.tri-low , (Base.tri-low , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permIdentity (Base.tri-low , (Base.tri-low , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permIdentity (Base.tri-low , (Base.tri-low , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permIdentity (Base.tri-low , (Base.tri-mid , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permIdentity (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permIdentity (Base.tri-low , (Base.tri-mid , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permIdentity (Base.tri-low , (Base.tri-high , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permIdentity (Base.tri-low , (Base.tri-high , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permIdentity (Base.tri-low , (Base.tri-high , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permIdentity (Base.tri-mid , (Base.tri-low , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permIdentity (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permIdentity (Base.tri-mid , (Base.tri-low , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permIdentity (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permIdentity (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permIdentity (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permIdentity (Base.tri-mid , (Base.tri-high , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permIdentity (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permIdentity (Base.tri-mid , (Base.tri-high , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permIdentity (Base.tri-high , (Base.tri-low , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permIdentity (Base.tri-high , (Base.tri-low , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permIdentity (Base.tri-high , (Base.tri-low , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permIdentity (Base.tri-high , (Base.tri-mid , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permIdentity (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permIdentity (Base.tri-high , (Base.tri-mid , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permIdentity (Base.tri-high , (Base.tri-high , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permIdentity (Base.tri-high , (Base.tri-high , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permIdentity (Base.tri-high , (Base.tri-high , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate (Base.tri-low , (Base.tri-low , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate (Base.tri-low , (Base.tri-low , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate (Base.tri-low , (Base.tri-low , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate (Base.tri-low , (Base.tri-mid , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate (Base.tri-low , (Base.tri-mid , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate (Base.tri-low , (Base.tri-high , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate (Base.tri-low , (Base.tri-high , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate (Base.tri-low , (Base.tri-high , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate (Base.tri-mid , (Base.tri-low , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate (Base.tri-mid , (Base.tri-low , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate (Base.tri-mid , (Base.tri-high , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate (Base.tri-mid , (Base.tri-high , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate (Base.tri-high , (Base.tri-low , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate (Base.tri-high , (Base.tri-low , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate (Base.tri-high , (Base.tri-low , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate (Base.tri-high , (Base.tri-mid , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate (Base.tri-high , (Base.tri-mid , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate (Base.tri-high , (Base.tri-high , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate (Base.tri-high , (Base.tri-high , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate (Base.tri-high , (Base.tri-high , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate2 (Base.tri-low , (Base.tri-low , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate2 (Base.tri-low , (Base.tri-low , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate2 (Base.tri-low , (Base.tri-low , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate2 (Base.tri-low , (Base.tri-mid , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate2 (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate2 (Base.tri-low , (Base.tri-mid , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate2 (Base.tri-low , (Base.tri-high , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate2 (Base.tri-low , (Base.tri-high , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate2 (Base.tri-low , (Base.tri-high , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate2 (Base.tri-mid , (Base.tri-low , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate2 (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate2 (Base.tri-mid , (Base.tri-low , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate2 (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate2 (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate2 (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate2 (Base.tri-mid , (Base.tri-high , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate2 (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate2 (Base.tri-mid , (Base.tri-high , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate2 (Base.tri-high , (Base.tri-low , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate2 (Base.tri-high , (Base.tri-low , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate2 (Base.tri-high , (Base.tri-low , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate2 (Base.tri-high , (Base.tri-mid , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate2 (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate2 (Base.tri-high , (Base.tri-mid , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate2 (Base.tri-high , (Base.tri-high , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate2 (Base.tri-high , (Base.tri-high , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permRotate2 (Base.tri-high , (Base.tri-high , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowMid (Base.tri-low , (Base.tri-low , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowMid (Base.tri-low , (Base.tri-low , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowMid (Base.tri-low , (Base.tri-low , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowMid (Base.tri-low , (Base.tri-mid , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowMid (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowMid (Base.tri-low , (Base.tri-mid , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowMid (Base.tri-low , (Base.tri-high , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowMid (Base.tri-low , (Base.tri-high , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowMid (Base.tri-low , (Base.tri-high , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowMid (Base.tri-mid , (Base.tri-low , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowMid (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowMid (Base.tri-mid , (Base.tri-low , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowMid (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowMid (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowMid (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowMid (Base.tri-mid , (Base.tri-high , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowMid (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowMid (Base.tri-mid , (Base.tri-high , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowMid (Base.tri-high , (Base.tri-low , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowMid (Base.tri-high , (Base.tri-low , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowMid (Base.tri-high , (Base.tri-low , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowMid (Base.tri-high , (Base.tri-mid , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowMid (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowMid (Base.tri-high , (Base.tri-mid , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowMid (Base.tri-high , (Base.tri-high , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowMid (Base.tri-high , (Base.tri-high , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowMid (Base.tri-high , (Base.tri-high , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowHigh (Base.tri-low , (Base.tri-low , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowHigh (Base.tri-low , (Base.tri-low , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowHigh (Base.tri-low , (Base.tri-low , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowHigh (Base.tri-low , (Base.tri-mid , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowHigh (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowHigh (Base.tri-low , (Base.tri-mid , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowHigh (Base.tri-low , (Base.tri-high , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowHigh (Base.tri-low , (Base.tri-high , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowHigh (Base.tri-low , (Base.tri-high , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowHigh (Base.tri-mid , (Base.tri-low , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowHigh (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowHigh (Base.tri-mid , (Base.tri-low , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowHigh (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowHigh (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowHigh (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowHigh (Base.tri-mid , (Base.tri-high , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowHigh (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowHigh (Base.tri-mid , (Base.tri-high , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowHigh (Base.tri-high , (Base.tri-low , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowHigh (Base.tri-high , (Base.tri-low , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowHigh (Base.tri-high , (Base.tri-low , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowHigh (Base.tri-high , (Base.tri-mid , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowHigh (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowHigh (Base.tri-high , (Base.tri-mid , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowHigh (Base.tri-high , (Base.tri-high , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowHigh (Base.tri-high , (Base.tri-high , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapLowHigh (Base.tri-high , (Base.tri-high , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapMidHigh (Base.tri-low , (Base.tri-low , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapMidHigh (Base.tri-low , (Base.tri-low , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapMidHigh (Base.tri-low , (Base.tri-low , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapMidHigh (Base.tri-low , (Base.tri-mid , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapMidHigh (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapMidHigh (Base.tri-low , (Base.tri-mid , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapMidHigh (Base.tri-low , (Base.tri-high , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapMidHigh (Base.tri-low , (Base.tri-high , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapMidHigh (Base.tri-low , (Base.tri-high , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapMidHigh (Base.tri-mid , (Base.tri-low , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapMidHigh (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapMidHigh (Base.tri-mid , (Base.tri-low , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapMidHigh (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapMidHigh (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapMidHigh (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapMidHigh (Base.tri-mid , (Base.tri-high , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapMidHigh (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapMidHigh (Base.tri-mid , (Base.tri-high , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapMidHigh (Base.tri-high , (Base.tri-low , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapMidHigh (Base.tri-high , (Base.tri-low , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapMidHigh (Base.tri-high , (Base.tri-low , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapMidHigh (Base.tri-high , (Base.tri-mid , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapMidHigh (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapMidHigh (Base.tri-high , (Base.tri-mid , Base.tri-high)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapMidHigh (Base.tri-high , (Base.tri-high , Base.tri-low)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapMidHigh (Base.tri-high , (Base.tri-high , Base.tri-mid)) = refl
all27CodesHeapsInvariantUnderValueRelabeling Perm.permSwapMidHigh (Base.tri-high , (Base.tri-high , Base.tri-high)) = refl

-- Distinct POSITION reorientations for the SAME code carrier.
swapYZ : Tower.LevelTwoCode → Tower.LevelTwoCode
swapYZ (x , (y , z)) = x , (z , y)

rotateXYZ : Tower.LevelTwoCode → Tower.LevelTwoCode
rotateXYZ (x , (y , z)) = y , (z , x)

swapYZInvolution : (code : Tower.LevelTwoCode) →
  swapYZ (swapYZ code) ≡ code
swapYZInvolution (x , (y , z)) = refl

rotateXYZHasOrderThree : (code : Tower.LevelTwoCode) →
  rotateXYZ (rotateXYZ (rotateXYZ code)) ≡ code
rotateXYZHasOrderThree (x , (y , z)) = refl

aab : Tower.LevelTwoCode
aab = Base.tri-low , (Base.tri-low , Base.tri-mid)

aabFullCurve :
  codeHeaps aab ≡
  (zero ∷ suc zero ∷ suc zero ∷ suc (suc zero) ∷ [])
aabFullCurve = refl

abaFullCurve :
  codeHeaps (swapYZ aab) ≡
  (zero ∷ suc zero ∷ suc (suc zero) ∷ suc (suc zero) ∷ [])
abaFullCurve = refl

-- Source-backed explicit negative result: two equal coordinates swap
-- temporal first-discovery order. No universal coordinate invariance.
coordinateSwapDoesNotPreserveAllHeaps :
  ((code : Tower.LevelTwoCode) →
    codeHeaps (swapYZ code) ≡ codeHeaps code) → Hist.⊥
coordinateSwapDoesNotPreserveAllHeaps assumption
  with assumption aab
... | ()

-- The repo's existing S3 conjugation action on endomorphism codes
-- HAS SEVEN functional-graph orbits. It is not value relabeling alone,
-- nor coordinate swapping alone, nor the full Heaps quotient.
existingConjugacyHasSevenOrbits :
  Perm.listCount Perm.allShapeOrbits ≡ 7
existingConjugacyHasSevenOrbits = Perm.shapeOrbitCountIsSeven

existingConjugacySizesSum27 :
  Perm.shapeOrbitSize Perm.identityShape
  + Perm.shapeOrbitSize Perm.threeCycleShape
  + Perm.shapeOrbitSize Perm.transpositionShape
  + Perm.shapeOrbitSize Perm.constantShape
  + Perm.shapeOrbitSize Perm.rank2OneFixedShape
  + Perm.shapeOrbitSize Perm.rank2TwoFixedShape
  + Perm.shapeOrbitSize Perm.rank2TwoCycleShape ≡ 27
existingConjugacySizesSum27 = Perm.shapeOrbitSizesSumToTwentySeven

existingCubeHas27Points : Fabric.hypervoxelStateCount ≡ 27
existingCubeHas27Points = Fabric.hypervoxelStateCountIs27
