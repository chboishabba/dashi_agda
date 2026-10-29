module DASHI.Foundations.PolynomialS3TwentySevenOrbitBlockAssemblyExact where

-- ACTUAL 27-CODE ≃ 1 + 2 + 3 + 3 + 6 + 6 + 6 S3-SET ATLAS.
-- Extends ORIGINAL seven functional-graph shape decomposition.
-- Constructive inverse chart for ALL 27 ternary endomorphisms.
-- The rational block matrices in Small/Regular certificates now
-- attach to the native code carrier by this exact G-set map.
-- Prior sources: ordinary S3 action/representation, original DASHI
-- seven shape owner, explicit #1414 small and regular block matrices.
-- No root Galois, wild exterior, wave, RH or Ibrahim Monster3B weld.
-- SOURCE WRITTEN; AGDA KERNEL CHECK NOT PERFORMED.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import Base369 as Base
import DASHI.Cognition.RecursiveFibreTower as Tower
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Shape
import DASHI.Foundations.TernaryEndomorphismS3ActionLawsExact as ActionLaws
import DASHI.Foundations.TernaryPermutationS3LawsExact as S3
import DASHI.Foundations.PolynomialS3SmallRationalBlockCertificateExact as Small
import DASHI.Foundations.PolynomialS3RegularOrbitToNativeCodeExact as Regular

data OrbitBlock27 : Set where
  identityBlock : OrbitBlock27
  cycleBlock : Small.Pair → OrbitBlock27
  transpositionBlock : Small.Three → OrbitBlock27
  constantBlock : Small.Three → OrbitBlock27
  oneFixedBlock : Regular.Block.Six → OrbitBlock27
  twoFixedBlock : Regular.Block.Six → OrbitBlock27
  twoCycleBlock : Regular.Block.Six → OrbitBlock27

blockToCode : OrbitBlock27 → Tower.LevelTwoCode
blockToCode identityBlock = Small.nativeOneCode
blockToCode (cycleBlock i) = Small.nativeTwoCode i
blockToCode (transpositionBlock i) =
  Small.nativeThreeCode Small.transpositionFamily i
blockToCode (constantBlock i) =
  Small.nativeThreeCode Small.constantFamily i
blockToCode (oneFixedBlock i) =
  Regular.regularCode Regular.rank2OneFixed i
blockToCode (twoFixedBlock i) =
  Regular.regularCode Regular.rank2TwoFixed i
blockToCode (twoCycleBlock i) =
  Regular.regularCode Regular.rank2TwoCycle i

codeToBlock : Tower.LevelTwoCode → OrbitBlock27
codeToBlock (Base.tri-low , (Base.tri-low , Base.tri-low)) = constantBlock Small.axis0
codeToBlock (Base.tri-low , (Base.tri-low , Base.tri-mid)) = oneFixedBlock Regular.Block.slot0
codeToBlock (Base.tri-low , (Base.tri-low , Base.tri-high)) = twoFixedBlock Regular.Block.slot0
codeToBlock (Base.tri-low , (Base.tri-mid , Base.tri-low)) = twoFixedBlock Regular.Block.slot5
codeToBlock (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = twoFixedBlock Regular.Block.slot1
codeToBlock (Base.tri-low , (Base.tri-mid , Base.tri-high)) = identityBlock
codeToBlock (Base.tri-low , (Base.tri-high , Base.tri-low)) = oneFixedBlock Regular.Block.slot5
codeToBlock (Base.tri-low , (Base.tri-high , Base.tri-mid)) = transpositionBlock Small.axis0
codeToBlock (Base.tri-low , (Base.tri-high , Base.tri-high)) = twoFixedBlock Regular.Block.slot4
codeToBlock (Base.tri-mid , (Base.tri-low , Base.tri-low)) = twoCycleBlock Regular.Block.slot0
codeToBlock (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = twoCycleBlock Regular.Block.slot3
codeToBlock (Base.tri-mid , (Base.tri-low , Base.tri-high)) = transpositionBlock Small.axis2
codeToBlock (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = oneFixedBlock Regular.Block.slot3
codeToBlock (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = constantBlock Small.axis1
codeToBlock (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = twoFixedBlock Regular.Block.slot3
codeToBlock (Base.tri-mid , (Base.tri-high , Base.tri-low)) = cycleBlock Small.pair0
codeToBlock (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = twoCycleBlock Regular.Block.slot1
codeToBlock (Base.tri-mid , (Base.tri-high , Base.tri-high)) = oneFixedBlock Regular.Block.slot4
codeToBlock (Base.tri-high , (Base.tri-low , Base.tri-low)) = twoCycleBlock Regular.Block.slot5
codeToBlock (Base.tri-high , (Base.tri-low , Base.tri-mid)) = cycleBlock Small.pair1
codeToBlock (Base.tri-high , (Base.tri-low , Base.tri-high)) = oneFixedBlock Regular.Block.slot2
codeToBlock (Base.tri-high , (Base.tri-mid , Base.tri-low)) = transpositionBlock Small.axis1
codeToBlock (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = oneFixedBlock Regular.Block.slot1
codeToBlock (Base.tri-high , (Base.tri-mid , Base.tri-high)) = twoFixedBlock Regular.Block.slot2
codeToBlock (Base.tri-high , (Base.tri-high , Base.tri-low)) = twoCycleBlock Regular.Block.slot2
codeToBlock (Base.tri-high , (Base.tri-high , Base.tri-mid)) = twoCycleBlock Regular.Block.slot4
codeToBlock (Base.tri-high , (Base.tri-high , Base.tri-high)) = constantBlock Small.axis2

codeBlockRoundTrip :
  (b : OrbitBlock27) → codeToBlock (blockToCode b) ≡ b
codeBlockRoundTrip identityBlock = refl
codeBlockRoundTrip (cycleBlock Small.pair0) = refl
codeBlockRoundTrip (cycleBlock Small.pair1) = refl
codeBlockRoundTrip (transpositionBlock Small.axis0) = refl
codeBlockRoundTrip (transpositionBlock Small.axis1) = refl
codeBlockRoundTrip (transpositionBlock Small.axis2) = refl
codeBlockRoundTrip (constantBlock Small.axis0) = refl
codeBlockRoundTrip (constantBlock Small.axis1) = refl
codeBlockRoundTrip (constantBlock Small.axis2) = refl
codeBlockRoundTrip (oneFixedBlock Regular.Block.slot0) = refl
codeBlockRoundTrip (oneFixedBlock Regular.Block.slot1) = refl
codeBlockRoundTrip (oneFixedBlock Regular.Block.slot2) = refl
codeBlockRoundTrip (oneFixedBlock Regular.Block.slot3) = refl
codeBlockRoundTrip (oneFixedBlock Regular.Block.slot4) = refl
codeBlockRoundTrip (oneFixedBlock Regular.Block.slot5) = refl
codeBlockRoundTrip (twoFixedBlock Regular.Block.slot0) = refl
codeBlockRoundTrip (twoFixedBlock Regular.Block.slot1) = refl
codeBlockRoundTrip (twoFixedBlock Regular.Block.slot2) = refl
codeBlockRoundTrip (twoFixedBlock Regular.Block.slot3) = refl
codeBlockRoundTrip (twoFixedBlock Regular.Block.slot4) = refl
codeBlockRoundTrip (twoFixedBlock Regular.Block.slot5) = refl
codeBlockRoundTrip (twoCycleBlock Regular.Block.slot0) = refl
codeBlockRoundTrip (twoCycleBlock Regular.Block.slot1) = refl
codeBlockRoundTrip (twoCycleBlock Regular.Block.slot2) = refl
codeBlockRoundTrip (twoCycleBlock Regular.Block.slot3) = refl
codeBlockRoundTrip (twoCycleBlock Regular.Block.slot4) = refl
codeBlockRoundTrip (twoCycleBlock Regular.Block.slot5) = refl

blockCodeRoundTrip :
  (x : Tower.LevelTwoCode) → blockToCode (codeToBlock x) ≡ x
blockCodeRoundTrip (Base.tri-low , (Base.tri-low , Base.tri-low)) = refl
blockCodeRoundTrip (Base.tri-low , (Base.tri-low , Base.tri-mid)) = refl
blockCodeRoundTrip (Base.tri-low , (Base.tri-low , Base.tri-high)) = refl
blockCodeRoundTrip (Base.tri-low , (Base.tri-mid , Base.tri-low)) = refl
blockCodeRoundTrip (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = refl
blockCodeRoundTrip (Base.tri-low , (Base.tri-mid , Base.tri-high)) = refl
blockCodeRoundTrip (Base.tri-low , (Base.tri-high , Base.tri-low)) = refl
blockCodeRoundTrip (Base.tri-low , (Base.tri-high , Base.tri-mid)) = refl
blockCodeRoundTrip (Base.tri-low , (Base.tri-high , Base.tri-high)) = refl
blockCodeRoundTrip (Base.tri-mid , (Base.tri-low , Base.tri-low)) = refl
blockCodeRoundTrip (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = refl
blockCodeRoundTrip (Base.tri-mid , (Base.tri-low , Base.tri-high)) = refl
blockCodeRoundTrip (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = refl
blockCodeRoundTrip (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = refl
blockCodeRoundTrip (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = refl
blockCodeRoundTrip (Base.tri-mid , (Base.tri-high , Base.tri-low)) = refl
blockCodeRoundTrip (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = refl
blockCodeRoundTrip (Base.tri-mid , (Base.tri-high , Base.tri-high)) = refl
blockCodeRoundTrip (Base.tri-high , (Base.tri-low , Base.tri-low)) = refl
blockCodeRoundTrip (Base.tri-high , (Base.tri-low , Base.tri-mid)) = refl
blockCodeRoundTrip (Base.tri-high , (Base.tri-low , Base.tri-high)) = refl
blockCodeRoundTrip (Base.tri-high , (Base.tri-mid , Base.tri-low)) = refl
blockCodeRoundTrip (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = refl
blockCodeRoundTrip (Base.tri-high , (Base.tri-mid , Base.tri-high)) = refl
blockCodeRoundTrip (Base.tri-high , (Base.tri-high , Base.tri-low)) = refl
blockCodeRoundTrip (Base.tri-high , (Base.tri-high , Base.tri-mid)) = refl
blockCodeRoundTrip (Base.tri-high , (Base.tri-high , Base.tri-high)) = refl

blockAction :
  Shape.TriPermutation → OrbitBlock27 → OrbitBlock27
blockAction p b =
  codeToBlock (Shape.conjugateCode p (blockToCode b))

blockActionPreservesNative :
  (p : Shape.TriPermutation) (b : OrbitBlock27) →
  blockToCode (blockAction p b) ≡
  Shape.conjugateCode p (blockToCode b)
blockActionPreservesNative p b =
  blockCodeRoundTrip (Shape.conjugateCode p (blockToCode b))

blockActionIdentity :
  (b : OrbitBlock27) → blockAction Shape.permIdentity b ≡ b
blockActionIdentity b =
  trans
    (cong codeToBlock (ActionLaws.conjugateIdentity (blockToCode b)))
    (codeBlockRoundTrip b)

blockActionComposition :
  (p q : Shape.TriPermutation) (b : OrbitBlock27) →
  blockAction (S3._∙_ p q) b ≡ blockAction p (blockAction q b)
blockActionComposition p q b =
  trans
    (cong codeToBlock
      (ActionLaws.conjugateComposition p q (blockToCode b)))
    (cong (λ x → codeToBlock (Shape.conjugateCode p x))
      (sym (blockActionPreservesNative q b)))

-- Explicit original group actions on each individual orbit block,
-- not just a partition-count equality.
caseBlockAction : Shape.TriPermutation → OrbitBlock27 → OrbitBlock27 Shape.TriPermutation → OrbitBlock27 → OrbitBlock27
caseBlockAction p identityBlock = identityBlock
caseBlockAction p (cycleBlock i) = cycleBlock (Small.flipPair p i)
caseBlockAction p (transpositionBlock i) =
  transpositionBlock
    (Small.toThree
      (Shape.applyPermutation p (Small.fromThree i)))
caseBlockAction p (constantBlock i) =
  constantBlock
    (Small.toThree
      (Shape.applyPermutation p (Small.fromThree i)))
caseBlockAction p (oneFixedBlock i) =
  oneFixedBlock (Regular.leftMultiplyIndex p i)
caseBlockAction p (twoFixedBlock i) =
  twoFixedBlock (Regular.leftMultiplyIndex p i)
caseBlockAction p (twoCycleBlock i) =
  twoCycleBlock (Regular.leftMultiplyIndex p i)

nativeBlockActionByShape :
  (p : Shape.TriPermutation) (b : OrbitBlock27) →
  blockAction p b ≡ caseBlockAction p b
nativeBlockActionByShape Shape.permIdentity (identityBlock) = refl
nativeBlockActionByShape Shape.permIdentity (cycleBlock Small.pair0) = refl
nativeBlockActionByShape Shape.permIdentity (cycleBlock Small.pair1) = refl
nativeBlockActionByShape Shape.permIdentity (transpositionBlock Small.axis0) = refl
nativeBlockActionByShape Shape.permIdentity (transpositionBlock Small.axis1) = refl
nativeBlockActionByShape Shape.permIdentity (transpositionBlock Small.axis2) = refl
nativeBlockActionByShape Shape.permIdentity (constantBlock Small.axis0) = refl
nativeBlockActionByShape Shape.permIdentity (constantBlock Small.axis1) = refl
nativeBlockActionByShape Shape.permIdentity (constantBlock Small.axis2) = refl
nativeBlockActionByShape Shape.permIdentity (oneFixedBlock Regular.Block.slot0) = refl
nativeBlockActionByShape Shape.permIdentity (oneFixedBlock Regular.Block.slot1) = refl
nativeBlockActionByShape Shape.permIdentity (oneFixedBlock Regular.Block.slot2) = refl
nativeBlockActionByShape Shape.permIdentity (oneFixedBlock Regular.Block.slot3) = refl
nativeBlockActionByShape Shape.permIdentity (oneFixedBlock Regular.Block.slot4) = refl
nativeBlockActionByShape Shape.permIdentity (oneFixedBlock Regular.Block.slot5) = refl
nativeBlockActionByShape Shape.permIdentity (twoFixedBlock Regular.Block.slot0) = refl
nativeBlockActionByShape Shape.permIdentity (twoFixedBlock Regular.Block.slot1) = refl
nativeBlockActionByShape Shape.permIdentity (twoFixedBlock Regular.Block.slot2) = refl
nativeBlockActionByShape Shape.permIdentity (twoFixedBlock Regular.Block.slot3) = refl
nativeBlockActionByShape Shape.permIdentity (twoFixedBlock Regular.Block.slot4) = refl
nativeBlockActionByShape Shape.permIdentity (twoFixedBlock Regular.Block.slot5) = refl
nativeBlockActionByShape Shape.permIdentity (twoCycleBlock Regular.Block.slot0) = refl
nativeBlockActionByShape Shape.permIdentity (twoCycleBlock Regular.Block.slot1) = refl
nativeBlockActionByShape Shape.permIdentity (twoCycleBlock Regular.Block.slot2) = refl
nativeBlockActionByShape Shape.permIdentity (twoCycleBlock Regular.Block.slot3) = refl
nativeBlockActionByShape Shape.permIdentity (twoCycleBlock Regular.Block.slot4) = refl
nativeBlockActionByShape Shape.permIdentity (twoCycleBlock Regular.Block.slot5) = refl
nativeBlockActionByShape Shape.permRotate (identityBlock) = refl
nativeBlockActionByShape Shape.permRotate (cycleBlock Small.pair0) = refl
nativeBlockActionByShape Shape.permRotate (cycleBlock Small.pair1) = refl
nativeBlockActionByShape Shape.permRotate (transpositionBlock Small.axis0) = refl
nativeBlockActionByShape Shape.permRotate (transpositionBlock Small.axis1) = refl
nativeBlockActionByShape Shape.permRotate (transpositionBlock Small.axis2) = refl
nativeBlockActionByShape Shape.permRotate (constantBlock Small.axis0) = refl
nativeBlockActionByShape Shape.permRotate (constantBlock Small.axis1) = refl
nativeBlockActionByShape Shape.permRotate (constantBlock Small.axis2) = refl
nativeBlockActionByShape Shape.permRotate (oneFixedBlock Regular.Block.slot0) = refl
nativeBlockActionByShape Shape.permRotate (oneFixedBlock Regular.Block.slot1) = refl
nativeBlockActionByShape Shape.permRotate (oneFixedBlock Regular.Block.slot2) = refl
nativeBlockActionByShape Shape.permRotate (oneFixedBlock Regular.Block.slot3) = refl
nativeBlockActionByShape Shape.permRotate (oneFixedBlock Regular.Block.slot4) = refl
nativeBlockActionByShape Shape.permRotate (oneFixedBlock Regular.Block.slot5) = refl
nativeBlockActionByShape Shape.permRotate (twoFixedBlock Regular.Block.slot0) = refl
nativeBlockActionByShape Shape.permRotate (twoFixedBlock Regular.Block.slot1) = refl
nativeBlockActionByShape Shape.permRotate (twoFixedBlock Regular.Block.slot2) = refl
nativeBlockActionByShape Shape.permRotate (twoFixedBlock Regular.Block.slot3) = refl
nativeBlockActionByShape Shape.permRotate (twoFixedBlock Regular.Block.slot4) = refl
nativeBlockActionByShape Shape.permRotate (twoFixedBlock Regular.Block.slot5) = refl
nativeBlockActionByShape Shape.permRotate (twoCycleBlock Regular.Block.slot0) = refl
nativeBlockActionByShape Shape.permRotate (twoCycleBlock Regular.Block.slot1) = refl
nativeBlockActionByShape Shape.permRotate (twoCycleBlock Regular.Block.slot2) = refl
nativeBlockActionByShape Shape.permRotate (twoCycleBlock Regular.Block.slot3) = refl
nativeBlockActionByShape Shape.permRotate (twoCycleBlock Regular.Block.slot4) = refl
nativeBlockActionByShape Shape.permRotate (twoCycleBlock Regular.Block.slot5) = refl
nativeBlockActionByShape Shape.permRotate2 (identityBlock) = refl
nativeBlockActionByShape Shape.permRotate2 (cycleBlock Small.pair0) = refl
nativeBlockActionByShape Shape.permRotate2 (cycleBlock Small.pair1) = refl
nativeBlockActionByShape Shape.permRotate2 (transpositionBlock Small.axis0) = refl
nativeBlockActionByShape Shape.permRotate2 (transpositionBlock Small.axis1) = refl
nativeBlockActionByShape Shape.permRotate2 (transpositionBlock Small.axis2) = refl
nativeBlockActionByShape Shape.permRotate2 (constantBlock Small.axis0) = refl
nativeBlockActionByShape Shape.permRotate2 (constantBlock Small.axis1) = refl
nativeBlockActionByShape Shape.permRotate2 (constantBlock Small.axis2) = refl
nativeBlockActionByShape Shape.permRotate2 (oneFixedBlock Regular.Block.slot0) = refl
nativeBlockActionByShape Shape.permRotate2 (oneFixedBlock Regular.Block.slot1) = refl
nativeBlockActionByShape Shape.permRotate2 (oneFixedBlock Regular.Block.slot2) = refl
nativeBlockActionByShape Shape.permRotate2 (oneFixedBlock Regular.Block.slot3) = refl
nativeBlockActionByShape Shape.permRotate2 (oneFixedBlock Regular.Block.slot4) = refl
nativeBlockActionByShape Shape.permRotate2 (oneFixedBlock Regular.Block.slot5) = refl
nativeBlockActionByShape Shape.permRotate2 (twoFixedBlock Regular.Block.slot0) = refl
nativeBlockActionByShape Shape.permRotate2 (twoFixedBlock Regular.Block.slot1) = refl
nativeBlockActionByShape Shape.permRotate2 (twoFixedBlock Regular.Block.slot2) = refl
nativeBlockActionByShape Shape.permRotate2 (twoFixedBlock Regular.Block.slot3) = refl
nativeBlockActionByShape Shape.permRotate2 (twoFixedBlock Regular.Block.slot4) = refl
nativeBlockActionByShape Shape.permRotate2 (twoFixedBlock Regular.Block.slot5) = refl
nativeBlockActionByShape Shape.permRotate2 (twoCycleBlock Regular.Block.slot0) = refl
nativeBlockActionByShape Shape.permRotate2 (twoCycleBlock Regular.Block.slot1) = refl
nativeBlockActionByShape Shape.permRotate2 (twoCycleBlock Regular.Block.slot2) = refl
nativeBlockActionByShape Shape.permRotate2 (twoCycleBlock Regular.Block.slot3) = refl
nativeBlockActionByShape Shape.permRotate2 (twoCycleBlock Regular.Block.slot4) = refl
nativeBlockActionByShape Shape.permRotate2 (twoCycleBlock Regular.Block.slot5) = refl
nativeBlockActionByShape Shape.permSwapLowMid (identityBlock) = refl
nativeBlockActionByShape Shape.permSwapLowMid (cycleBlock Small.pair0) = refl
nativeBlockActionByShape Shape.permSwapLowMid (cycleBlock Small.pair1) = refl
nativeBlockActionByShape Shape.permSwapLowMid (transpositionBlock Small.axis0) = refl
nativeBlockActionByShape Shape.permSwapLowMid (transpositionBlock Small.axis1) = refl
nativeBlockActionByShape Shape.permSwapLowMid (transpositionBlock Small.axis2) = refl
nativeBlockActionByShape Shape.permSwapLowMid (constantBlock Small.axis0) = refl
nativeBlockActionByShape Shape.permSwapLowMid (constantBlock Small.axis1) = refl
nativeBlockActionByShape Shape.permSwapLowMid (constantBlock Small.axis2) = refl
nativeBlockActionByShape Shape.permSwapLowMid (oneFixedBlock Regular.Block.slot0) = refl
nativeBlockActionByShape Shape.permSwapLowMid (oneFixedBlock Regular.Block.slot1) = refl
nativeBlockActionByShape Shape.permSwapLowMid (oneFixedBlock Regular.Block.slot2) = refl
nativeBlockActionByShape Shape.permSwapLowMid (oneFixedBlock Regular.Block.slot3) = refl
nativeBlockActionByShape Shape.permSwapLowMid (oneFixedBlock Regular.Block.slot4) = refl
nativeBlockActionByShape Shape.permSwapLowMid (oneFixedBlock Regular.Block.slot5) = refl
nativeBlockActionByShape Shape.permSwapLowMid (twoFixedBlock Regular.Block.slot0) = refl
nativeBlockActionByShape Shape.permSwapLowMid (twoFixedBlock Regular.Block.slot1) = refl
nativeBlockActionByShape Shape.permSwapLowMid (twoFixedBlock Regular.Block.slot2) = refl
nativeBlockActionByShape Shape.permSwapLowMid (twoFixedBlock Regular.Block.slot3) = refl
nativeBlockActionByShape Shape.permSwapLowMid (twoFixedBlock Regular.Block.slot4) = refl
nativeBlockActionByShape Shape.permSwapLowMid (twoFixedBlock Regular.Block.slot5) = refl
nativeBlockActionByShape Shape.permSwapLowMid (twoCycleBlock Regular.Block.slot0) = refl
nativeBlockActionByShape Shape.permSwapLowMid (twoCycleBlock Regular.Block.slot1) = refl
nativeBlockActionByShape Shape.permSwapLowMid (twoCycleBlock Regular.Block.slot2) = refl
nativeBlockActionByShape Shape.permSwapLowMid (twoCycleBlock Regular.Block.slot3) = refl
nativeBlockActionByShape Shape.permSwapLowMid (twoCycleBlock Regular.Block.slot4) = refl
nativeBlockActionByShape Shape.permSwapLowMid (twoCycleBlock Regular.Block.slot5) = refl
nativeBlockActionByShape Shape.permSwapLowHigh (identityBlock) = refl
nativeBlockActionByShape Shape.permSwapLowHigh (cycleBlock Small.pair0) = refl
nativeBlockActionByShape Shape.permSwapLowHigh (cycleBlock Small.pair1) = refl
nativeBlockActionByShape Shape.permSwapLowHigh (transpositionBlock Small.axis0) = refl
nativeBlockActionByShape Shape.permSwapLowHigh (transpositionBlock Small.axis1) = refl
nativeBlockActionByShape Shape.permSwapLowHigh (transpositionBlock Small.axis2) = refl
nativeBlockActionByShape Shape.permSwapLowHigh (constantBlock Small.axis0) = refl
nativeBlockActionByShape Shape.permSwapLowHigh (constantBlock Small.axis1) = refl
nativeBlockActionByShape Shape.permSwapLowHigh (constantBlock Small.axis2) = refl
nativeBlockActionByShape Shape.permSwapLowHigh (oneFixedBlock Regular.Block.slot0) = refl
nativeBlockActionByShape Shape.permSwapLowHigh (oneFixedBlock Regular.Block.slot1) = refl
nativeBlockActionByShape Shape.permSwapLowHigh (oneFixedBlock Regular.Block.slot2) = refl
nativeBlockActionByShape Shape.permSwapLowHigh (oneFixedBlock Regular.Block.slot3) = refl
nativeBlockActionByShape Shape.permSwapLowHigh (oneFixedBlock Regular.Block.slot4) = refl
nativeBlockActionByShape Shape.permSwapLowHigh (oneFixedBlock Regular.Block.slot5) = refl
nativeBlockActionByShape Shape.permSwapLowHigh (twoFixedBlock Regular.Block.slot0) = refl
nativeBlockActionByShape Shape.permSwapLowHigh (twoFixedBlock Regular.Block.slot1) = refl
nativeBlockActionByShape Shape.permSwapLowHigh (twoFixedBlock Regular.Block.slot2) = refl
nativeBlockActionByShape Shape.permSwapLowHigh (twoFixedBlock Regular.Block.slot3) = refl
nativeBlockActionByShape Shape.permSwapLowHigh (twoFixedBlock Regular.Block.slot4) = refl
nativeBlockActionByShape Shape.permSwapLowHigh (twoFixedBlock Regular.Block.slot5) = refl
nativeBlockActionByShape Shape.permSwapLowHigh (twoCycleBlock Regular.Block.slot0) = refl
nativeBlockActionByShape Shape.permSwapLowHigh (twoCycleBlock Regular.Block.slot1) = refl
nativeBlockActionByShape Shape.permSwapLowHigh (twoCycleBlock Regular.Block.slot2) = refl
nativeBlockActionByShape Shape.permSwapLowHigh (twoCycleBlock Regular.Block.slot3) = refl
nativeBlockActionByShape Shape.permSwapLowHigh (twoCycleBlock Regular.Block.slot4) = refl
nativeBlockActionByShape Shape.permSwapLowHigh (twoCycleBlock Regular.Block.slot5) = refl
nativeBlockActionByShape Shape.permSwapMidHigh (identityBlock) = refl
nativeBlockActionByShape Shape.permSwapMidHigh (cycleBlock Small.pair0) = refl
nativeBlockActionByShape Shape.permSwapMidHigh (cycleBlock Small.pair1) = refl
nativeBlockActionByShape Shape.permSwapMidHigh (transpositionBlock Small.axis0) = refl
nativeBlockActionByShape Shape.permSwapMidHigh (transpositionBlock Small.axis1) = refl
nativeBlockActionByShape Shape.permSwapMidHigh (transpositionBlock Small.axis2) = refl
nativeBlockActionByShape Shape.permSwapMidHigh (constantBlock Small.axis0) = refl
nativeBlockActionByShape Shape.permSwapMidHigh (constantBlock Small.axis1) = refl
nativeBlockActionByShape Shape.permSwapMidHigh (constantBlock Small.axis2) = refl
nativeBlockActionByShape Shape.permSwapMidHigh (oneFixedBlock Regular.Block.slot0) = refl
nativeBlockActionByShape Shape.permSwapMidHigh (oneFixedBlock Regular.Block.slot1) = refl
nativeBlockActionByShape Shape.permSwapMidHigh (oneFixedBlock Regular.Block.slot2) = refl
nativeBlockActionByShape Shape.permSwapMidHigh (oneFixedBlock Regular.Block.slot3) = refl
nativeBlockActionByShape Shape.permSwapMidHigh (oneFixedBlock Regular.Block.slot4) = refl
nativeBlockActionByShape Shape.permSwapMidHigh (oneFixedBlock Regular.Block.slot5) = refl
nativeBlockActionByShape Shape.permSwapMidHigh (twoFixedBlock Regular.Block.slot0) = refl
nativeBlockActionByShape Shape.permSwapMidHigh (twoFixedBlock Regular.Block.slot1) = refl
nativeBlockActionByShape Shape.permSwapMidHigh (twoFixedBlock Regular.Block.slot2) = refl
nativeBlockActionByShape Shape.permSwapMidHigh (twoFixedBlock Regular.Block.slot3) = refl
nativeBlockActionByShape Shape.permSwapMidHigh (twoFixedBlock Regular.Block.slot4) = refl
nativeBlockActionByShape Shape.permSwapMidHigh (twoFixedBlock Regular.Block.slot5) = refl
nativeBlockActionByShape Shape.permSwapMidHigh (twoCycleBlock Regular.Block.slot0) = refl
nativeBlockActionByShape Shape.permSwapMidHigh (twoCycleBlock Regular.Block.slot1) = refl
nativeBlockActionByShape Shape.permSwapMidHigh (twoCycleBlock Regular.Block.slot2) = refl
nativeBlockActionByShape Shape.permSwapMidHigh (twoCycleBlock Regular.Block.slot3) = refl
nativeBlockActionByShape Shape.permSwapMidHigh (twoCycleBlock Regular.Block.slot4) = refl
nativeBlockActionByShape Shape.permSwapMidHigh (twoCycleBlock Regular.Block.slot5) = refl

-- This actual source group-set isomorphism induces a pointwise
-- equivalence on fields over ANY carrier A, including rational
-- representation fields. No funext postulate.
toBlockField : ∀ {A : Set} →
  (Tower.LevelTwoCode → A) → OrbitBlock27 → A
toBlockField f b = f (blockToCode b)

fromBlockField : ∀ {A : Set} →
  (OrbitBlock27 → A) → Tower.LevelTwoCode → A
fromBlockField f x = f (codeToBlock x)

fromToBlockField :
  ∀ {A : Set} (f : Tower.LevelTwoCode → A)
  (x : Tower.LevelTwoCode) →
  fromBlockField (toBlockField f) x ≡ f x
fromToBlockField f x =
  cong f (blockCodeRoundTrip x)

toFromBlockField :
  ∀ {A : Set} (f : OrbitBlock27 → A)
  (b : OrbitBlock27) →
  toBlockField (fromBlockField f) b ≡ f b
toFromBlockField f b =
  cong f (codeBlockRoundTrip b)

-- The mathematical O40 remaining part is to assemble the
-- small & regular rational matrices into a kernel-checked
-- additive/linear Q-field block isomorphism. It is not implied
-- by a number match or the existence of this G-set chart.
