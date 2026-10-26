module DASHI.Moonshine.JInvariant369BraidModularGeneratorWeldExact where

-- B3 generator comparison against native signed-SSP j-word and SL2(Z)
-- owners.  This module pays exact arithmetic, NOT a whole analytic action
-- on V^natural, framed braid isotopy, or a physical Monster gravity dual.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _*_)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as Modular
import DASHI.Moonshine.JInvariant369ModularLevelCuspObserversExact as Cusp
import DASHI.Moonshine.JInvariantOrderThreeSeamModularWordExact as Legacy
import DASHI.Moonshine.JInvariant369LevelNonDescentThroughJExact as NonDescent

record Matrix2 : Set where
  constructor mat
  field
    aa bb cc dd : ℤ
open Matrix2 public

multiply : Matrix2 → Matrix2 → Matrix2
multiply (mat a b c d) (mat e f g h) =
  mat (a * e + b * g) (a * f + b * h)
      (c * e + d * g) (c * f + d * h)

identity : Matrix2
identity = mat 1ℤ 0ℤ 0ℤ 1ℤ

upper : Matrix2
upper = mat 1ℤ 1ℤ 0ℤ 1ℤ

-- L is the *positive* lower shear of the existing SSP modular seam.
-- Artin sigma2 is its inverse U, not L itself.
legacyPositiveLower : Matrix2
legacyPositiveLower = mat 1ℤ 0ℤ 1ℤ 1ℤ

artinSecond : Matrix2
artinSecond = mat 1ℤ 0ℤ (- 1ℤ) 1ℤ

upperInverse : Matrix2
upperInverse = mat 1ℤ (- 1ℤ) 0ℤ 1ℤ

legacyPositiveLowerHasInverse :
  multiply legacyPositiveLower artinSecond ≡ identity
legacyPositiveLowerHasInverse = refl

artinSecondHasInverse :
  multiply artinSecond legacyPositiveLower ≡ identity
artinSecondHasInverse = refl

artinBraidRelation :
  multiply (multiply upper artinSecond) upper
  ≡ multiply (multiply artinSecond upper) artinSecond
artinBraidRelation = refl

-- The naively substituted two positive shears do NOT satisfy the Artin
-- relation, so the SSP signed-token interpretation needs an inverse map.
legacyTwoPositiveShearsDoNotSatisfyBraid :
  multiply (multiply upper legacyPositiveLower) upper
  ≡ multiply (multiply legacyPositiveLower upper) legacyPositiveLower
  → ⊥
legacyTwoPositiveShearsDoNotSatisfyBraid ()

legacySignedNegativeTokenIsPositiveLower :
  Legacy.signedShearAction
    Legacy.negativeShearToken Legacy.identityMatrix
  ≡ Legacy.matrix2 1 0 1 1
legacySignedNegativeTokenIsPositiveLower = refl

upperMatchesLegacySignedPositiveToken :
  Legacy.signedShearAction
    Legacy.positiveShearToken Legacy.identityMatrix
  ≡ Legacy.upperShearT
upperMatchesLegacySignedPositiveToken = refl

cube : Matrix2 → Matrix2
cube m = multiply (multiply m m) m

braidCentralFullTwist :
  cube (multiply upper artinSecond)
  ≡ mat (- 1ℤ) 0ℤ 0ℤ (- 1ℤ)
braidCentralFullTwist = refl

sixfoldCentralKernel :
  multiply (cube (multiply upper artinSecond))
           (cube (multiply upper artinSecond))
  ≡ identity
sixfoldCentralKernel = refl

recordedBraidWord : Matrix2
recordedBraidWord = cube (multiply upperInverse artinSecond)

recordedBraidExact :
  recordedBraidWord
  ≡ mat (+ 13) (- (+ 8)) (- (+ 8)) (+ 5)
recordedBraidExact = refl

recordedBraidSquare :
  multiply recordedBraidWord recordedBraidWord
  ≡ mat (+ 233) (- (+ 144)) (- (+ 144)) (+ 89)
recordedBraidSquare = refl

-- Use the existing physical/mathematical SL2Z lattice owner, not a
-- second independent matrix notion as a final analytic carrier.
fromNative : Modular.SL2Z → Matrix2
fromNative g =
  mat (Modular.a g) (Modular.b g)
      (Modular.c g) (Modular.d g)

nativeUpper : Modular.SL2Z
nativeUpper = Cusp.T

nativeArtinSecond : Modular.SL2Z
nativeArtinSecond =
  Modular.sl2z 1ℤ 0ℤ (- 1ℤ) 1ℤ refl

nativeRecordedImage : Modular.SL2Z
nativeRecordedImage =
  Modular.sl2z (+ 13) (- (+ 8)) (- (+ 8)) (+ 5) refl

nativeUpperAgrees : fromNative nativeUpper ≡ upper
nativeUpperAgrees = refl

nativeArtinSecondAgrees :
  fromNative nativeArtinSecond ≡ artinSecond
nativeArtinSecondAgrees = refl

nativeRecordedImageAgrees :
  fromNative nativeRecordedImage ≡ recordedBraidWord
nativeRecordedImageAgrees = refl

-- Do not infer any mod-3/9/27 cusp transformation from the fact that
-- the scalar modular j is invariant: NonDescent already proves that
-- the full principal-level data cannot factor through j alone.
