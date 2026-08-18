module DASHI.Moonshine.P37MarkedDeckIsotypicHighestAlphaRegression where

open import DASHI.Core.Prelude

import DASHI.Moonshine.P37MarkedDeckIsotypicJointDecompositionExact as Iso
import DASHI.Moonshine.P37MarkedDeckIsotypicCollisionExact as Collision
import DASHI.Moonshine.P11MarkedX2S3HeckeDecompositionExact as P11
import DASHI.Moonshine.P11P37MarkedDeckSelectorCutsetExact as Cutset
import DASHI.Moonshine.BrandtHeckeFrobeniusFrickeSelectorWeldExact as Selector
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix

------------------------------------------------------------------------
-- Complete p=37 deck dimensions.
------------------------------------------------------------------------

p37DeckDimensions :
  Iso.trivialDeckDimension + Iso.signDeckDimension + Iso.standardDeckIsotypicDimension
  ≡ 18
p37DeckDimensions = Iso.isotypicDimensionsSumToEighteen

p37StandardIsotypicMultiplicityShape :
  2 * Iso.standardMultiplicityDimension ≡ Iso.standardDeckIsotypicDimension
p37StandardIsotypicMultiplicityShape = Iso.standardIsotypicIsTwoMultiplicityCopies

------------------------------------------------------------------------
-- Structural explanation of the p=37 scalar-fingerprint collision.
------------------------------------------------------------------------

p37TrivialT3One :
  Iso.trivialT3 Collision.p37TrivialCollisionVector
  ≡ Collision.p37TrivialCollisionVector
p37TrivialT3One = Collision.p37TrivialT3EigenOne

p37StandardT3One :
  Iso.standardT3 Collision.p37StandardCollisionVector
  ≡ Collision.p37StandardCollisionVector
p37StandardT3One = Collision.p37StandardT3EigenOne

p37ScalarCollision :
  Collision.p37TrivialFingerprint ≡ Collision.p37StandardFingerprint
p37ScalarCollision = Collision.p37ArithmeticFingerprintsCoincide

p37DeckRepairsCollision :
  Collision.p37TrivialRefined ≡ Collision.p37StandardRefined → ⊥
p37DeckRepairsCollision = Collision.p37DeckRefinementSeparates

------------------------------------------------------------------------
-- Cross-prime information-loss pattern and surviving selector coordinate.
------------------------------------------------------------------------

p11CollisionStillExists :
  P11.brandtNewformFingerprint ≡ P11.standardFingerprint
p11CollisionStillExists = Collision.p11ArithmeticCollisionStillExact

p11FrobeniusDefectZero :
  Selector.frobeniusPairDefect Matrix.prime11 ≡ 0
p11FrobeniusDefectZero = Cutset.p11DefectZero

p37FrobeniusDefectOne :
  Selector.frobeniusPairDefect Matrix.prime37 ≡ 1
p37FrobeniusDefectOne = Cutset.p37DefectOne

p11P37DefectsDiffer :
  Selector.frobeniusPairDefect Matrix.prime11
  ≡ Selector.frobeniusPairDefect Matrix.prime37 → ⊥
p11P37DefectsDiffer = Cutset.coarseFrobeniusPairDefectSeparates11And37

finiteOggCalibrationPreserved :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  Selector.finiteFrobeniusSelector prime ≡ Matrix.externalOggLabel prime
finiteOggCalibrationPreserved = Cutset.finiteUnder72SelectorMatchesExternalOgg

finiteCalibrationNotPromotedToIndependentGlobalGeometry :
  Cutset.P11P37MarkedDeckSelectorCutsetBoundary.finiteScanIsIndependentGeometricAllPrimeProof
    Cutset.canonicalP11P37MarkedDeckSelectorCutsetBoundary
  ≡ false
finiteCalibrationNotPromotedToIndependentGlobalGeometry = refl
